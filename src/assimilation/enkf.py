#!/usr/bin/env python3
"""
Xarray-based Ensemble Kalman Filter for QCAL-Balearic Phase 3.
"""

from __future__ import annotations

from dataclasses import dataclass
import logging
from pathlib import Path
from typing import Dict, List

import numpy as np
import xarray as xr


LOGGER = logging.getLogger("qcal-enkf")
QCAL_SKIP_VARS = {"psi", "coherence", "entropy", "freq_dev"}


@dataclass(frozen=True)
class EnKFConfig:
    ensemble_size: int = 32
    inflation_factor: float = 1.05
    localization_radius_km: float = 100.0
    qcal_coupling: bool = True
    qcal_alpha: float = 0.05
    qcal_lambda: float = 0.01
    seed: int = 1417001


class EnsembleKalmanFilter:
    def __init__(self, config: EnKFConfig | None = None):
        self.config = config or EnKFConfig()
        self.ensemble: List[xr.Dataset] | None = None
        self.observations: Dict[str, xr.DataArray] | None = None
        self.prior_mean: xr.Dataset | None = None
        self.posterior_mean: xr.Dataset | None = None
        self.analysis_time = None
        self._rng = np.random.default_rng(self.config.seed)

    def initialize_ensemble(self, state: xr.Dataset, noise_std: float = 0.1) -> List[xr.Dataset]:
        ensemble = []
        for _ in range(self.config.ensemble_size):
            perturbed = state.copy(deep=True)
            for var_name, variable in state.data_vars.items():
                if var_name in QCAL_SKIP_VARS:
                    continue
                noise = self._rng.normal(0.0, noise_std, size=variable.shape)
                perturbed[var_name] = variable + xr.DataArray(noise, dims=variable.dims, coords=variable.coords)
            if self.config.qcal_coupling:
                perturbed = self._update_qcal_field(perturbed)
            ensemble.append(perturbed)

        self.ensemble = ensemble
        self.prior_mean = self._compute_mean(ensemble)
        return ensemble

    def assimilate_observations(
        self,
        observations: Dict[str, xr.DataArray],
        observation_error: Dict[str, float],
    ) -> xr.Dataset:
        if self.ensemble is None:
            raise ValueError("Ensemble not initialized")

        self.observations = observations
        anomalies = self._compute_anomalies()

        for obs_name, obs_data in observations.items():
            if obs_name == "time" or obs_name not in observation_error:
                continue
            projected = self._project_ensemble(obs_name)
            kalman_gain = self._compute_kalman_gain(projected, observation_error[obs_name], anomalies)

            for index, member in enumerate(self.ensemble):
                innovation = obs_data.values - projected[index]
                self.ensemble[index] = self._update_member(member, kalman_gain, innovation)

        self.posterior_mean = self._compute_mean(self.ensemble)
        self.analysis_time = observations.get("time")
        if self.config.qcal_coupling:
            self.posterior_mean = self._update_qcal_field(self.posterior_mean)
        return self.posterior_mean

    def save_posterior_to_zarr(self, path: str) -> Path:
        if self.posterior_mean is None:
            raise ValueError("Posterior mean not available")
        output = Path(path)
        if output.exists():
            import shutil

            shutil.rmtree(output)
        self.posterior_mean.to_zarr(output, mode="w", consolidated=False)
        return output

    def _compute_mean(self, ensemble: List[xr.Dataset]) -> xr.Dataset:
        template = ensemble[0].copy(deep=True)
        for var_name in template.data_vars:
            stacked = np.stack([member[var_name].values for member in ensemble], axis=0)
            template[var_name].values = np.mean(stacked, axis=0)
        return template

    def _compute_anomalies(self) -> Dict[str, np.ndarray]:
        assert self.ensemble is not None
        anomalies: Dict[str, np.ndarray] = {}
        for var_name in self.ensemble[0].data_vars:
            stacked = np.stack([member[var_name].values for member in self.ensemble], axis=0)
            anomalies[var_name] = stacked - np.mean(stacked, axis=0, keepdims=True)
        return anomalies

    def _project_ensemble(self, obs_name: str) -> List[np.ndarray]:
        assert self.ensemble is not None
        return [member[obs_name].values for member in self.ensemble if obs_name in member.data_vars]

    def _compute_kalman_gain(
        self,
        projected_ensemble: List[np.ndarray],
        observation_error: float,
        anomalies: Dict[str, np.ndarray],
    ) -> Dict[str, np.ndarray]:
        observation_stack = np.stack(projected_ensemble, axis=0)
        observation_anomalies = observation_stack - np.mean(observation_stack, axis=0, keepdims=True)
        observation_variance = np.mean(observation_anomalies**2, axis=0) + observation_error**2
        localization = self._localization_weights(observation_variance.shape)

        gains: Dict[str, np.ndarray] = {}
        for var_name, var_anomalies in anomalies.items():
            cross_covariance = np.mean(var_anomalies * observation_anomalies, axis=0)
            gains[var_name] = self.config.inflation_factor * localization * cross_covariance / observation_variance
        return gains

    def _update_member(self, member: xr.Dataset, kalman_gain: Dict[str, np.ndarray], innovation: np.ndarray) -> xr.Dataset:
        updated = member.copy(deep=True)
        for var_name in updated.data_vars:
            if var_name in kalman_gain:
                updated[var_name].values = updated[var_name].values + kalman_gain[var_name] * innovation
        return updated

    def _localization_weights(self, shape: tuple[int, ...]) -> np.ndarray:
        if len(shape) < 2:
            return np.ones(shape, dtype=float)
        y, x = np.indices(shape[-2:])
        center_y = (shape[-2] - 1) / 2.0
        center_x = (shape[-1] - 1) / 2.0
        radius = max(self.config.localization_radius_km, 1.0)
        distances = np.sqrt((x - center_x) ** 2 + (y - center_y) ** 2)
        weights = np.exp(-(distances**2) / (2.0 * radius**2))
        if len(shape) == 3:
            return np.broadcast_to(weights, shape)
        return weights

    def _update_qcal_field(self, state: xr.Dataset) -> xr.Dataset:
        if "psi" not in state.data_vars:
            return state

        updated = state.copy(deep=True)
        psi = updated["psi"].values
        forcing = np.zeros_like(psi)

        if "u" in updated.data_vars and "v" in updated.data_vars:
            du_dy = np.gradient(updated["u"].values, axis=-2)
            dv_dx = np.gradient(updated["v"].values, axis=-1)
            vorticity_sq = (dv_dx - du_dy) ** 2
            forcing = forcing + vorticity_sq
        if "T" in updated.data_vars:
            grad_t = np.gradient(updated["T"].values, axis=-1) ** 2 + np.gradient(updated["T"].values, axis=-2) ** 2
            forcing = forcing + grad_t
        if "p" in updated.data_vars:
            grad_p = np.gradient(updated["p"].values, axis=-1) ** 2 + np.gradient(updated["p"].values, axis=-2) ** 2
            forcing = forcing + 1e-6 * grad_p

        forcing = forcing / (1.0 + forcing)
        psi_new = np.clip(
            psi + self.config.qcal_alpha * forcing - self.config.qcal_lambda * (psi - 0.999999),
            0.0,
            1.0,
        )
        updated["psi"].values = psi_new
        if "coherence" in updated.data_vars:
            updated["coherence"].values = psi_new
        if "entropy" in updated.data_vars:
            updated["entropy"].values = -psi_new * np.log(psi_new + 1e-12)
        if "freq_dev" in updated.data_vars:
            updated["freq_dev"].values = (psi_new - 0.999999) * 141.7001
        return updated
