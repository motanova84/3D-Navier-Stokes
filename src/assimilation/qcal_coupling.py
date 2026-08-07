#!/usr/bin/env python3
"""
Variational QCAL coupling for Phase 3 analysis updates.
"""

from __future__ import annotations

import logging
from typing import Dict, Tuple

import numpy as np
import xarray as xr


LOGGER = logging.getLogger("qcal-variational-coupling")


class QCALVariationalCoupling:
    def __init__(
        self,
        f0: float = 141.7001,
        psi_ref: float = 0.999999,
        alpha: float = 0.05,
        lambda_coeff: float = 0.01,
        d_psi: float = 0.1,
    ):
        self.f0 = f0
        self.psi_ref = psi_ref
        self.alpha = alpha
        self.lambda_coeff = lambda_coeff
        self.d_psi = d_psi

    def compute_cost_function(
        self,
        state: xr.Dataset,
        observations: Dict[str, xr.DataArray],
        background: xr.Dataset,
    ) -> float:
        j_obs = 0.0
        for obs_name, obs_data in observations.items():
            if obs_name == "time" or obs_name not in state.data_vars:
                continue
            innovation = state[obs_name].values - obs_data.values
            j_obs += float(np.sum(innovation**2))

        j_bg = 0.0
        for var_name in background.data_vars:
            if var_name in state.data_vars:
                diff = state[var_name].values - background[var_name].values
                j_bg += float(np.sum(diff**2))

        j_qcal = 0.0
        if "psi" in state.data_vars:
            j_qcal = float(self.lambda_coeff * np.sum((state["psi"].values - self.psi_ref) ** 2))
        return j_obs + j_bg + j_qcal

    def compute_gradient(
        self,
        state: xr.Dataset,
        observations: Dict[str, xr.DataArray],
        background: xr.Dataset,
    ) -> Dict[str, np.ndarray]:
        gradient: Dict[str, np.ndarray] = {}
        for var_name in state.data_vars:
            if var_name not in background.data_vars:
                continue
            grad_obs = np.zeros_like(state[var_name].values)
            if var_name in observations:
                grad_obs = 2.0 * (state[var_name].values - observations[var_name].values)
            grad_bg = 2.0 * (state[var_name].values - background[var_name].values)
            grad_qcal = np.zeros_like(state[var_name].values)
            if var_name == "psi":
                grad_qcal = 2.0 * self.lambda_coeff * (state[var_name].values - self.psi_ref)
            gradient[var_name] = grad_obs + grad_bg + grad_qcal
        return gradient

    def variational_update(
        self,
        state: xr.Dataset,
        observations: Dict[str, xr.DataArray],
        background: xr.Dataset,
        n_iter: int = 10,
        learning_rate: float = 0.01,
    ) -> xr.Dataset:
        current = state.copy(deep=True)
        for _ in range(n_iter):
            gradient = self.compute_gradient(current, observations, background)
            for var_name in current.data_vars:
                if var_name in gradient:
                    current[var_name].values = current[var_name].values - learning_rate * gradient[var_name]
            current = self._apply_qcal_constraints(current)
        return current

    def qcal_analysis_cycle(
        self,
        background: xr.Dataset,
        observations: Dict[str, xr.DataArray],
        ensemble_mean: xr.Dataset,
    ) -> Tuple[xr.Dataset, Dict[str, float]]:
        analysis = self.variational_update(ensemble_mean, observations, background)
        metrics = {
            "cost_final": self.compute_cost_function(analysis, observations, background),
            "psi_mean": float(analysis["psi"].mean().values),
            "psi_std": float(analysis["psi"].std().values),
            "coherence_min": float(analysis["psi"].min().values),
            "coherence_max": float(analysis["psi"].max().values),
            "entropy_mean": float(analysis["entropy"].mean().values),
            "freq_dev_mean": float(analysis["freq_dev"].mean().values),
        }
        return analysis, metrics

    def _apply_qcal_constraints(self, state: xr.Dataset) -> xr.Dataset:
        updated = state.copy(deep=True)
        if "psi" not in updated.data_vars:
            return updated

        psi = np.clip(updated["psi"].values, 0.0, 1.0)
        updated["psi"].values = psi
        if "coherence" in updated.data_vars:
            updated["coherence"].values = psi
        if "entropy" in updated.data_vars:
            updated["entropy"].values = -psi * np.log(psi + 1e-12)
        if "freq_dev" in updated.data_vars:
            updated["freq_dev"].values = (psi - self.psi_ref) * self.f0
        return updated
