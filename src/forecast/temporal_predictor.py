#!/usr/bin/env python3
"""
Temporal predictor for Phase 4 nowcasting and short-range forecasting.
"""

from __future__ import annotations

from dataclasses import dataclass
import logging
from pathlib import Path
from typing import Dict, List

import numpy as np
import xarray as xr


LOGGER = logging.getLogger("qcal-forecast")
F0_HZ = 141.7001


@dataclass(frozen=True)
class PredictorConfig:
    forecast_hours: tuple[int, ...] = (6, 12, 24, 48, 72)
    dt_seconds: float = 600.0
    qcal_alpha: float = 0.05
    qcal_lambda: float = 0.01
    ensemble_size: int = 8
    output_dir: str = "data/forecasts"
    viscosity: float = 0.01
    thermal_relaxation: float = 0.001


class TemporalPredictor:
    def __init__(self, config: PredictorConfig | None = None):
        self.config = config or PredictorConfig()
        self.output_dir = Path(self.config.output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        self.state: xr.Dataset | None = None
        self.forecasts: Dict[int, xr.Dataset] = {}

    def initialize_state(self, analysis_state: xr.Dataset) -> None:
        self.state = analysis_state.copy(deep=True)

    def integrate_barotropic(self, state: xr.Dataset, steps: int) -> xr.Dataset:
        current = state.copy(deep=True)
        current = self._compute_vorticity(current)
        dt = self.config.dt_seconds
        for _ in range(steps):
            current["vorticity"].values = current["vorticity"].values + dt * (
                self.config.viscosity * self._laplacian(current["vorticity"].values)
            )
            current = self._apply_qcal_coupling(current)
        return current

    def integrate_forecast(self, steps: int, output_frequency: int = 6) -> Dict[int, xr.Dataset]:
        if self.state is None:
            raise ValueError("Predictor state not initialized")

        current = self.state.copy(deep=True)
        forecasts: Dict[int, xr.Dataset] = {}
        for step in range(1, steps + 1):
            current = self._navier_stokes_step(current, self.config.dt_seconds)
            current = self._apply_qcal_coupling(current)
            if step % output_frequency == 0:
                hour = int(round(step * self.config.dt_seconds / 3600.0))
                if hour in self.config.forecast_hours:
                    forecasts[hour] = current.copy(deep=True)
        self.forecasts = forecasts
        return forecasts

    def forecast_ensemble(self, perturbations: List[Dict[str, float]]) -> Dict[int, List[xr.Dataset]]:
        if self.state is None:
            raise ValueError("Predictor state not initialized")

        ensemble_forecasts: Dict[int, List[xr.Dataset]] = {}
        max_hour = max(self.config.forecast_hours)
        steps = int(max_hour * 3600 / self.config.dt_seconds)
        output_frequency = max(1, int(3600 / self.config.dt_seconds))
        rng = np.random.default_rng(1417001)

        for perturbation in perturbations:
            perturbed = self.state.copy(deep=True)
            for var_name, sigma in perturbation.items():
                if var_name in perturbed.data_vars:
                    noise = rng.normal(0.0, sigma, size=perturbed[var_name].shape)
                    perturbed[var_name].values = perturbed[var_name].values + noise
            self.initialize_state(perturbed)
            forecast = self.integrate_forecast(steps=steps, output_frequency=output_frequency)
            for hour, dataset in forecast.items():
                ensemble_forecasts.setdefault(hour, []).append(dataset)

        return ensemble_forecasts

    def save_forecast(self, forecast: Dict[int, xr.Dataset], name: str = "latest") -> None:
        for hour, dataset in forecast.items():
            path = self.output_dir / f"{name}_f{hour:03d}.zarr"
            if path.exists():
                import shutil

                shutil.rmtree(path)
            dataset.to_zarr(path, mode="w", consolidated=False)

    def load_forecast(self, name: str = "latest", hour: int = 24) -> xr.Dataset | None:
        path = self.output_dir / f"{name}_f{hour:03d}.zarr"
        return xr.open_zarr(path, consolidated=False) if path.exists() else None

    def _navier_stokes_step(self, state: xr.Dataset, dt: float) -> xr.Dataset:
        updated = state.copy(deep=True)
        dt_scale = dt / 3600.0
        if "u" in updated and "p" in updated:
            dp_dx = np.gradient(updated["p"].values, axis=-1)
            updated["u"].values = updated["u"].values + dt_scale * (
                -0.05 * updated["u"].values - 1e-4 * dp_dx + self.config.viscosity * self._laplacian(updated["u"].values)
            )
        if "v" in updated and "p" in updated:
            dp_dy = np.gradient(updated["p"].values, axis=-2)
            updated["v"].values = updated["v"].values + dt_scale * (
                -0.05 * updated["v"].values - 1e-4 * dp_dy + self.config.viscosity * self._laplacian(updated["v"].values)
            )
        if "T" in updated:
            updated["T"].values = updated["T"].values + dt_scale * (
                -self.config.thermal_relaxation * (updated["T"].values - np.mean(updated["T"].values))
            )
        if "p" in updated and "u" in updated and "v" in updated:
            divergence = np.gradient(updated["u"].values, axis=-1) + np.gradient(updated["v"].values, axis=-2)
            updated["p"].values = updated["p"].values - dt_scale * 5.0 * divergence
        return self._compute_vorticity(updated)

    def _apply_qcal_coupling(self, state: xr.Dataset) -> xr.Dataset:
        updated = state.copy(deep=True)
        if "psi" not in updated.data_vars:
            return updated

        forcing = np.zeros_like(updated["psi"].values)
        if "vorticity" in updated.data_vars:
            forcing = forcing + np.abs(updated["vorticity"].values)
        if "T" in updated.data_vars:
            forcing = forcing + 0.01 * np.abs(np.gradient(updated["T"].values, axis=-1))
        forcing = forcing / (1.0 + forcing)

        psi_new = np.clip(
            updated["psi"].values
            + self.config.qcal_alpha * forcing
            - self.config.qcal_lambda * (updated["psi"].values - 0.999999),
            0.0,
            1.0,
        )
        updated["psi"].values = psi_new
        if "coherence" in updated:
            updated["coherence"].values = psi_new
        if "entropy" in updated:
            updated["entropy"].values = -psi_new * np.log(psi_new + 1e-12)
        if "freq_dev" in updated:
            updated["freq_dev"].values = (psi_new - 0.999999) * F0_HZ
        return updated

    def _compute_vorticity(self, state: xr.Dataset) -> xr.Dataset:
        updated = state.copy(deep=True)
        if "u" in updated.data_vars and "v" in updated.data_vars:
            updated["vorticity"] = xr.DataArray(
                np.gradient(updated["v"].values, axis=-1) - np.gradient(updated["u"].values, axis=-2),
                dims=updated["u"].dims,
                coords=updated["u"].coords,
            )
        return updated

    def _laplacian(self, field: np.ndarray) -> np.ndarray:
        padded = np.pad(field, pad_width=1, mode="edge")
        return (
            padded[2:, 1:-1]
            + padded[:-2, 1:-1]
            + padded[1:-1, 2:]
            + padded[1:-1, :-2]
            - 4.0 * padded[1:-1, 1:-1]
        )
