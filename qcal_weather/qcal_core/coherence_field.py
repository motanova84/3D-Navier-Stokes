from __future__ import annotations

from dataclasses import dataclass

import numpy as np

from .spectral_diagnostics import compute_spectral_diagnostics, gradient_x, gradient_y, laplacian


@dataclass(frozen=True)
class CoherenceParameters:
    diffusion: float = 0.02
    relaxation_rate: float = 0.08
    alpha: float = 0.10
    beta_vorticity: float = 0.45
    beta_temperature: float = 0.20
    beta_pressure: float = 0.20
    beta_divergence: float = 0.15
    psi_ref: float = 1.0
    min_psi: float = 0.0
    max_psi: float = 1.0


class CoherenceField:
    def __init__(self, psi: np.ndarray, parameters: CoherenceParameters | None = None):
        self.psi = np.asarray(psi, dtype=float)
        self.parameters = parameters or CoherenceParameters()

    @classmethod
    def from_shape(cls, shape, value: float = 1.0, parameters: CoherenceParameters | None = None) -> "CoherenceField":
        return cls(np.full(shape, value, dtype=float), parameters=parameters)

    def forcing(self, state, spacing_km: float) -> np.ndarray:
        diagnostics = compute_spectral_diagnostics(state, spacing_km)
        return self.parameters.alpha * (
            self.parameters.beta_vorticity * diagnostics["vorticity_norm_sq"]
            + self.parameters.beta_temperature * diagnostics["temperature_gradient_norm_sq"]
            + self.parameters.beta_pressure * diagnostics["pressure_gradient_norm_sq"]
            + self.parameters.beta_divergence * diagnostics["divergence_abs_mean"]
        ) * np.ones_like(self.psi)

    def step(self, state, dt_hours: float, spacing_km: float) -> np.ndarray:
        """
        Advance the Ψ field in place and return a detached copy of the updated raw array.
        """
        adv_x = state.wind_u * gradient_x(self.psi, spacing_km)
        adv_y = state.wind_v * gradient_y(self.psi, spacing_km)
        advection = adv_x + adv_y
        diffusion = self.parameters.diffusion * laplacian(self.psi, spacing_km)
        relaxation = -self.parameters.relaxation_rate * (self.psi - self.parameters.psi_ref)
        forcing = self.forcing(state, spacing_km)

        updated = self.psi + dt_hours * (-advection + diffusion + relaxation + forcing)
        self.psi = np.clip(updated, self.parameters.min_psi, self.parameters.max_psi)
        return self.psi.copy()
