from __future__ import annotations

from dataclasses import dataclass

import numpy as np

from qcal_weather.qcal_core.coherence_field import CoherenceField
from qcal_weather.qcal_core.regularization import apply_qcal_regularization


@dataclass(frozen=True)
class QCALCouplingParameters:
    coupling_strength: float = 0.12
    wind_damping: float = 0.18
    thermal_relaxation: float = 0.06
    pressure_relaxation: float = 0.03


class QCALAtmosphereCoupler:
    def __init__(self, coherence_field: CoherenceField, parameters: QCALCouplingParameters | None = None):
        self.coherence_field = coherence_field
        self.parameters = parameters or QCALCouplingParameters()

    def apply(self, state, diagnostics, dt_hours: float, spacing_km: float):
        psi = self.coherence_field.step(state, dt_hours, spacing_km)
        correction = 1.0 + self.parameters.coupling_strength * psi
        state.wind_u = apply_qcal_regularization(state.wind_u, psi, self.parameters.wind_damping) / correction
        state.wind_v = apply_qcal_regularization(state.wind_v, psi, self.parameters.wind_damping) / correction
        state.temperature = state.temperature - dt_hours * self.parameters.thermal_relaxation * diagnostics["vorticity_rms"] * (1.0 - psi)
        state.pressure = state.pressure - dt_hours * self.parameters.pressure_relaxation * diagnostics["divergence_abs_mean"] * (1.0 - psi)
        state.humidity = np.clip(state.humidity + 0.01 * psi, 0.0, 1.0)
        return state
