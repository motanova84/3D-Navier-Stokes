from __future__ import annotations

from typing import Dict

import numpy as np

from .metrics import mae, minimum_pressure_error, rmse


def _wind_speed(state) -> np.ndarray:
    return np.sqrt(state.wind_u**2 + state.wind_v**2)


def evaluate_nowcast(baseline_state, qcal_state, observed_state) -> Dict[str, Dict[str, float]]:
    return {
        "baseline": {
            "wind_rmse": rmse(_wind_speed(baseline_state), _wind_speed(observed_state)),
            "temperature_mae": mae(baseline_state.temperature, observed_state.temperature),
            "pressure_min_error": minimum_pressure_error(baseline_state.pressure, observed_state.pressure),
        },
        "qcal": {
            "wind_rmse": rmse(_wind_speed(qcal_state), _wind_speed(observed_state)),
            "temperature_mae": mae(qcal_state.temperature, observed_state.temperature),
            "pressure_min_error": minimum_pressure_error(qcal_state.pressure, observed_state.pressure),
        },
    }
