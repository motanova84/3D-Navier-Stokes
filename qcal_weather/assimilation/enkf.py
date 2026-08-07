from __future__ import annotations

from typing import Iterable, List

import numpy as np

from qcal_weather.data.quality_control import PHYSICAL_LIMITS


def build_ensemble(state, members: int = 8, perturbation_scale: float = 0.05) -> List:
    ensemble = []
    rng = np.random.default_rng(1417001)
    for _ in range(members):
        member = state.copy()
        for variable in ("wind_u", "wind_v", "temperature", "pressure", "humidity", "sea_level_anomaly"):
            field = getattr(member, variable)
            sigma = np.std(field) if np.std(field) > 0 else 1.0
            perturbation = rng.normal(loc=0.0, scale=perturbation_scale * sigma, size=field.shape)
            updated = field + perturbation
            if variable in PHYSICAL_LIMITS:
                lower, upper = PHYSICAL_LIMITS[variable]
                updated = np.clip(updated, lower, upper)
            setattr(member, variable, updated)
        ensemble.append(member)
    return ensemble


class EnsembleKalmanFilter:
    def __init__(self, inflation: float = 1.01, observation_error_floor: float = 0.25):
        self.inflation = inflation
        self.observation_error_floor = observation_error_floor

    def update(self, ensemble: List, observations: Iterable, operator) -> List:
        updated = [member.copy() for member in ensemble]
        observations = list(observations)
        if not observations:
            return updated

        for obs in observations:
            model_values = np.array(
                [operator.read_variable(member, obs.variable, obs.latitude, obs.longitude) for member in updated],
                dtype=float,
            )
            mean_value = float(np.mean(model_values))
            inflated_values = mean_value + self.inflation * (model_values - mean_value)
            variance = float(np.var(inflated_values))
            observation_error = max(self.observation_error_floor, obs.uncertainty**2)
            gain = variance / (variance + observation_error) if variance > 0 else 0.0

            for index, member in enumerate(updated):
                innovation = obs.value - model_values[index]
                operator.add_local_increment(member, obs.variable, obs.latitude, obs.longitude, gain * innovation)
                for variable, bounds in PHYSICAL_LIMITS.items():
                    lower, upper = bounds
                    setattr(member, variable, np.clip(getattr(member, variable), lower, upper))

            if obs.variable == "pressure":
                mean_adjustment = obs.value - mean_value
                for member in updated:
                    member.sea_level_anomaly = np.clip(member.sea_level_anomaly + 0.001 * mean_adjustment, -5.0, 5.0)
        return updated
