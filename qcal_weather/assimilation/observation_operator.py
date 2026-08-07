from __future__ import annotations

from typing import Iterable, Tuple

import numpy as np


class ObservationOperator:
    def __init__(self, config):
        self.config = config
        self.lat_min, self.lat_max, self.lon_min, self.lon_max = config.extent()

    def location_to_index(self, latitude: float, longitude: float) -> Tuple[int, int]:
        lat_ratio = (latitude - self.lat_min) / max(self.lat_max - self.lat_min, 1e-12)
        lon_ratio = (longitude - self.lon_min) / max(self.lon_max - self.lon_min, 1e-12)
        iy = int(np.clip(round(lat_ratio * (self.config.ny - 1)), 0, self.config.ny - 1))
        ix = int(np.clip(round(lon_ratio * (self.config.nx - 1)), 0, self.config.nx - 1))
        return iy, ix

    def read_variable(self, state, variable: str, latitude: float, longitude: float) -> float:
        iy, ix = self.location_to_index(latitude, longitude)
        field = getattr(state, variable)
        return float(field[iy, ix])

    def extract(self, state, observations: Iterable) -> np.ndarray:
        return np.array(
            [self.read_variable(state, obs.variable, obs.latitude, obs.longitude) for obs in observations],
            dtype=float,
        )

    def add_local_increment(self, state, variable: str, latitude: float, longitude: float, increment: float, radius: int = 1):
        iy, ix = self.location_to_index(latitude, longitude)
        field = getattr(state, variable)
        for dy in range(-radius, radius + 1):
            for dx in range(-radius, radius + 1):
                y = int(np.clip(iy + dy, 0, field.shape[0] - 1))
                x = int(np.clip(ix + dx, 0, field.shape[1] - 1))
                distance = abs(dx) + abs(dy)
                weight = 1.0 / (1.0 + distance)
                field[y, x] += weight * increment
        return state
