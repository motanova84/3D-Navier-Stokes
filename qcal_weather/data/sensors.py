from __future__ import annotations

from datetime import UTC, datetime
from typing import Iterable, List

import numpy as np

from .schemas import Observation


def generate_synthetic_observations(config, when: datetime | None = None, variables: Iterable[str] | None = None) -> List[Observation]:
    when = when or datetime.now(UTC)
    variables = list(variables or ("wind_u", "wind_v", "temperature", "pressure", "humidity"))
    rng = np.random.default_rng(17)
    lat_min, lat_max, lon_min, lon_max = config.extent()
    points = [
        (config.center_lat, config.center_lon),
        (lat_min + 0.25 * (lat_max - lat_min), lon_min + 0.35 * (lon_max - lon_min)),
        (lat_min + 0.65 * (lat_max - lat_min), lon_min + 0.70 * (lon_max - lon_min)),
    ]
    baselines = {
        "wind_u": 8.0,
        "wind_v": 1.5,
        "temperature": 295.0,
        "pressure": 1010.0,
        "humidity": 0.7,
    }
    spreads = {"wind_u": 1.2, "wind_v": 1.0, "temperature": 1.8, "pressure": 2.5, "humidity": 0.08}
    observations = []
    for latitude, longitude in points:
        for variable in variables:
            observations.append(
                Observation(
                    timestamp=when,
                    latitude=latitude,
                    longitude=longitude,
                    variable=variable,
                    value=float(baselines[variable] + rng.normal(0.0, spreads[variable])),
                    uncertainty=float(max(0.1, spreads[variable] * 0.5)),
                )
            )
    return observations
