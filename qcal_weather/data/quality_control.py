from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, List

from .schemas import Observation


PHYSICAL_LIMITS = {
    "wind_u": (-120.0, 120.0),
    "wind_v": (-120.0, 120.0),
    "temperature": (180.0, 330.0),
    "pressure": (870.0, 1085.0),
    "humidity": (0.0, 1.0),
    "sea_level_anomaly": (-5.0, 5.0),
}


@dataclass(frozen=True)
class QualityControlResult:
    accepted: List[Observation]
    rejected: List[Observation]


def quality_control_filter(observations: Iterable[Observation]) -> QualityControlResult:
    accepted: List[Observation] = []
    rejected: List[Observation] = []

    for observation in observations:
        bounds = PHYSICAL_LIMITS.get(observation.variable)
        if bounds is None:
            rejected.append(observation)
            continue
        lower, upper = bounds
        if lower <= observation.value <= upper:
            accepted.append(observation)
        else:
            rejected.append(observation)
    return QualityControlResult(accepted=accepted, rejected=rejected)
