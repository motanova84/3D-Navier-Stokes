from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime


@dataclass(frozen=True)
class Observation:
    timestamp: datetime
    latitude: float
    longitude: float
    variable: str
    value: float
    source: str = "synthetic"
    uncertainty: float = 1.0
    quality_flag: str = "raw"
