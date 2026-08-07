from __future__ import annotations

from dataclasses import asdict, dataclass
from math import ceil
from math import cos, radians
from typing import Dict, Tuple


@dataclass(frozen=True)
class RegionalDomainConfig:
    """
    Configuration for the Balearic regional nowcast MVP.
    """

    name: str = "QCAL-Balearic Nowcast"
    center_lat: float = 39.6953
    center_lon: float = 2.9980
    domain_size_km: Tuple[float, float] = (500.0, 500.0)
    resolution_km: float = 3.0
    coastal_refinement_km: float = 1.0
    vertical_levels: int = 60
    forecast_hours_min: int = 6
    forecast_hours_max: int = 72
    output_interval_minutes: int = 10
    total_fields: int = 16
    float_bytes: int = 4

    @property
    def nx(self) -> int:
        return ceil(self.domain_size_km[0] / self.resolution_km)

    @property
    def ny(self) -> int:
        return ceil(self.domain_size_km[1] / self.resolution_km)

    @property
    def horizontal_cells(self) -> int:
        return self.nx * self.ny

    @property
    def total_cells(self) -> int:
        return self.horizontal_cells * self.vertical_levels

    def estimated_state_size_mb(self, total_fields: int | None = None) -> float:
        fields = total_fields or self.total_fields
        bytes_used = self.total_cells * fields * self.float_bytes
        return bytes_used / (1024 * 1024)

    def estimated_operational_memory_gb(self, ensemble_members: int = 8) -> float:
        state_gb = self.estimated_state_size_mb() / 1024
        buffer_gb = state_gb * 3.0
        diagnostic_gb = state_gb * 1.5
        checkpoints_gb = max(2.0, state_gb * 2.0)
        ensemble_gb = state_gb * max(1, ensemble_members)
        return round(state_gb + buffer_gb + diagnostic_gb + checkpoints_gb + ensemble_gb, 2)

    def mesh_memory_report(self, resolution_km: float | None = None) -> Dict[str, float]:
        resolution = resolution_km or self.resolution_km
        nx = ceil(self.domain_size_km[0] / resolution)
        ny = ceil(self.domain_size_km[1] / resolution)
        horizontal_cells = nx * ny
        total_cells = horizontal_cells * self.vertical_levels
        state_mb = (total_cells * self.total_fields * self.float_bytes) / (1024 * 1024)
        state_gb = state_mb / 1024
        if resolution <= 1.0:
            buffers_gb = state_gb * 4.0
            operators_gb = state_gb * 2.2
            halo_gb = max(0.8, state_gb * 0.8)
            reserve_gb = 2.3
            peak_vram_gb = state_gb + buffers_gb + operators_gb + halo_gb + reserve_gb
        else:
            buffers_gb = state_gb * 3.0
            operators_gb = state_gb * 1.2
            halo_gb = max(0.2, state_gb * 0.6)
            reserve_gb = 0.5
            peak_vram_gb = state_gb + buffers_gb + operators_gb + halo_gb + reserve_gb
        return {
            "resolution_km": float(resolution),
            "nx": nx,
            "ny": ny,
            "horizontal_cells": horizontal_cells,
            "total_cells": total_cells,
            "state_memory_mb": round(state_mb, 2),
            "peak_vram_gb": round(peak_vram_gb, 2),
        }

    def recommended_hardware(self) -> Dict[str, str]:
        return {
            "cpu": "16-24 cores",
            "ram": "128 GB",
            "gpu": "24 GB VRAM",
            "disk": "2 TB NVMe",
            "runtime": "Docker + optional CUDA/JAX acceleration",
        }

    def extent(self) -> Tuple[float, float, float, float]:
        half_lat = self.domain_size_km[1] / 2.0 / 111.0
        lon_scale = max(0.1, 111.0 * abs(cos(radians(self.center_lat))))
        half_lon = self.domain_size_km[0] / 2.0 / lon_scale
        return (
            self.center_lat - half_lat,
            self.center_lat + half_lat,
            self.center_lon - half_lon,
            self.center_lon + half_lon,
        )

    def as_dict(self) -> Dict[str, object]:
        return {
            **asdict(self),
            "nx": self.nx,
            "ny": self.ny,
            "total_cells": self.total_cells,
            "estimated_state_size_mb": round(self.estimated_state_size_mb(), 2),
            "estimated_operational_memory_gb": self.estimated_operational_memory_gb(),
        }


DEFAULT_BALEARIC_CONFIG = RegionalDomainConfig()
