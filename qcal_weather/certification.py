from __future__ import annotations

from dataclasses import asdict, dataclass
from typing import Dict, List

from .config import RegionalDomainConfig


@dataclass(frozen=True)
class DeploymentPhase:
    name: str
    milestones: List[str]


@dataclass(frozen=True)
class TechnicalCertification:
    status: str
    hardware_ok: bool
    mesh_3km: Dict[str, float]
    mesh_1km: Dict[str, float]
    gpu_margin_percent: float
    recommended_hardware: Dict[str, str]
    phases: List[DeploymentPhase]

    def as_dict(self) -> Dict[str, object]:
        data = asdict(self)
        data["phases"] = [asdict(phase) for phase in self.phases]
        return data


def build_technical_certification(
    config: RegionalDomainConfig,
    gpu_vram_gb: float = 24.0,
    ram_gb: float = 128.0,
    disk_tb: float = 2.0,
) -> TechnicalCertification:
    mesh_3km = config.mesh_memory_report(3.0)
    mesh_1km = config.mesh_memory_report(1.0)
    hardware_ok = gpu_vram_gb >= mesh_1km["peak_vram_gb"] and ram_gb >= 128.0 and disk_tb >= 2.0
    gpu_margin_percent = round(((gpu_vram_gb - mesh_1km["peak_vram_gb"]) / mesh_1km["peak_vram_gb"]) * 100.0, 1)
    phases = [
        DeploymentPhase(
            name="Benchmark & Core",
            milestones=[
                "Benchmark 2D/3D small cases from the repository",
                "Build fixed 3 km Balearic mesh",
                "Profile solver performance on 16-24 CPU cores and 24 GB VRAM",
            ],
        ),
        DeploymentPhase(
            name="Divergence & QCAL",
            milestones=[
                "Run 6h deterministic atmospheric solver",
                "Inject optional Ψ spectral module at f₀ = 141.7001 Hz",
                "Persist forecast fields in compressed Zarr-compatible workflow",
            ],
        ),
        DeploymentPhase(
            name="Refinement & Ensemble",
            milestones=[
                "Add 1 km coastal nesting",
                "Extend forecast horizon to 72h",
                "Expose baseline vs QCAL vs observed error dashboard",
            ],
        ),
    ]
    return TechnicalCertification(
        status="certified" if hardware_ok else "insufficient-hardware",
        hardware_ok=hardware_ok,
        mesh_3km=mesh_3km,
        mesh_1km=mesh_1km,
        gpu_margin_percent=gpu_margin_percent,
        recommended_hardware=config.recommended_hardware(),
        phases=phases,
    )
