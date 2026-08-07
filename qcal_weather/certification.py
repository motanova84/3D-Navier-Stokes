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
            name="Phase 1 — Benchmark & Mesh",
            milestones=[
                "Benchmark 2D/3D small cases from the repository",
                "Build fixed 3 km Balearic mesh",
                "Profile solver performance on 16-24 CPU cores and 24 GB VRAM",
            ],
        ),
        DeploymentPhase(
            name="Phase 2 — Frontier Ingestion & QC",
            milestones=[
                "Ingest GFS, ECMWF, SOCIB, AEMET, Puertos and Copernicus frontiers",
                "Run deterministic quality-control filters on incoming fields",
                "Persist source caches in Zarr/JSON operational stores",
            ],
        ),
        DeploymentPhase(
            name="Phase 3 — EnKF & QCAL Assimilation",
            milestones=[
                "Run 32-member ensemble Kalman filter analysis",
                "Apply Ψ variational coupling at f₀ = 141.7001 Hz",
                "Store posterior analysis state for production cycling",
            ],
        ),
        DeploymentPhase(
            name="Phase 4 — Nowcast & Temporal Prediction",
            milestones=[
                "Generate 0-6h nowcasts from the assimilated state",
                "Extend the horizon to 72h with the temporal predictor",
                "Persist forecast fields in compressed Zarr-compatible workflow",
            ],
        ),
        DeploymentPhase(
            name="Phase 5 — Verification & Production Seal",
            milestones=[
                "Compare baseline, QCAL and observed fields with operational metrics",
                "Emit the production certification package and deployment map",
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
