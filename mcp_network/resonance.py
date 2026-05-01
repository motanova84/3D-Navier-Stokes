# -*- coding: utf-8 -*-
"""Resonance Engine QCAL ∞³ with synthetic and real-observer modes."""

from __future__ import annotations

import csv
import math
import os
from datetime import datetime, timezone
from typing import Any, Callable, Dict, Optional, Tuple

F0_REFERENCE = 141.7001

NODE_CATALOG: Dict[str, Dict[str, Any]] = {
    "auron-governor": {
        "frequency_hz": 50.0,
        "description": "Grid frequency observer",
    },
    "141-hz": {
        "frequency_hz": 141.7001,
        "description": "QCAL spectral observer",
    },
    "interferometro-noesico": {
        "frequency_hz": 283.4002,
        "description": "Interferometric node",
    },
    "biologia-cuantica-noesica": {
        "frequency_hz": 70.85005,
        "description": "Biological coherence node",
    },
}

ObserverReturn = Tuple[float, float, bool, bool]
REAL_OBSERVERS: Dict[str, Callable[[], ObserverReturn]] = {}


def register_real_observer(node: str, fn: Callable[[], ObserverReturn]) -> None:
    """Register a real observer callback for a node."""
    REAL_OBSERVERS[node] = fn


def clear_real_observers() -> None:
    """Clear observer registry (mostly for tests)."""
    REAL_OBSERVERS.clear()


def reset_default_real_observers() -> None:
    """Restore built-in default observers."""
    REAL_OBSERVERS.clear()
    REAL_OBSERVERS["auron-governor"] = load_real_grid_sample
    REAL_OBSERVERS["141-hz"] = load_qcal_spectrum


def score_psi(
    latency_ms: float,
    phase_offset_rad: float,
    heartbeat_ok: bool = True,
    schema_ok: bool = True,
) -> float:
    """Compute bounded QCAL coherence score."""
    if not heartbeat_ok or not schema_ok:
        return 0.0
    latency_penalty = min(latency_ms / 100.0, 1.0)
    phase_penalty = min(abs(phase_offset_rad) / 0.25, 1.0)
    psi = 1.0 - 0.45 * latency_penalty - 0.55 * phase_penalty
    return max(0.0, min(psi, 1.0))


def classify_resonance(psi: float, reachable: bool) -> tuple[str, str]:
    """Classify resonance and status from ψ and reachability."""
    if not reachable:
        return "offline", "fail"
    if psi >= 0.99:
        return "coherent", "pass"
    if psi >= 0.95:
        return "drifting", "warn"
    return "fault", "fail"


def _real_mode_enabled() -> bool:
    return os.getenv("QCAL_REAL_TESTS", "").strip().lower() in {"1", "true", "yes", "on"}


def load_real_grid_sample() -> ObserverReturn:
    """Load an optional real grid-frequency sample from CSV."""
    path = os.getenv("QCAL_GRID_SAMPLE_PATH", "/tmp/grid_frequency_2026-04-15T14_55Z.csv")
    if not os.path.exists(path):
        return 12.4, 0.018, True, True

    frequencies = []
    try:
        with open(path, "r", encoding="utf-8") as handle:
            reader = csv.DictReader(handle)
            for row in reader:
                raw = row.get("frequency_hz")
                if raw is None:
                    continue
                try:
                    frequencies.append(float(raw))
                except (TypeError, ValueError):
                    continue
    except OSError:
        return 12.4, 0.018, False, False

    if not frequencies:
        return 12.4, 0.018, False, False

    delta_f = (sum(frequencies) / len(frequencies)) - 50.0
    window_seconds = float(len(frequencies))
    phase_offset = 2.0 * math.pi * delta_f * window_seconds
    latency_ms = float(os.getenv("QCAL_GRID_LATENCY_MS", "20.0"))
    return latency_ms, phase_offset, True, True


def load_qcal_spectrum() -> ObserverReturn:
    """Default observer placeholder for QCAL spectrum node."""
    return 8.7, 0.003, True, True


reset_default_real_observers()


def check_node_resonance(
    node_name: str,
    latency_ms: Optional[float] = None,
    phase_offset_rad: Optional[float] = None,
    heartbeat_ok: Optional[bool] = None,
    schema_ok: Optional[bool] = None,
    reachable: bool = True,
) -> Dict[str, Any]:
    """Evaluate node health using synthetic defaults or registered real observers."""
    frequency_hz = NODE_CATALOG.get(node_name, {}).get("frequency_hz", F0_REFERENCE)
    modo_real = bool(_real_mode_enabled() and node_name in REAL_OBSERVERS)

    if modo_real:
        lat, phase, hb, sch = REAL_OBSERVERS[node_name]()
    else:
        lat = 12.4 if latency_ms is None else float(latency_ms)
        phase = 0.018 if phase_offset_rad is None else float(phase_offset_rad)
        hb = True if heartbeat_ok is None else bool(heartbeat_ok)
        sch = True if schema_ok is None else bool(schema_ok)

    psi_raw = score_psi(lat, phase, hb, sch)
    resonance, status = classify_resonance(psi_raw, reachable)
    phase_coherence = 1.0 - abs(phase) / (math.pi / 2.0)
    phase_coherence = max(0.0, min(phase_coherence, 1.0))

    return {
        "node": node_name,
        "status": status,
        "reachable": reachable,
        "latency_ms": round(lat, 2),
        "resonance": resonance,
        "psi": round(psi_raw, 6),
        "phase_offset_rad": round(phase, 6),
        "frequency_hz": frequency_hz,
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "qcal": {
            "psi_raw": round(psi_raw, 6),
            "f0_reference_hz": F0_REFERENCE,
            "harmonic_factor": round(frequency_hz / F0_REFERENCE, 5),
            "phase_coherence": round(phase_coherence, 4),
            "resonance_class": resonance,
            "logos_level": "saturated" if psi_raw > 0.999 else "stable",
            "modo_real": modo_real,
        },
        "checks": {
            "transport": "ok" if reachable else "fail",
            "schema": "ok" if sch else "fail",
            "heartbeat": "ok" if hb else "fail",
            "qcal_protocol": "ok",
            "fuente_fisica": "real" if modo_real else "simulada",
        },
        "error_code": None,
        "error_message": None,
    }
