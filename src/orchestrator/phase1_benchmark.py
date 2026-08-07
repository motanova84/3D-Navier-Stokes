#!/usr/bin/env python3
"""
Phase 1 benchmark and checkpoint generator for QCAL-Balearic Nowcast.

Uses CuPy when available and falls back to NumPy in CPU-only environments.
"""

from __future__ import annotations

import argparse
import json
import logging
import os
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Tuple

import numpy as np

try:
    import cupy as cp  # type: ignore
except ImportError:  # pragma: no cover - exercised implicitly in CPU environments
    cp = None


LOGGER = logging.getLogger("qcal-balearic-phase1")
F0_HZ = 141.7001


@dataclass(frozen=True)
class DomainConfig:
    nx: int = 167
    ny: int = 167
    nz: int = 60
    dx: float = 3000.0
    dy: float = 3000.0
    dz: float = 500.0
    dt: float = 10.0

    @property
    def size(self) -> int:
        return self.nx * self.ny * self.nz


@dataclass(frozen=True)
class QCALConfig:
    f0_hz: float = F0_HZ
    alpha: float = 0.05
    lambda_coeff: float = 0.01
    d_psi: float = 0.1
    psi_ref: float = 0.999999


class Phase1Benchmark:
    def __init__(self, domain: DomainConfig, qcal: QCALConfig):
        self.domain = domain
        self.qcal = qcal
        self.xp = cp if cp is not None else np
        self.backend = "cupy" if cp is not None else "numpy"
        self.allocate_fields()

    def allocate_fields(self) -> None:
        xp = self.xp
        n = self.domain.size
        grid = xp.linspace(-1.0, 1.0, n, dtype=xp.float32)
        self.u = 8.0 + 0.5 * grid
        self.v = 1.5 - 0.25 * grid
        self.w = xp.zeros(n, dtype=xp.float32)
        self.T = 288.0 + 2.0 * grid
        self.p = 101325.0 + 100.0 * grid
        self.q = xp.full(n, 0.01, dtype=xp.float32)
        self.psi = xp.full(n, self.qcal.psi_ref, dtype=xp.float32)

    def _sync(self) -> None:
        if self.backend == "cupy":
            cp.cuda.Stream.null.synchronize()

    def step(self) -> None:
        xp = self.xp
        thermal_gradient = (self.T - 288.0) / 288.0
        pressure_gradient = (self.p - 101325.0) / 101325.0
        forcing = (
            xp.square(self.u) * 1e-4
            + xp.square(self.v) * 1e-4
            + xp.abs(thermal_gradient) * 0.5
            + xp.abs(pressure_gradient) * 0.2
        ).astype(xp.float32)

        self.u = self.u + self.domain.dt * (-0.001 * self.u + 0.02 * thermal_gradient)
        self.v = self.v + self.domain.dt * (-0.001 * self.v - 0.01 * pressure_gradient)
        self.T = self.T + self.domain.dt * (-0.0005 * (self.T - 288.0) + 0.001 * self.u)
        self.p = self.p + self.domain.dt * (-0.0002 * (self.p - 101325.0) - 0.05 * self.v)
        self.q = xp.clip(self.q + self.domain.dt * (-0.0001 * self.q + 1e-5 * self.T), 0.0, 1.0)
        self.psi = xp.clip(
            self.psi
            + self.domain.dt
            * (
                self.qcal.d_psi * (self.qcal.psi_ref - self.psi)
                - self.qcal.lambda_coeff * (self.psi - self.qcal.psi_ref)
                + self.qcal.alpha * forcing
            ),
            0.0,
            1.0,
        )

    def run_benchmark(self, steps: int = 100) -> Dict[str, float]:
        timings = []
        for _ in range(steps):
            start = time.perf_counter()
            self.step()
            self._sync()
            timings.append(time.perf_counter() - start)

        array_bytes = sum(
            int(array.nbytes)
            for array in (self.u, self.v, self.w, self.T, self.p, self.q, self.psi)
        )
        return {
            "backend": self.backend,
            "steps": steps,
            "avg_time_ms": float(np.mean(timings) * 1000.0),
            "std_time_ms": float(np.std(timings) * 1000.0),
            "min_time_ms": float(np.min(timings) * 1000.0),
            "max_time_ms": float(np.max(timings) * 1000.0),
            "total_time_s": float(np.sum(timings)),
            "steps_per_second": float(steps / np.sum(timings)),
            "field_memory_gb": float(array_bytes / (1024**3)),
            "domain_cells": self.domain.size,
            "dt_seconds": self.domain.dt,
        }

    def save_checkpoint(self, path: str) -> int:
        arrays = {}
        for name in ("u", "v", "w", "T", "p", "q", "psi"):
            field = getattr(self, name)
            arrays[name] = cp.asnumpy(field) if self.backend == "cupy" else np.asarray(field)
        np.savez_compressed(path, **arrays)
        return os.path.getsize(path)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Run Phase 1 benchmark for QCAL-Balearic Nowcast.")
    parser.add_argument("--steps", type=int, default=100)
    parser.add_argument("--domain", type=int, nargs=3, metavar=("NX", "NY", "NZ"), default=(167, 167, 60))
    parser.add_argument("--dt", type=float, default=10.0)
    parser.add_argument("--output", default="benchmark_results.json")
    parser.add_argument("--checkpoint", default="checkpoint_initial.npz")
    return parser.parse_args()


def main() -> None:
    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(message)s")
    args = parse_args()
    domain = DomainConfig(nx=args.domain[0], ny=args.domain[1], nz=args.domain[2], dt=args.dt)
    qcal = QCALConfig()
    benchmark = Phase1Benchmark(domain, qcal)

    LOGGER.info("Starting Phase 1 benchmark")
    LOGGER.info("Domain: %s x %s x %s (%s cells)", domain.nx, domain.ny, domain.nz, domain.size)
    LOGGER.info("Backend: %s", benchmark.backend)

    stats = benchmark.run_benchmark(steps=args.steps)
    checkpoint_size = benchmark.save_checkpoint(args.checkpoint)
    stats["checkpoint_size_bytes"] = checkpoint_size
    stats["checkpoint_path"] = str(Path(args.checkpoint).resolve())
    stats["frequency_base_hz"] = F0_HZ

    with open(args.output, "w", encoding="utf-8") as handle:
        json.dump(stats, handle, indent=2)

    LOGGER.info("Benchmark results written to %s", args.output)
    LOGGER.info("Checkpoint written to %s", args.checkpoint)


if __name__ == "__main__":
    main()
