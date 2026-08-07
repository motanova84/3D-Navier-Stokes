#!/usr/bin/env python3
"""
Tests for Phase 4 forecasting and Phase 5 verification/certification.
"""

from __future__ import annotations

import asyncio
import os
import subprocess
import tempfile
import unittest

import numpy as np
import xarray as xr

from src.forecast.nowcasting_engine import NowcastingEngine
from src.forecast.temporal_predictor import PredictorConfig, TemporalPredictor
from src.verification.operational_verification import OperationalVerification


def build_state() -> xr.Dataset:
    y = np.linspace(-1.0, 1.0, 6)
    x = np.linspace(-1.0, 1.0, 6)
    xx, yy = np.meshgrid(x, y)
    psi = np.clip(0.999999 + 1e-7 * np.sin(np.pi * xx), 0.0, 1.0)
    return xr.Dataset(
        {
            "u": (("y", "x"), 8.0 + 0.5 * xx),
            "v": (("y", "x"), 1.5 + 0.2 * yy),
            "T": (("y", "x"), 288.0 + yy),
            "p": (("y", "x"), 101325.0 + 25.0 * xx),
            "psi": (("y", "x"), psi),
            "coherence": (("y", "x"), psi.copy()),
            "entropy": (("y", "x"), -psi * np.log(psi + 1e-12)),
            "freq_dev": (("y", "x"), (psi - 0.999999) * 141.7001),
        },
        coords={"y": y, "x": x},
    )


class TestPhase4Forecast(unittest.TestCase):
    def test_temporal_predictor_forecast_and_save(self):
        state = build_state()
        with tempfile.TemporaryDirectory() as temp_dir:
            predictor = TemporalPredictor(
                PredictorConfig(forecast_hours=(1, 2), dt_seconds=600.0, output_dir=temp_dir)
            )
            predictor.initialize_state(state)
            forecast = predictor.integrate_forecast(steps=12, output_frequency=6)
            self.assertIn(1, forecast)
            predictor.save_forecast(forecast, name="baseline")
            loaded = predictor.load_forecast(name="baseline", hour=1)
            self.assertIsNotNone(loaded)

    def test_nowcasting_engine_cycle(self):
        state = build_state()
        with tempfile.TemporaryDirectory() as temp_dir:
            engine = NowcastingEngine(forecast_hours=[1], output_dir=temp_dir, update_interval=0)
            engine.state = state
            asyncio.run(engine.start(cycles=1))
            self.assertIn(1, engine.nowcasts)
            self.assertIsNotNone(engine.last_publication)


class TestPhase5Verification(unittest.TestCase):
    def test_operational_verification_and_certification_script(self):
        state = build_state()
        with tempfile.TemporaryDirectory() as temp_dir:
            baseline_dir = os.path.join(temp_dir, "baseline")
            qcal_dir = os.path.join(temp_dir, "qcal")
            obs_dir = os.path.join(temp_dir, "observations")
            os.makedirs(baseline_dir, exist_ok=True)
            os.makedirs(qcal_dir, exist_ok=True)
            os.makedirs(obs_dir, exist_ok=True)

            for hour in (6, 12, 24, 48, 72):
                baseline = state.copy(deep=True)
                qcal = state.copy(deep=True)
                obs = state.copy(deep=True)
                baseline["u"].values = baseline["u"].values + 0.4
                qcal["u"].values = qcal["u"].values + 0.1
                baseline.to_zarr(os.path.join(baseline_dir, f"baseline_f{hour:03d}.zarr"), mode="w", consolidated=False)
                qcal.to_zarr(os.path.join(qcal_dir, f"qcal_f{hour:03d}.zarr"), mode="w", consolidated=False)
                obs.to_zarr(os.path.join(obs_dir, f"obs_f{hour:03d}.zarr"), mode="w", consolidated=False)

            verification = OperationalVerification()
            report = verification.run_benchmark(
                {h: xr.open_zarr(os.path.join(baseline_dir, f"baseline_f{h:03d}.zarr"), consolidated=False) for h in (6, 12, 24, 48, 72)},
                {h: xr.open_zarr(os.path.join(qcal_dir, f"qcal_f{h:03d}.zarr"), consolidated=False) for h in (6, 12, 24, 48, 72)},
                {h: xr.open_zarr(os.path.join(obs_dir, f"obs_f{h:03d}.zarr"), consolidated=False) for h in (6, 12, 24, 48, 72)},
            )
            self.assertIn(6, report)
            output_report = os.path.join(temp_dir, "verification_report.json")
            verification.generate_verification_report(output_report)
            self.assertTrue(os.path.exists(output_report))

            cert_path = os.path.join(temp_dir, "CERTIFICATION.md")
            env = os.environ.copy()
            env["BASELINE_PATH"] = baseline_dir
            env["QCAL_PATH"] = qcal_dir
            env["OBS_PATH"] = obs_dir
            env["REPORT_PATH"] = output_report
            env["CERT_PATH"] = cert_path
            subprocess.run(["bash", "scripts/certify_system.sh"], check=True, cwd=os.getcwd(), env=env)
            self.assertTrue(os.path.exists(cert_path))


if __name__ == "__main__":
    unittest.main()
