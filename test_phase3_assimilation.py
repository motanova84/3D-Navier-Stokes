#!/usr/bin/env python3
"""
Tests for Phase 3 assimilation and variational coupling.
"""

from __future__ import annotations

import os
import tempfile
import unittest

import numpy as np
import xarray as xr

from src.assimilation.enkf import EnKFConfig, EnsembleKalmanFilter
from src.assimilation.qcal_coupling import QCALVariationalCoupling


def build_state() -> xr.Dataset:
    y = np.linspace(-1.0, 1.0, 6)
    x = np.linspace(-1.0, 1.0, 6)
    xx, yy = np.meshgrid(x, y)
    psi = np.clip(0.999999 + 1e-7 * np.sin(np.pi * xx * yy), 0.0, 1.0)
    return xr.Dataset(
        {
            "u": (("y", "x"), 8.0 + 0.5 * xx),
            "v": (("y", "x"), 1.5 + 0.3 * yy),
            "T": (("y", "x"), 288.0 + yy),
            "p": (("y", "x"), 101325.0 + 50.0 * xx),
            "psi": (("y", "x"), psi),
            "coherence": (("y", "x"), psi.copy()),
            "entropy": (("y", "x"), -psi * np.log(psi + 1e-12)),
            "freq_dev": (("y", "x"), (psi - 0.999999) * 141.7001),
        },
        coords={"y": y, "x": x},
    )


class TestPhase3Assimilation(unittest.TestCase):
    def test_enkf_analysis_and_zarr_output(self):
        state = build_state()
        enkf = EnsembleKalmanFilter(EnKFConfig(ensemble_size=4))
        ensemble = enkf.initialize_ensemble(state, noise_std=0.01)
        self.assertEqual(len(ensemble), 4)

        observations = {
            "u": state["u"] + 0.1,
            "T": state["T"] - 0.2,
        }
        posterior = enkf.assimilate_observations(observations, {"u": 0.5, "T": 0.5})
        self.assertIn("psi", posterior.data_vars)

        with tempfile.TemporaryDirectory() as temp_dir:
            path = os.path.join(temp_dir, "posterior.zarr")
            written = enkf.save_posterior_to_zarr(path)
            self.assertTrue(written.exists())

    def test_variational_coupling_cycle(self):
        background = build_state()
        ensemble_mean = build_state()
        observations = {"u": background["u"] + 0.2, "psi": background["psi"]}
        coupling = QCALVariationalCoupling()
        analysis, metrics = coupling.qcal_analysis_cycle(background, observations, ensemble_mean)
        self.assertIn("cost_final", metrics)
        self.assertGreaterEqual(metrics["coherence_min"], 0.0)
        self.assertLessEqual(metrics["coherence_max"], 1.0)
        self.assertIn("psi", analysis.data_vars)


if __name__ == "__main__":
    unittest.main()
