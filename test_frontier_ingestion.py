#!/usr/bin/env python3
"""
Tests for Phase 2 frontier ingestion.
"""

import os
import tempfile
import unittest

import numpy as np
import yaml

from src.data.frontier_ingestion import FrontierIngestion
from src.data.quality_control import QualityControl


class TestFrontierIngestion(unittest.TestCase):
    def setUp(self):
        self.temp_dir = tempfile.TemporaryDirectory()
        self.config_path = os.path.join(self.temp_dir.name, "frontier_config.yaml")
        with open(self.config_path, "w", encoding="utf-8") as handle:
            yaml.safe_dump({"cache_dir": self.temp_dir.name, "simulate": True}, handle)

    def tearDown(self):
        self.temp_dir.cleanup()

    def test_ingest_all_creates_sources_and_cache(self):
        ingestion = FrontierIngestion(self.config_path)
        results = ingestion.ingest_all(forecast_hour=6)
        summary = ingestion.source_summary()

        self.assertIn("gfs", results)
        self.assertTrue(summary["gfs"]["active"])
        self.assertTrue(summary["ecmwf"]["active"])
        self.assertTrue(os.path.exists(summary["gfs"]["cache_path"]))
        self.assertTrue(os.path.exists(summary["socib"]["cache_path"]))


class TestQualityControl(unittest.TestCase):
    def test_check_qcal_field(self):
        psi = np.array([[1.0, 0.999998], [1.2, -0.1]])
        checked, below = QualityControl.check_qcal_field(psi)
        self.assertTrue(np.isnan(checked[1, 0]))
        self.assertTrue(np.isnan(checked[1, 1]))
        self.assertEqual(int(np.nansum(below)), 1)


if __name__ == "__main__":
    unittest.main()
