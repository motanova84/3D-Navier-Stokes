#!/usr/bin/env python3
"""
Tests for the unified 5-phase NOESIS production workflow.
"""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from qcal_weather import RegionalDomainConfig, build_technical_certification
from src.orchestrator.phase1_benchmark import DomainConfig
from src.pipeline.noesis_production_workflow import NOESISProductionWorkflow


class TestNOESISProductionWorkflow(unittest.TestCase):
    def test_run_writes_all_sealing_artifacts(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            workflow = NOESISProductionWorkflow(
                root_dir="/home/runner/work/3D-Navier-Stokes/3D-Navier-Stokes",
                output_dir=temp_dir,
                benchmark_steps=1,
                forecast_hours=(6, 12),
                phase1_domain=DomainConfig(nx=6, ny=6, nz=3, dt=2.0),
            )
            artifacts = workflow.run()

            for path in (
                artifacts.benchmark_stats_path,
                artifacts.checkpoint_path,
                artifacts.ingestion_summary_path,
                artifacts.analysis_state_path,
                artifacts.analysis_metrics_path,
                artifacts.verification_report_path,
                artifacts.certification_path,
                artifacts.final_act_path,
                artifacts.production_certificate_path,
                artifacts.deployment_map_path,
                artifacts.final_seal_path,
            ):
                with self.subTest(path=path):
                    self.assertTrue(Path(path).exists())

    def test_technical_certification_has_five_phases(self):
        certification = build_technical_certification(RegionalDomainConfig())
        self.assertEqual(len(certification.phases), 5)
        self.assertEqual(certification.phases[0].name, "Phase 1 — Benchmark & Mesh")
        self.assertEqual(certification.phases[-1].name, "Phase 5 — Verification & Production Seal")


if __name__ == "__main__":
    unittest.main()
