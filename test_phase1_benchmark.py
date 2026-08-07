#!/usr/bin/env python3
"""
Tests for Phase 1 benchmark orchestration.
"""

import json
import os
import tempfile
import unittest

from src.orchestrator.phase1_benchmark import DomainConfig, Phase1Benchmark, QCALConfig


class TestPhase1Benchmark(unittest.TestCase):
    def test_small_benchmark_and_checkpoint(self):
        domain = DomainConfig(nx=8, ny=8, nz=4, dt=2.0)
        benchmark = Phase1Benchmark(domain, QCALConfig())
        stats = benchmark.run_benchmark(steps=3)

        self.assertIn("avg_time_ms", stats)
        self.assertEqual(stats["domain_cells"], 8 * 8 * 4)
        self.assertGreater(stats["steps_per_second"], 0.0)

        with tempfile.TemporaryDirectory() as temp_dir:
            checkpoint_path = os.path.join(temp_dir, "checkpoint_test.npz")
            output_path = os.path.join(temp_dir, "benchmark_results.json")

            size = benchmark.save_checkpoint(checkpoint_path)
            self.assertGreater(size, 0)
            self.assertTrue(os.path.exists(checkpoint_path))

            with open(output_path, "w", encoding="utf-8") as handle:
                json.dump(stats, handle)
            self.assertTrue(os.path.exists(output_path))


if __name__ == "__main__":
    unittest.main()
