"""Tests for MCP resonance synthetic and real-observer flows."""

from __future__ import annotations

import os
import tempfile
import unittest
from unittest.mock import patch

from mcp_network.resonance import (
    check_node_resonance,
    classify_resonance,
    register_real_observer,
    score_psi,
)


class TestMCPResonanceEngine(unittest.TestCase):
    def test_score_psi_bounds_and_flags(self) -> None:
        psi = score_psi(latency_ms=10.0, phase_offset_rad=0.01, heartbeat_ok=True, schema_ok=True)
        self.assertGreaterEqual(psi, 0.0)
        self.assertLessEqual(psi, 1.0)
        self.assertEqual(score_psi(10.0, 0.01, heartbeat_ok=False, schema_ok=True), 0.0)
        self.assertEqual(score_psi(10.0, 0.01, heartbeat_ok=True, schema_ok=False), 0.0)

    def test_classify_resonance_thresholds(self) -> None:
        self.assertEqual(classify_resonance(1.0, True), ("coherent", "pass"))
        self.assertEqual(classify_resonance(0.96, True), ("drifting", "warn"))
        self.assertEqual(classify_resonance(0.4, True), ("fault", "fail"))
        self.assertEqual(classify_resonance(0.999, False), ("offline", "fail"))

    def test_synthetic_mode_by_default(self) -> None:
        with patch.dict(os.environ, {}, clear=False):
            os.environ.pop("QCAL_REAL_TESTS", None)
            health = check_node_resonance("auron-governor")
        self.assertFalse(health["qcal"]["modo_real"])
        self.assertEqual(health["checks"]["fuente_fisica"], "simulada")

    def test_real_mode_with_grid_csv(self) -> None:
        with tempfile.NamedTemporaryFile("w", suffix=".csv", delete=False, encoding="utf-8") as handle:
            handle.write("frequency_hz\n")
            handle.write("50.01\n")
            handle.write("49.99\n")
            path = handle.name

        try:
            with patch.dict(
                os.environ,
                {"QCAL_REAL_TESTS": "1", "QCAL_GRID_SAMPLE_PATH": path, "QCAL_GRID_LATENCY_MS": "21.5"},
                clear=False,
            ):
                health = check_node_resonance("auron-governor")
            self.assertTrue(health["qcal"]["modo_real"])
            self.assertEqual(health["checks"]["fuente_fisica"], "real")
            self.assertEqual(health["latency_ms"], 21.5)
            self.assertEqual(health["frequency_hz"], 50.0)
        finally:
            os.unlink(path)

    def test_custom_observer_in_real_mode(self) -> None:
        register_real_observer("interferometro-noesico", lambda: (5.0, 0.001, True, True))
        with patch.dict(os.environ, {"QCAL_REAL_TESTS": "true"}, clear=False):
            health = check_node_resonance("interferometro-noesico")
        self.assertTrue(health["qcal"]["modo_real"])
        self.assertIn(health["status"], {"pass", "warn"})
        self.assertEqual(health["frequency_hz"], 283.4002)


if __name__ == "__main__":
    unittest.main()
