import math
import os
from pathlib import Path

import pandas as pd
import pytest

from mcp_network.resonance import (
    F0_REFERENCE,
    PSI_GATE,
    check_node_resonance,
)


pytestmark = pytest.mark.skipif(
    os.getenv("QCAL_REAL_TESTS") != "1",
    reason="Set QCAL_REAL_TESTS=1 to run physical observer tests",
)


class TestCheckNodeResonanceRealObservers:
    def test_biologia_cuantica_psi_above_gate(self):
        health = check_node_resonance("biologia-cuantica-noesica")
        assert health["psi"] >= PSI_GATE

    def test_biologia_cuantica_phase_calculation(self):
        path = Path("tests/data/hrv_eeg_biologia_cuantica.csv")
        df = pd.read_csv(path)
        rr_mean = df["rr_interval_ms"].mean()
        expected_rr = 1000 / (F0_REFERENCE / 2)
        expected_phase = 2 * math.pi * ((rr_mean - expected_rr) / 1000) * 60.0

        health = check_node_resonance("biologia-cuantica-noesica")
        assert health["phase_offset_rad"] == pytest.approx(expected_phase, abs=1e-12)

    def test_biologia_cuantica_harmonic_factor(self):
        health = check_node_resonance("biologia-cuantica-noesica")
        assert health["qcal"]["harmonic_factor"] == 0.5

    def test_biologia_cuantica_mode_is_real(self):
        health = check_node_resonance("biologia-cuantica-noesica")
        assert health["qcal"]["modo_real"] is True

    def test_biologia_cuantica_physical_source_tag(self):
        health = check_node_resonance("biologia-cuantica-noesica")
        assert health["checks"]["fuente_fisica"] == "real"

    def test_biologia_cuantica_gate_consistency(self):
        health = check_node_resonance("biologia-cuantica-noesica")
        assert health["checks"]["psi_gate"] == PSI_GATE
        assert health["checks"]["above_gate"] is True

    def test_biologia_cuantica_observer_registered(self):
        health = check_node_resonance("biologia-cuantica-noesica")
        assert health["node"] == "biologia-cuantica-noesica"
        assert health["resonance"] == "coherent"

    def test_interferometro_psi_above_gate(self):
        health = check_node_resonance("interferometro-noesico")
        assert health["psi"] >= PSI_GATE

    def test_interferometro_phase_from_magnetometer(self):
        path = Path("tests/data/magnetometer_interferometer.csv")
        df = pd.read_csv(path)
        peak_freq = df["frequency_hz"].mean()
        target = F0_REFERENCE * 2
        expected_phase = 2 * math.pi * (peak_freq - target) / target

        health = check_node_resonance("interferometro-noesico")
        assert health["phase_offset_rad"] == pytest.approx(expected_phase, abs=1e-12)

    def test_interferometro_harmonic_factor(self):
        health = check_node_resonance("interferometro-noesico")
        assert health["qcal"]["harmonic_factor"] == 2.0

    def test_interferometro_mode_is_real(self):
        health = check_node_resonance("interferometro-noesico")
        assert health["qcal"]["modo_real"] is True

    def test_interferometro_physical_source_tag(self):
        health = check_node_resonance("interferometro-noesico")
        assert health["checks"]["fuente_fisica"] == "real"

    def test_interferometro_gate_consistency(self):
        health = check_node_resonance("interferometro-noesico")
        assert health["checks"]["psi_gate"] == PSI_GATE
        assert health["checks"]["above_gate"] is True

    def test_interferometro_observer_registered(self):
        health = check_node_resonance("interferometro-noesico")
        assert health["node"] == "interferometro-noesico"
        assert health["resonance"] == "coherent"
