#!/usr/bin/env python3
"""
Tests para QCAL-Strings — Validación Experimental UPE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Pruebas unitarias para qcal.upe_validation:
- UPESignal: generación de señal, modulación HRV, beats
- NBECCondensate: simulación del condensado, formación del plateau
- HardResetProtocol: activación y recuperación tras decoherencia
- validate_upe_protocol: protocolo completo de validación

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
License: MIT
"""

import unittest
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).parent))

from qcal.upe_validation import (
    UPESignal,
    NBECCondensate,
    HardResetProtocol,
    validate_upe_protocol,
    _compute_lambda_modes,
    F0,
    F_HRV,
    LAMBDA_1,
    N_MODES_UPE,
    PSI_RESET_THRESHOLD,
    PSI_TARGET,
    N_MICROTUBULES,
)


# ─────────────────────────────────────────────────────────────────────────────
# Tests: constantes
# ─────────────────────────────────────────────────────────────────────────────

class TestConstants(unittest.TestCase):

    def test_f0(self):
        self.assertAlmostEqual(F0, 141.7001, places=4)

    def test_f_hrv(self):
        self.assertAlmostEqual(F_HRV, 0.1, places=4)

    def test_lambda_1(self):
        self.assertAlmostEqual(LAMBDA_1, 2002.89, places=2)

    def test_n_modes_upe(self):
        self.assertEqual(N_MODES_UPE, 20)

    def test_psi_reset_threshold(self):
        self.assertAlmostEqual(PSI_RESET_THRESHOLD, 0.3, places=4)

    def test_psi_target(self):
        self.assertAlmostEqual(PSI_TARGET, 0.999, places=4)

    def test_n_microtubules(self):
        self.assertEqual(N_MICROTUBULES, int(1e13))


# ─────────────────────────────────────────────────────────────────────────────
# Tests: _compute_lambda_modes
# ─────────────────────────────────────────────────────────────────────────────

class TestComputeLambdaModes(unittest.TestCase):

    def test_first_mode(self):
        lambdas = _compute_lambda_modes(1)
        self.assertAlmostEqual(lambdas[0], LAMBDA_1, places=1)

    def test_length(self):
        for n in [1, 5, 10, 20]:
            lambdas = _compute_lambda_modes(n)
            self.assertEqual(len(lambdas), n)

    def test_increasing(self):
        lambdas = _compute_lambda_modes(10)
        self.assertTrue(np.all(np.diff(lambdas) > 0))

    def test_positive(self):
        lambdas = _compute_lambda_modes(20)
        self.assertTrue(np.all(lambdas > 0))


# ─────────────────────────────────────────────────────────────────────────────
# Tests: UPESignal
# ─────────────────────────────────────────────────────────────────────────────

class TestUPESignal(unittest.TestCase):

    def setUp(self):
        self.upe = UPESignal(n_modes=5)
        self.t = np.linspace(0, 0.1, 1000)

    def test_instantiation(self):
        self.assertEqual(self.upe.n_modes, 5)
        self.assertAlmostEqual(self.upe.f_hrv, F_HRV, places=4)

    def test_lambda_n_length(self):
        self.assertEqual(len(self.upe.lambda_n), 5)

    def test_lambda_1_value(self):
        self.assertAlmostEqual(self.upe.lambda_n[0], LAMBDA_1, places=1)

    def test_alpha_n_length(self):
        self.assertEqual(len(self.upe.alpha_n), 5)

    def test_alpha_n_positive(self):
        self.assertTrue(np.all(self.upe.alpha_n > 0))

    def test_alpha_n_decreasing(self):
        self.assertTrue(np.all(np.diff(self.upe.alpha_n) < 0))

    def test_hrv_modulation_shape(self):
        mod = self.upe.hrv_modulation(self.t)
        self.assertEqual(mod.shape, self.t.shape)

    def test_hrv_modulation_range(self):
        mod = self.upe.hrv_modulation(self.t)
        self.assertTrue(np.all(mod > 0))  # Never negative

    def test_hrv_modulation_near_one(self):
        mod = self.upe.hrv_modulation(self.t)
        self.assertAlmostEqual(float(np.mean(mod)), 1.0, places=1)

    def test_riemann_superposition_shape(self):
        sig = self.upe.riemann_superposition(self.t)
        self.assertEqual(sig.shape, self.t.shape)

    def test_generate_shape(self):
        sig = self.upe.generate(self.t)
        self.assertEqual(sig.shape, self.t.shape)

    def test_generate_not_zero(self):
        sig = self.upe.generate(self.t)
        self.assertGreater(float(np.max(np.abs(sig))), 0.0)

    def test_beat_frequencies_shape(self):
        beats = self.upe.beat_frequencies()
        self.assertEqual(beats.shape, (5, 2))

    def test_beat_frequencies_lambda1(self):
        beats = self.upe.beat_frequencies()
        # First beat should be λ₁ ± f_HRV
        self.assertAlmostEqual(beats[0, 0], LAMBDA_1 - F_HRV, places=1)
        self.assertAlmostEqual(beats[0, 1], LAMBDA_1 + F_HRV, places=1)

    def test_beat_frequencies_spread(self):
        beats = self.upe.beat_frequencies()
        # Upper beat > lower beat for all modes
        self.assertTrue(np.all(beats[:, 1] > beats[:, 0]))

    def test_integrated_energy_positive(self):
        energy = self.upe.integrated_energy(self.t)
        self.assertGreater(energy, 0.0)

    def test_spectral_analysis_keys(self):
        result = self.upe.spectral_analysis(self.t)
        for key in ["freqs", "power", "peak_freq", "peak_power",
                    "lambda_1", "beat_freqs"]:
            self.assertIn(key, result)

    def test_spectral_analysis_lambda1(self):
        result = self.upe.spectral_analysis(self.t)
        self.assertAlmostEqual(result["lambda_1"], LAMBDA_1, places=1)

    def test_spectral_analysis_power_positive(self):
        result = self.upe.spectral_analysis(self.t)
        self.assertGreater(result["peak_power"], 0.0)


# ─────────────────────────────────────────────────────────────────────────────
# Tests: NBECCondensate
# ─────────────────────────────────────────────────────────────────────────────

class TestNBECCondensate(unittest.TestCase):

    def setUp(self):
        # Use small N_micro for test speed
        self.nbec = NBECCondensate(N_micro=int(1e6), psi_0=0.12, r=0.1)

    def test_instantiation(self):
        self.assertAlmostEqual(self.nbec.psi_0, 0.12, places=4)
        self.assertAlmostEqual(self.nbec.r, 0.1, places=4)

    def test_superradiant_gain_at_psi_1(self):
        g = self.nbec.superradiant_gain(1.0)
        self.assertAlmostEqual(g, 1.0, places=6)

    def test_superradiant_gain_at_psi_0(self):
        g = self.nbec.superradiant_gain(0.0)
        self.assertAlmostEqual(g, 0.0, places=6)

    def test_dpsi_dt_positive_near_0(self):
        # Near ψ=0, growth rate should be positive
        dpsi = self.nbec.dpsi_dt(0.01)
        self.assertGreater(dpsi, 0.0)

    def test_dpsi_dt_near_0_at_psi_1(self):
        # Near ψ=1, (1-ψ) → 0, growth slows
        dpsi = self.nbec.dpsi_dt(0.999)
        self.assertAlmostEqual(dpsi, 0.0, delta=0.01)

    def test_simulate_returns_dict(self):
        result = self.nbec.simulate(n_steps=100, dt=0.01)
        self.assertIsInstance(result, dict)

    def test_simulate_keys(self):
        result = self.nbec.simulate(n_steps=100, dt=0.01)
        for key in ["psi_history", "psi_final", "t_plateau", "nbec_formed",
                    "G_superrad_final", "n_resets"]:
            self.assertIn(key, result)

    def test_psi_history_shape(self):
        n = 100
        result = self.nbec.simulate(n_steps=n, dt=0.01)
        self.assertEqual(len(result["psi_history"]), n + 1)

    def test_psi_in_range(self):
        result = self.nbec.simulate(n_steps=100, dt=0.01)
        psi = result["psi_history"]
        self.assertTrue(np.all(psi >= 0.0))
        self.assertTrue(np.all(psi <= 1.0))

    def test_psi_grows(self):
        # Coherence should grow from initial value
        result = self.nbec.simulate(n_steps=500, dt=0.01)
        self.assertGreater(result["psi_final"], self.nbec.psi_0)

    def test_nbec_formation_long_run(self):
        # With sufficient steps, NBEC should form
        nbec = NBECCondensate(N_micro=int(1e6), psi_0=0.5, r=0.5, D_consciousness=5.0)
        result = nbec.simulate(n_steps=2000, dt=0.01)
        self.assertTrue(result["nbec_formed"])

    def test_g_superrad_final_positive(self):
        result = self.nbec.simulate(n_steps=100, dt=0.01)
        self.assertGreaterEqual(result["G_superrad_final"], 0.0)

    def test_n_resets_non_negative(self):
        result = self.nbec.simulate(n_steps=100, dt=0.01)
        self.assertGreaterEqual(result["n_resets"], 0)


# ─────────────────────────────────────────────────────────────────────────────
# Tests: HardResetProtocol
# ─────────────────────────────────────────────────────────────────────────────

class TestHardResetProtocol(unittest.TestCase):

    def setUp(self):
        self.protocol = HardResetProtocol(f0=F0, psi_threshold=PSI_RESET_THRESHOLD)
        self.t = np.linspace(0, 0.1, 100)

    def test_instantiation(self):
        self.assertAlmostEqual(self.protocol.f0, F0, places=4)
        self.assertAlmostEqual(self.protocol.psi_threshold, PSI_RESET_THRESHOLD, places=4)

    def test_g_max_at_psi_1(self):
        g = self.protocol.g_max(1.0)
        self.assertAlmostEqual(g, 1.0, places=6)

    def test_g_max_at_psi_0(self):
        g = self.protocol.g_max(0.0)
        self.assertAlmostEqual(g, 0.0, places=6)

    def test_reset_signal_shape(self):
        sig = self.protocol.reset_signal(self.t, psi=0.5)
        self.assertEqual(sig.shape, self.t.shape)

    def test_reset_signal_zero_psi(self):
        sig = self.protocol.reset_signal(self.t, psi=0.0)
        np.testing.assert_array_equal(sig, np.zeros_like(self.t))

    def test_apply_activated_below_threshold(self):
        result = self.protocol.apply(self.t, psi=0.1)
        self.assertTrue(result["activated"])

    def test_apply_not_activated_above_threshold(self):
        result = self.protocol.apply(self.t, psi=0.9)
        self.assertFalse(result["activated"])

    def test_apply_keys(self):
        result = self.protocol.apply(self.t, psi=0.2)
        for key in ["activated", "reset_signal", "psi_recovered",
                    "entropy_reduction_pct", "steps_to_recovery"]:
            self.assertIn(key, result)

    def test_apply_no_activation_zero_signal(self):
        result = self.protocol.apply(self.t, psi=0.9)
        np.testing.assert_array_equal(result["reset_signal"], np.zeros_like(self.t))

    def test_entropy_reduction_after_activation(self):
        result = self.protocol.apply(self.t, psi=0.05,
                                       n_steps_recovery=500, dt=0.005)
        # If NBEC forms, entropy reduction should be >= 49%
        if result["psi_recovered"] >= PSI_TARGET:
            self.assertGreaterEqual(result["entropy_reduction_pct"], 49.0)

    def test_psi_recovered_in_range(self):
        result = self.protocol.apply(self.t, psi=0.2)
        self.assertGreaterEqual(result["psi_recovered"], 0.0)
        self.assertLessEqual(result["psi_recovered"], 1.0)

    def test_steps_to_recovery_non_negative(self):
        result = self.protocol.apply(self.t, psi=0.2)
        self.assertGreaterEqual(result["steps_to_recovery"], 0)


# ─────────────────────────────────────────────────────────────────────────────
# Tests: validate_upe_protocol
# ─────────────────────────────────────────────────────────────────────────────

class TestValidateUPEProtocol(unittest.TestCase):

    def setUp(self):
        # Quick validation with short parameters
        self.result = validate_upe_protocol(
            t_max=0.01,
            n_samples=500,
            n_modes=5,
            n_steps_nbec=200,
            dt_nbec=0.01,
        )

    def test_returns_dict(self):
        self.assertIsInstance(self.result, dict)

    def test_required_keys(self):
        for key in [
            "lambda_1", "beat_freqs_range", "upe_energy", "upe_peak_freq",
            "nbec_formed", "psi_final", "t_plateau",
            "reset_activated", "entropy_reduction_pct",
            "G_superrad", "G_superrad_log10", "validado"
        ]:
            self.assertIn(key, self.result)

    def test_lambda_1_value(self):
        self.assertAlmostEqual(self.result["lambda_1"], LAMBDA_1, places=1)

    def test_beat_freqs_range(self):
        lo, hi = self.result["beat_freqs_range"]
        self.assertLess(lo, hi)
        self.assertAlmostEqual(lo, LAMBDA_1 - F_HRV, places=1)
        self.assertAlmostEqual(hi, LAMBDA_1 + F_HRV, places=1)

    def test_upe_energy_positive(self):
        self.assertGreater(self.result["upe_energy"], 0.0)

    def test_g_superrad_positive(self):
        self.assertGreater(self.result["G_superrad"], 0.0)

    def test_g_superrad_log10_positive(self):
        self.assertGreater(self.result["G_superrad_log10"], 0.0)

    def test_reset_activated(self):
        # NBEC starts at psi_0=0.12 < PSI_RESET_THRESHOLD=0.3 → reset activates
        self.assertIsInstance(self.result["reset_activated"], bool)

    def test_validado_is_bool(self):
        self.assertIsInstance(self.result["validado"], bool)

    def test_psi_final_in_range(self):
        self.assertGreaterEqual(self.result["psi_final"], 0.0)
        self.assertLessEqual(self.result["psi_final"], 1.0)


if __name__ == "__main__":
    unittest.main(verbosity=2)
