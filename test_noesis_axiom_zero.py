#!/usr/bin/env python3
"""
Tests for noesis_axiom_zero — Continuous Macroscopic Coherence Field (QCAL).

Covers:
  - spectral_purity_coherence
  - autocorrelation_coherence
  - coherence_uncertainty (GUM propagation)
  - psi_threshold_sigma_f
  - integration_region
"""

import unittest
from math import pi, sqrt

import numpy as np

from noesis_axiom_zero import (
    F0_HZ,
    PSI_TOTAL,
    S_VN_MAX,
    T_MIN_S,
    CoherenceEstimate,
    CoherenceUncertainty,
    IntegrationRegion,
    autocorrelation_coherence,
    coherence_uncertainty,
    integration_region,
    psi_threshold_sigma_f,
    spectral_purity_coherence,
)


class TestConstants(unittest.TestCase):
    def test_f0_value(self):
        self.assertAlmostEqual(F0_HZ, 141.7001, places=4)

    def test_psi_total_value(self):
        self.assertAlmostEqual(PSI_TOTAL, 0.999999, places=6)

    def test_s_vn_max(self):
        self.assertAlmostEqual(S_VN_MAX, 0.01, places=6)

    def test_t_min_s(self):
        # T_min = 10 / f₀ ≈ 0.07057 s
        self.assertAlmostEqual(T_MIN_S, 10.0 / F0_HZ, places=10)
        self.assertGreater(T_MIN_S, 1.0 / F0_HZ)  # T_min ≫ larmor period


class TestSpectralPurityCoherence(unittest.TestCase):
    """Tests for spectral_purity_coherence."""

    def _make_pure_tone(self, f_hz: float, duration_s: float = 1.0, sr: float = 2000.0) -> np.ndarray:
        t = np.arange(int(duration_s * sr)) / sr
        return np.sin(2.0 * pi * f_hz * t)

    def test_perfect_tone_at_f0_high_coherence(self):
        signal = self._make_pure_tone(F0_HZ, duration_s=2.0, sr=2000.0)
        result = spectral_purity_coherence(signal, sample_rate_hz=2000.0)
        # A pure discrete sinusoid gives high Ψ, but finite-length edge effects
        # from np.diff on the unwrapped phase produce a small σ_f > 0.
        # The threshold is set conservatively at 0.85 (actual ≈ 0.90).
        self.assertGreater(result.psi, 0.85)
        # σ_f must be much smaller than f₀
        self.assertLess(result.sigma_f_hz, 0.2 * F0_HZ)

    def test_noisy_tone_lower_coherence(self):
        rng = np.random.default_rng(42)
        signal = self._make_pure_tone(F0_HZ, duration_s=2.0, sr=2000.0)
        noise = rng.normal(0, 0.5, len(signal))
        result_pure = spectral_purity_coherence(signal, sample_rate_hz=2000.0)
        result_noisy = spectral_purity_coherence(signal + noise, sample_rate_hz=2000.0)
        self.assertGreater(result_pure.psi, result_noisy.psi)

    def test_psi_clamped_to_unit_interval(self):
        rng = np.random.default_rng(7)
        signal = rng.normal(0, 1, 2000)
        result = spectral_purity_coherence(signal, sample_rate_hz=2000.0)
        self.assertGreaterEqual(result.psi, 0.0)
        self.assertLessEqual(result.psi, 1.0)

    def test_returns_coherence_estimate_type(self):
        signal = self._make_pure_tone(F0_HZ)
        result = spectral_purity_coherence(signal, sample_rate_hz=2000.0)
        self.assertIsInstance(result, CoherenceEstimate)
        self.assertEqual(result.f0_hz, F0_HZ)

    def test_invalid_sample_rate_raises(self):
        with self.assertRaises(ValueError):
            spectral_purity_coherence(np.ones(100), sample_rate_hz=0.0)

    def test_invalid_f0_raises(self):
        with self.assertRaises(ValueError):
            spectral_purity_coherence(np.ones(100), sample_rate_hz=1000.0, f0_hz=-1.0)

    def test_too_short_signal_raises(self):
        with self.assertRaises(ValueError):
            spectral_purity_coherence(np.array([1.0, 2.0]), sample_rate_hz=1000.0)

    def test_formula_psi_equals_1_minus_sigmaf_over_f0(self):
        signal = self._make_pure_tone(F0_HZ, duration_s=2.0, sr=2000.0)
        result = spectral_purity_coherence(signal, sample_rate_hz=2000.0)
        expected_psi = max(0.0, min(1.0, 1.0 - result.sigma_f_hz / F0_HZ))
        self.assertAlmostEqual(result.psi, expected_psi, places=12)


class TestAutocorrelationCoherence(unittest.TestCase):
    """Tests for autocorrelation_coherence."""

    def test_perfect_tone_unit_coherence(self):
        t = np.linspace(0, 2.0, 4000)
        signal = np.exp(1j * 2.0 * pi * F0_HZ * t)
        psi = autocorrelation_coherence(signal, tau_samples=1)
        self.assertAlmostEqual(psi, 1.0, delta=1e-6)

    def test_pure_noise_lower_coherence(self):
        rng = np.random.default_rng(0)
        noise = rng.normal(0, 1, 4000)
        psi = autocorrelation_coherence(noise, tau_samples=1)
        self.assertLessEqual(psi, 0.1)

    def test_real_valued_signal_valid(self):
        t = np.linspace(0, 1.0, 2000)
        signal = np.cos(2.0 * pi * F0_HZ * t)
        psi = autocorrelation_coherence(signal, tau_samples=1)
        self.assertGreaterEqual(psi, 0.0)
        self.assertLessEqual(psi, 1.0)

    def test_zero_signal_returns_zero(self):
        psi = autocorrelation_coherence(np.zeros(100), tau_samples=1)
        self.assertEqual(psi, 0.0)

    def test_too_short_signal_raises(self):
        with self.assertRaises(ValueError):
            autocorrelation_coherence(np.array([1.0, 2.0]), tau_samples=5)

    def test_invalid_lag_raises(self):
        with self.assertRaises(ValueError):
            autocorrelation_coherence(np.ones(100), tau_samples=0)

    def test_longer_lag_on_pure_tone(self):
        t = np.linspace(0, 2.0, 4000)
        signal = np.exp(1j * 2.0 * pi * F0_HZ * t)
        for lag in [1, 5, 10, 50]:
            psi = autocorrelation_coherence(signal, tau_samples=lag)
            self.assertAlmostEqual(psi, 1.0, delta=1e-5)


class TestCoherenceUncertainty(unittest.TestCase):
    """Tests for coherence_uncertainty (GUM propagation)."""

    def test_known_values(self):
        # σ_f = 0.01 Hz,  u(σ_f) = 0.001 Hz,  f₀ = 141.7001 Hz,  u(f₀) = 0
        result = coherence_uncertainty(sigma_f_hz=0.01, u_sigma_f_hz=0.001, f0_hz=F0_HZ, u_f0_hz=0.0)
        expected_u_psi = 0.001 / F0_HZ
        self.assertAlmostEqual(result.u_psi, expected_u_psi, places=12)
        self.assertIsInstance(result, CoherenceUncertainty)

    def test_f0_uncertainty_contributes(self):
        r_no_f0_unc = coherence_uncertainty(0.05, 0.001, F0_HZ, 0.0)
        r_with_f0_unc = coherence_uncertainty(0.05, 0.001, F0_HZ, 0.01)
        self.assertGreater(r_with_f0_unc.u_psi, r_no_f0_unc.u_psi)

    def test_zero_uncertainties_give_zero_u_psi(self):
        result = coherence_uncertainty(0.05, 0.0, F0_HZ, 0.0)
        self.assertEqual(result.u_psi, 0.0)

    def test_negative_sigma_f_raises(self):
        with self.assertRaises(ValueError):
            coherence_uncertainty(-0.01, 0.001, F0_HZ)

    def test_negative_u_sigma_f_raises(self):
        with self.assertRaises(ValueError):
            coherence_uncertainty(0.01, -0.001, F0_HZ)

    def test_negative_f0_raises(self):
        with self.assertRaises(ValueError):
            coherence_uncertainty(0.01, 0.001, -1.0)

    def test_gum_formula_consistency(self):
        sigma_f = 0.03
        u_sf = 0.002
        u_f0 = 0.0005
        f0 = F0_HZ
        result = coherence_uncertainty(sigma_f, u_sf, f0, u_f0)
        expected = sqrt((u_sf / f0) ** 2 + (sigma_f * u_f0 / f0 ** 2) ** 2)
        self.assertAlmostEqual(result.u_psi, expected, places=15)


class TestPsiThresholdSigmaF(unittest.TestCase):
    """Tests for psi_threshold_sigma_f."""

    def test_psi_total_threshold(self):
        sigma_max = psi_threshold_sigma_f(PSI_TOTAL, F0_HZ)
        # σ_f_max = f₀ × (1 − Ψ) = 141.7001 × 1e-6 ≈ 1.417001e-4 Hz
        expected = F0_HZ * (1.0 - PSI_TOTAL)
        self.assertAlmostEqual(sigma_max, expected, places=12)
        self.assertAlmostEqual(sigma_max, 1.417001e-4, delta=1e-9)

    def test_higher_psi_gives_smaller_sigma_max(self):
        sigma_loose = psi_threshold_sigma_f(0.99, F0_HZ)
        sigma_tight = psi_threshold_sigma_f(0.9999, F0_HZ)
        self.assertGreater(sigma_loose, sigma_tight)

    def test_invalid_psi_raises(self):
        with self.assertRaises(ValueError):
            psi_threshold_sigma_f(0.0, F0_HZ)
        with self.assertRaises(ValueError):
            psi_threshold_sigma_f(1.0, F0_HZ)

    def test_invalid_f0_raises(self):
        with self.assertRaises(ValueError):
            psi_threshold_sigma_f(PSI_TOTAL, 0.0)


class TestIntegrationRegion(unittest.TestCase):
    """Tests for integration_region."""

    def test_adequate_window(self):
        r = integration_region(volume_m3=1e-3, window_s=1.0)
        self.assertTrue(r.window_adequate)
        self.assertAlmostEqual(r.larmor_period_s, 1.0 / F0_HZ, places=10)

    def test_too_short_window_flagged(self):
        short = 0.5 / F0_HZ  # << T_min
        r = integration_region(volume_m3=1e-3, window_s=short)
        self.assertFalse(r.window_adequate)

    def test_boundary_window(self):
        # Exactly at boundary: T = 10 / f₀
        r = integration_region(volume_m3=1e-3, window_s=10.0 / F0_HZ)
        self.assertTrue(r.window_adequate)

    def test_returns_integration_region_type(self):
        r = integration_region(volume_m3=0.001, window_s=1.0)
        self.assertIsInstance(r, IntegrationRegion)

    def test_invalid_volume_raises(self):
        with self.assertRaises(ValueError):
            integration_region(volume_m3=0.0, window_s=1.0)

    def test_invalid_window_raises(self):
        with self.assertRaises(ValueError):
            integration_region(volume_m3=0.001, window_s=0.0)

    def test_large_operational_window(self):
        for t in [1.0, 10.0, 100.0]:
            r = integration_region(volume_m3=1e-2, window_s=t)
            self.assertTrue(r.window_adequate)


if __name__ == "__main__":
    unittest.main()
