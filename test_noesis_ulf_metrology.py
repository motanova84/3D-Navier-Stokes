#!/usr/bin/env python3
"""Tests for NOESIS ULF metrology formalization."""

import unittest

import numpy as np

from noesis_ulf_metrology import (
    TARGET_FREQUENCY_HZ,
    DEUTERIUM_GAMMA_HZ_PER_UT,
    PROTON_GAMMA_HZ_PER_UT,
    MeasurementResult,
    UncertaintySource,
    acceptance_interval_hz,
    coherence_envelope,
    coherence_from_bandpower,
    combine_uncertainty,
    default_noesis_uncertainty_sources,
    evaluate_protocol,
    fid_signal,
    larmor_frequency_hz,
)


class TestNoesisUlfMetrology(unittest.TestCase):
    def test_larmor_frequency_proton_and_deuterium(self):
        b0_uT = 3.3281
        f_proton = larmor_frequency_hz(b0_uT)
        f_deuterium = larmor_frequency_hz(b0_uT, DEUTERIUM_GAMMA_HZ_PER_UT)

        self.assertAlmostEqual(f_proton, PROTON_GAMMA_HZ_PER_UT * b0_uT, places=9)
        self.assertAlmostEqual(f_deuterium, DEUTERIUM_GAMMA_HZ_PER_UT * b0_uT, places=9)
        self.assertAlmostEqual(f_deuterium, 21.7521, delta=0.002)
        self.assertGreater(f_proton, f_deuterium)

    def test_coherence_envelope_bounds(self):
        t = np.linspace(0.0, 2.0, 200)
        psi = coherence_envelope(t, tau_coherence_s=0.5, psi_inf=0.999999)

        self.assertAlmostEqual(psi[0], 0.0, places=12)
        self.assertTrue(np.all(psi >= 0.0))
        self.assertTrue(np.all(psi <= 0.999999))
        self.assertTrue(np.all(np.diff(psi) >= -1e-12))
        mid_idx = np.argmin(np.abs(t - 0.5))
        expected_mid = 0.999999 * (1.0 - np.exp(-(t[mid_idx] / 0.5)))
        self.assertAlmostEqual(psi[mid_idx], expected_mid, places=4)
        self.assertGreater(psi[-1], 0.98)

    def test_fid_signal_shape_and_decay(self):
        t = np.linspace(0.0, 1.0, 1000)
        s = fid_signal(
            times_s=t,
            f0_hz=TARGET_FREQUENCY_HZ,
            amplitude=1.0,
            t2_star_s=0.2,
            tau_coherence_s=0.05,
            interference_components=[(0.1, 50.0, 0.0)],
        )

        self.assertEqual(len(s), len(t))
        self.assertFalse(np.isnan(s).any())
        # Decay envelope should suppress late-time RMS
        early_rms = np.sqrt(np.mean(s[:200] ** 2))
        late_rms = np.sqrt(np.mean(s[-200:] ** 2))
        self.assertGreater(early_rms, late_rms)

    def test_uncertainty_budget_matches_reference_scale(self):
        budget = combine_uncertainty(default_noesis_uncertainty_sources(), coverage_factor=2.0)

        self.assertAlmostEqual(budget.combined_standard_uncertainty, 3.518e-4, delta=2.0e-6)
        self.assertAlmostEqual(budget.expanded_uncertainty, 7.036e-4, delta=4.0e-6)
        self.assertIn("B0_stability", budget.contributions)

    def test_uncertainty_with_covariance(self):
        sources = [
            UncertaintySource("a", 1.0, 2.0),
            UncertaintySource("b", 1.0, 3.0),
        ]
        uncorr = combine_uncertainty(sources)
        corr = combine_uncertainty(sources, covariances={("a", "b"): 0.25})
        corr_duplicate = combine_uncertainty(sources, covariances={("a", "b"): 0.25, ("b", "a"): 0.25})

        self.assertGreater(corr.combined_standard_uncertainty, uncorr.combined_standard_uncertainty)
        self.assertAlmostEqual(
            corr.combined_standard_uncertainty,
            corr_duplicate.combined_standard_uncertainty,
            places=12,
        )

    def test_uncertainty_self_covariance_rejected(self):
        sources = [UncertaintySource("a", 1.0, 2.0)]
        with self.assertRaises(ValueError):
            combine_uncertainty(sources, covariances={("a", "a"): 0.1})

    def test_acceptance_interval(self):
        lo, hi = acceptance_interval_hz(TARGET_FREQUENCY_HZ, expanded_uncertainty_hz=7.036e-4)
        self.assertAlmostEqual(lo, 141.6993964, places=7)
        self.assertAlmostEqual(hi, 141.7008036, places=7)

    def test_coherence_from_bandpower(self):
        freqs = np.linspace(0, 300, 6001)
        power = np.ones_like(freqs) * 0.01
        # Inject narrow strong peak around target
        power += np.exp(-0.5 * ((freqs - TARGET_FREQUENCY_HZ) / 0.05) ** 2)

        psi = coherence_from_bandpower(
            frequencies_hz=freqs,
            power_spectrum=power,
            target_frequency_hz=TARGET_FREQUENCY_HZ,
            delta_f_hz=0.2,
            noise_floor_power=0.0,
        )

        self.assertGreater(psi, 0.02)
        self.assertLessEqual(psi, 1.0)

    def test_protocol_evaluation_pass(self):
        uncertainty = combine_uncertainty(default_noesis_uncertainty_sources(), coverage_factor=2.0)
        result = MeasurementResult(
            measured_frequency_hz=TARGET_FREQUENCY_HZ,
            coherence=0.999999,
            von_neumann_entropy=0.005,
            controls={"blank": True, "d2o": True, "off_resonance": True},
        )

        decision = evaluate_protocol(result, uncertainty)

        self.assertTrue(decision.accepted)
        self.assertTrue(decision.within_frequency_interval)
        self.assertTrue(decision.controls_passed)

    def test_protocol_evaluation_fail(self):
        uncertainty = combine_uncertainty(default_noesis_uncertainty_sources(), coverage_factor=2.0)
        result = MeasurementResult(
            measured_frequency_hz=TARGET_FREQUENCY_HZ + 0.01,
            coherence=0.95,
            von_neumann_entropy=0.02,
            controls={"blank": True, "d2o": False, "off_resonance": True},
        )

        decision = evaluate_protocol(result, uncertainty)

        self.assertFalse(decision.accepted)
        self.assertFalse(decision.within_frequency_interval)
        self.assertFalse(decision.controls_passed)
        self.assertFalse(decision.coherence_passed)
        self.assertFalse(decision.entropy_passed)


if __name__ == "__main__":
    unittest.main()
