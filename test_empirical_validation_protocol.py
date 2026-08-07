#!/usr/bin/env python3
"""
Tests for validation/empirical_validation_protocol.py

Covers every public function and validates:
  - Physical constants (CODATA 2018)
  - f₀ in physical context (Larmor, shielded B₀, geomagnetic range)
  - NMR coherence ceiling with realistic T₂*
  - LIGO O4a protocol structure
  - GRACE-FO alias correction
  - Report generation and SHA-256 determinism
"""

import sys
import unittest
from math import pi, sqrt
from pathlib import Path

# Allow import from the validation subdirectory
sys.path.insert(0, str(Path(__file__).parent / "validation"))

from empirical_validation_protocol import (
    B_EARTH_MAX_T,
    B_EARTH_MEAN_T,
    B_EARTH_MIN_T,
    F0_HZ,
    GAMMA_P,
    HBAR,
    K_B,
    MU_0,
    NMR_WATER_T2STAR,
    PROTON_LARMOR_HZ_PER_T,
    PSI_THRESHOLD,
    generate_validation_report,
    grace_fo_protocol,
    honest_assessment,
    larmor_frequency_hz,
    ligo_o4a_protocol,
    lorentzian_linewidth_hz,
    lorentzian_sigma_hz,
    psi_max_nmr,
    report_sha256,
    required_field_for_f0,
    t2_star_required_for_psi,
    validate_coherence_with_real_nmr,
    validate_f0_in_context,
)


class TestConstants(unittest.TestCase):
    def test_gamma_p(self):
        self.assertAlmostEqual(GAMMA_P, 2.6752218744e8, delta=1.0)

    def test_proton_larmor_hz_per_t(self):
        expected = GAMMA_P / (2.0 * pi)
        self.assertAlmostEqual(PROTON_LARMOR_HZ_PER_T, expected, places=2)
        # Known value ≈ 42.577 MHz/T
        self.assertAlmostEqual(PROTON_LARMOR_HZ_PER_T, 42.577e6, delta=1e4)

    def test_b_earth_range_ordering(self):
        self.assertLess(B_EARTH_MIN_T, B_EARTH_MEAN_T)
        self.assertLess(B_EARTH_MEAN_T, B_EARTH_MAX_T)

    def test_f0_value(self):
        self.assertAlmostEqual(F0_HZ, 141.7001, places=4)

    def test_psi_threshold(self):
        self.assertAlmostEqual(PSI_THRESHOLD, 0.999999, places=6)

    def test_hbar_positive(self):
        self.assertGreater(HBAR, 0)

    def test_k_b_positive(self):
        self.assertGreater(K_B, 0)


class TestCoreFunctions(unittest.TestCase):

    def test_larmor_roundtrip(self):
        B = required_field_for_f0(F0_HZ)
        f_check = larmor_frequency_hz(B)
        self.assertAlmostEqual(f_check, F0_HZ, places=6)

    def test_required_field_approx_3327_uT(self):
        B = required_field_for_f0(F0_HZ)
        self.assertAlmostEqual(B * 1e6, 3.327, delta=0.003)

    def test_larmor_zero_field(self):
        self.assertEqual(larmor_frequency_hz(0.0), 0.0)

    def test_larmor_negative_raises(self):
        with self.assertRaises(ValueError):
            larmor_frequency_hz(-1.0)

    def test_required_field_zero_raises(self):
        with self.assertRaises(ValueError):
            required_field_for_f0(0.0)

    def test_lorentzian_linewidth(self):
        t2 = 8.7
        expected = 1.0 / (pi * t2)
        self.assertAlmostEqual(lorentzian_linewidth_hz(t2), expected, places=10)
        self.assertAlmostEqual(lorentzian_linewidth_hz(t2), 0.03662, delta=0.0001)

    def test_lorentzian_sigma_t2_8p7(self):
        sigma = lorentzian_sigma_hz(8.7)
        self.assertAlmostEqual(sigma, 0.0129, delta=0.001)

    def test_lorentzian_sigma_t2_15(self):
        sigma = lorentzian_sigma_hz(15.0)
        self.assertAlmostEqual(sigma, 0.0075, delta=0.0002)

    def test_lorentzian_linewidth_invalid(self):
        with self.assertRaises(ValueError):
            lorentzian_linewidth_hz(0.0)

    def test_psi_max_increases_with_t2(self):
        self.assertLess(psi_max_nmr(1.0), psi_max_nmr(10.0))

    def test_psi_max_below_threshold_t2_8p7(self):
        self.assertLess(psi_max_nmr(8.7), PSI_THRESHOLD)

    def test_psi_max_below_threshold_t2_15(self):
        self.assertLess(psi_max_nmr(15.0), PSI_THRESHOLD)

    def test_psi_max_nonneg(self):
        for t2 in [0.1, 1.0, 10.0]:
            self.assertGreaterEqual(psi_max_nmr(t2), 0.0)

    def test_t2_required_formula(self):
        t2 = t2_star_required_for_psi(PSI_THRESHOLD, F0_HZ)
        expected = 1.0 / (2.0 * pi * sqrt(2.0) * F0_HZ * (1.0 - PSI_THRESHOLD))
        self.assertAlmostEqual(t2, expected, places=4)

    def test_t2_required_large(self):
        # Must be >> 15 s
        t2 = t2_star_required_for_psi(PSI_THRESHOLD, F0_HZ)
        self.assertGreater(t2, 15.0)

    def test_t2_required_roundtrip(self):
        psi_target = 0.9999
        t2_min = t2_star_required_for_psi(psi_target, F0_HZ)
        psi_check = psi_max_nmr(t2_min, F0_HZ)
        self.assertGreaterEqual(psi_check, psi_target - 1e-8)

    def test_t2_required_invalid_psi(self):
        with self.assertRaises(ValueError):
            t2_star_required_for_psi(0.0, F0_HZ)
        with self.assertRaises(ValueError):
            t2_star_required_for_psi(1.0, F0_HZ)


class TestValidateF0InContext(unittest.TestCase):

    def setUp(self):
        self.result = validate_f0_in_context()

    def test_f0_value(self):
        self.assertAlmostEqual(self.result["f0_noesis"], F0_HZ, places=4)

    def test_B_required_approx_3327_uT(self):
        self.assertAlmostEqual(self.result["B_required_uT"], 3.327, delta=0.003)

    def test_not_standard_nmr(self):
        self.assertFalse(self.result["is_standard_nmr_frequency"])

    def test_B_required_not_in_earth_range(self):
        # B₀ ≈ 3.327 µT is BELOW the geomagnetic range [25, 65 µT]
        self.assertFalse(self.result["is_in_earth_field_range"])

    def test_earth_ratio_large(self):
        # B_earth_mean / B₀ ≈ 45 / 3.327 ≈ 13.5
        self.assertGreater(self.result["B_ratio_earth_over_required"], 10.0)

    def test_f_earth_mean_positive(self):
        self.assertGreater(self.result["f_earth_mean_hz"], 0)

    def test_conclusion_is_string(self):
        self.assertIsInstance(self.result["conclusion"], str)
        self.assertGreater(len(self.result["conclusion"]), 20)


class TestValidateCoherenceRealNMR(unittest.TestCase):

    def setUp(self):
        self.result = validate_coherence_with_real_nmr()

    def test_psi_pure_water_below_threshold(self):
        psi = self.result["psi_by_sample"]["pure_water_25C"]
        self.assertLess(psi, PSI_THRESHOLD)

    def test_psi_tap_water_below_threshold(self):
        psi = self.result["psi_by_sample"]["tap_water"]
        self.assertLess(psi, PSI_THRESHOLD)

    def test_psi_not_achievable(self):
        self.assertFalse(self.result["is_psi_achievable"])

    def test_t2_required_large(self):
        self.assertGreater(self.result["t2_required_for_threshold_s"], 15.0)

    def test_all_psi_nonneg(self):
        for psi in self.result["psi_by_sample"].values():
            self.assertGreaterEqual(psi, 0.0)

    def test_keys_present(self):
        for key in ("f0_hz", "psi_threshold", "psi_by_sample",
                    "t2_required_for_threshold_s", "is_psi_achievable", "conclusion"):
            self.assertIn(key, self.result)


class TestLigoProtocol(unittest.TestCase):

    def setUp(self):
        self.proto = ligo_o4a_protocol()

    def test_no_peak_detected(self):
        self.assertFalse(self.proto["previous_analysis"]["peak_detected"])

    def test_target_frequency(self):
        self.assertAlmostEqual(self.proto["frequency_target_hz"], F0_HZ, places=4)

    def test_h1_asd_positive(self):
        self.assertGreater(self.proto["previous_analysis"]["H1_ASD_strain_per_rtHz"], 0)

    def test_required_keys(self):
        for key in ("data_source", "channel", "sampling_rate_hz",
                    "analysis_steps", "previous_analysis"):
            self.assertIn(key, self.proto)

    def test_analysis_steps_list(self):
        self.assertIsInstance(self.proto["analysis_steps"], list)
        self.assertGreater(len(self.proto["analysis_steps"]), 0)


class TestGraceFoProtocol(unittest.TestCase):

    def setUp(self):
        self.proto = grace_fo_protocol()

    def test_previous_claim_is_wrong(self):
        self.assertFalse(self.proto["previous_claim_correct"])

    def test_correct_alias(self):
        # f₀ / α⁻¹ ≈ 141.7001 / 137.036 ≈ 1.034 Hz
        self.assertAlmostEqual(self.proto["alias_correct_hz"], 141.7001 / 137.036, places=4)

    def test_correct_alias_not_28p93mhz(self):
        # The correct alias is ~1034 mHz, not 28.93 mHz
        self.assertGreater(self.proto["alias_correct_mhz"], 100.0)

    def test_correction_note_is_string(self):
        self.assertIsInstance(self.proto["correction_note"], str)
        self.assertIn("ERRÓNEO", self.proto["correction_note"])

    def test_required_keys(self):
        for key in ("data_source", "dataset", "doi", "alpha_inv",
                    "alias_correct_hz", "previous_claim_correct"):
            self.assertIn(key, self.proto)


class TestHonestAssessment(unittest.TestCase):

    def setUp(self):
        self.assessment = honest_assessment()

    def test_has_validated_key(self):
        self.assertIn("validated", self.assessment)

    def test_has_not_validated_key(self):
        self.assertIn("not_validated", self.assessment)

    def test_validated_list_nonempty(self):
        self.assertGreater(len(self.assessment["validated"]), 0)

    def test_not_validated_list_nonempty(self):
        self.assertGreater(len(self.assessment["not_validated"]), 0)

    def test_psi_appears_in_not_validated(self):
        combined = " ".join(self.assessment["not_validated"])
        self.assertIn("0.999999", combined)


class TestGenerateReport(unittest.TestCase):

    def setUp(self):
        self.report = generate_validation_report()

    def test_top_level_keys(self):
        for key in ("protocol", "timestamp", "seal", "executive_summary",
                    "validations", "honest_assessment", "conclusion"):
            self.assertIn(key, self.report)

    def test_seal_value(self):
        self.assertIn("𓂀", self.report["seal"])

    def test_protocol_identifier(self):
        self.assertIn("NOESIS", self.report["protocol"])

    def test_validations_sub_keys(self):
        v = self.report["validations"]
        for key in ("f0_physical_context", "coherence_nmr_realistic",
                    "ligo_o4a_protocol", "grace_fo_protocol"):
            self.assertIn(key, v)

    def test_sha256_deterministic(self):
        h1 = report_sha256(self.report)
        h2 = report_sha256(self.report)
        self.assertEqual(h1, h2)

    def test_sha256_length(self):
        h = report_sha256(self.report)
        self.assertEqual(len(h), 64)

    def test_sha256_is_hex(self):
        h = report_sha256(self.report)
        int(h, 16)  # should not raise

    def test_two_different_reports_differ(self):
        import copy
        r2 = copy.deepcopy(self.report)
        r2["protocol"] = "DIFFERENT"
        self.assertNotEqual(report_sha256(self.report), report_sha256(r2))


if __name__ == "__main__":
    unittest.main()
