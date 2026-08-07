#!/usr/bin/env python3
"""
Tests for noesis_nmr_rectification — Analytic Rectification: NMR Coherence
Ceiling & Algebraic Reframing.

Covers:
  - derive_b0  (CODATA B₀ from Larmor relation)
  - fourier_coherence_bound  (Lorentzian linewidth ceiling on Ψ)
  - psi_ceiling_requires_t2_star  (inverse: T₂* needed for a given Ψ target)
  - algebraic_invariant  (cryptographic/ZK declaration)
"""

import unittest
from math import pi, sqrt

from noesis_nmr_rectification import (
    B0_SHIELDED_UT,
    F0_HZ,
    GAMMA_P_HZ_PER_T,
    GAMMA_P_HZ_PER_UT,
    GAMMA_P_RAD_S_T,
    PSI_TOTAL,
    AlgebraicInvariant,
    B0DerivationResult,
    FourierBound,
    algebraic_invariant,
    derive_b0,
    fourier_coherence_bound,
    psi_ceiling_requires_t2_star,
)


class TestConstants(unittest.TestCase):
    def test_codata_gyromagnetic_ratio(self):
        self.assertAlmostEqual(GAMMA_P_RAD_S_T, 2.6752218744e8, delta=1e0)

    def test_reduced_gamma_consistency(self):
        # γ_p / 2π  [Hz/T]
        expected_hz_per_T = GAMMA_P_RAD_S_T / (2.0 * pi)
        self.assertAlmostEqual(GAMMA_P_HZ_PER_T, expected_hz_per_T, places=2)

    def test_gamma_unit_conversion(self):
        # Hz/µT = Hz/T × 1e-6
        self.assertAlmostEqual(GAMMA_P_HZ_PER_UT, GAMMA_P_HZ_PER_T * 1e-6, places=10)

    def test_b0_shielded_approx_3327_uT(self):
        # B₀ = f₀ / (γ_p/2π) ≈ 3.327 µT
        self.assertAlmostEqual(B0_SHIELDED_UT, 3.327, delta=0.002)

    def test_f0_value(self):
        self.assertAlmostEqual(F0_HZ, 141.7001, places=4)

    def test_psi_total(self):
        self.assertAlmostEqual(PSI_TOTAL, 0.999999, places=6)


class TestDeriveB0(unittest.TestCase):
    """Tests for derive_b0 — CODATA Larmor inversion."""

    def test_b0_approximately_3327_uT(self):
        r = derive_b0()
        self.assertAlmostEqual(r.b0_uT, 3.327, delta=0.002)

    def test_larmor_roundtrip_residual_near_zero(self):
        r = derive_b0()
        # f₀_check = γ_p/2π × B₀ must equal f₀ to floating-point precision
        self.assertAlmostEqual(r.residual_hz, 0.0, places=8)

    def test_larmor_check_matches_f0(self):
        r = derive_b0()
        self.assertAlmostEqual(r.larmor_check_hz, F0_HZ, places=8)

    def test_returns_b0_derivation_result_type(self):
        r = derive_b0()
        self.assertIsInstance(r, B0DerivationResult)

    def test_custom_f0_and_gamma(self):
        # At twice the frequency, B₀ should double
        r_base = derive_b0(f0_hz=100.0, gamma_p_hz_per_uT=GAMMA_P_HZ_PER_UT)
        r_double = derive_b0(f0_hz=200.0, gamma_p_hz_per_uT=GAMMA_P_HZ_PER_UT)
        self.assertAlmostEqual(r_double.b0_uT, 2.0 * r_base.b0_uT, places=10)

    def test_invalid_f0_raises(self):
        with self.assertRaises(ValueError):
            derive_b0(f0_hz=0.0)

    def test_invalid_gamma_raises(self):
        with self.assertRaises(ValueError):
            derive_b0(gamma_p_hz_per_uT=0.0)

    def test_b0_formula(self):
        r = derive_b0()
        expected = F0_HZ / GAMMA_P_HZ_PER_UT
        self.assertAlmostEqual(r.b0_uT, expected, places=12)


class TestFourierCoherenceBound(unittest.TestCase):
    """Tests for fourier_coherence_bound — Lorentzian NMR linewidth ceiling."""

    def test_t2_8p7s_delta_f(self):
        # T₂* = 8.7 s  →  Δf = 1/(π·8.7) ≈ 0.03662 Hz
        r = fourier_coherence_bound(t2_star_s=8.7)
        expected_delta_f = 1.0 / (pi * 8.7)
        self.assertAlmostEqual(r.delta_f_fwhm_hz, expected_delta_f, places=8)

    def test_t2_8p7s_sigma_f(self):
        # σ_f_min = Δf / (2√2) ≈ 0.0129 Hz
        r = fourier_coherence_bound(t2_star_s=8.7)
        expected_sigma = r.delta_f_fwhm_hz / (2.0 * sqrt(2.0))
        self.assertAlmostEqual(r.sigma_f_min_hz, expected_sigma, places=10)
        self.assertAlmostEqual(r.sigma_f_min_hz, 0.0129, delta=0.001)

    def test_t2_8p7s_psi_max_below_threshold(self):
        # With T₂* = 8.7 s, Ψ_max must be below PSI_TOTAL = 0.999999
        r = fourier_coherence_bound(t2_star_s=8.7)
        self.assertFalse(r.psi_threshold_reachable)
        self.assertLess(r.psi_max, PSI_TOTAL)

    def test_t2_15s_sigma_f_approx_0p0075(self):
        # T₂* = 15 s  →  σ_f ≈ 0.0075 Hz
        r = fourier_coherence_bound(t2_star_s=15.0)
        self.assertAlmostEqual(r.sigma_f_min_hz, 0.0075, delta=0.0002)

    def test_t2_15s_psi_max_still_below_threshold(self):
        # Even at T₂* = 15 s, Ψ_max < 0.999999 (physically unreachable)
        r = fourier_coherence_bound(t2_star_s=15.0)
        self.assertFalse(r.psi_threshold_reachable)
        self.assertLess(r.psi_max, PSI_TOTAL)

    def test_longer_t2_gives_higher_psi_max(self):
        r_short = fourier_coherence_bound(t2_star_s=1.0)
        r_long = fourier_coherence_bound(t2_star_s=100.0)
        self.assertGreater(r_long.psi_max, r_short.psi_max)

    def test_psi_max_clamped_to_unit_interval(self):
        for t2 in [0.1, 1.0, 10.0, 1000.0]:
            r = fourier_coherence_bound(t2_star_s=t2)
            self.assertGreaterEqual(r.psi_max, 0.0)
            self.assertLessEqual(r.psi_max, 1.0)

    def test_returns_fourier_bound_type(self):
        r = fourier_coherence_bound(t2_star_s=8.7)
        self.assertIsInstance(r, FourierBound)

    def test_invalid_t2_raises(self):
        with self.assertRaises(ValueError):
            fourier_coherence_bound(t2_star_s=0.0)

    def test_psi_max_formula_consistency(self):
        t2 = 5.0
        r = fourier_coherence_bound(t2_star_s=t2)
        sigma = 1.0 / (pi * t2 * 2.0 * sqrt(2.0))
        expected_psi_max = max(0.0, min(1.0, 1.0 - sigma / F0_HZ))
        self.assertAlmostEqual(r.psi_max, expected_psi_max, places=12)

    def test_psi_999999_requires_enormous_t2(self):
        # Physically: Ψ ≥ 0.999999 via FID is unreachable in practice
        t2_needed = psi_ceiling_requires_t2_star(PSI_TOTAL, F0_HZ)
        r = fourier_coherence_bound(t2_star_s=t2_needed)
        self.assertTrue(r.psi_threshold_reachable)


class TestPsiCeilingRequiresT2Star(unittest.TestCase):
    """Tests for psi_ceiling_requires_t2_star — inverse Fourier bound."""

    def test_psi_total_requires_large_t2(self):
        # T₂*_min = 1 / (2π√2·f₀·(1−Ψ)) for Ψ = 0.999999
        t2_min = psi_ceiling_requires_t2_star(PSI_TOTAL, F0_HZ)
        expected = 1.0 / (2.0 * pi * sqrt(2.0) * F0_HZ * (1.0 - PSI_TOTAL))
        self.assertAlmostEqual(t2_min, expected, places=6)

    def test_higher_psi_requires_longer_t2(self):
        t2_loose = psi_ceiling_requires_t2_star(0.99, F0_HZ)
        t2_tight = psi_ceiling_requires_t2_star(0.9999, F0_HZ)
        self.assertGreater(t2_tight, t2_loose)

    def test_roundtrip_t2_psi(self):
        psi_target = 0.9999
        t2_min = psi_ceiling_requires_t2_star(psi_target, F0_HZ)
        r = fourier_coherence_bound(t2_star_s=t2_min)
        # At exactly T₂*_min, Ψ_max should be at or above psi_target
        self.assertGreaterEqual(r.psi_max, psi_target - 1e-9)

    def test_invalid_psi_target_raises(self):
        with self.assertRaises(ValueError):
            psi_ceiling_requires_t2_star(0.0, F0_HZ)
        with self.assertRaises(ValueError):
            psi_ceiling_requires_t2_star(1.0, F0_HZ)

    def test_invalid_f0_raises(self):
        with self.assertRaises(ValueError):
            psi_ceiling_requires_t2_star(PSI_TOTAL, 0.0)

    def test_result_positive(self):
        t2 = psi_ceiling_requires_t2_star(0.99, F0_HZ)
        self.assertGreater(t2, 0.0)


class TestAlgebraicInvariant(unittest.TestCase):
    """Tests for algebraic_invariant — ZK/Lean 4 cryptographic reframing."""

    def test_default_values(self):
        inv = algebraic_invariant()
        self.assertAlmostEqual(inv.f0_hz, F0_HZ, places=4)
        self.assertAlmostEqual(inv.psi, PSI_TOTAL, places=6)

    def test_not_empirical(self):
        # The invariant must declare it carries no empirical water-structure claim
        inv = algebraic_invariant()
        self.assertFalse(inv.is_empirical)

    def test_circuit_and_prover_set(self):
        inv = algebraic_invariant()
        self.assertIn("Groth16", inv.circuit_system)
        self.assertIn("Lean", inv.prover_system)

    def test_returns_algebraic_invariant_type(self):
        inv = algebraic_invariant()
        self.assertIsInstance(inv, AlgebraicInvariant)

    def test_custom_circuit_system(self):
        inv = algebraic_invariant(circuit_system="PLONK/UltraPlonk")
        self.assertEqual(inv.circuit_system, "PLONK/UltraPlonk")
        self.assertFalse(inv.is_empirical)

    def test_invalid_f0_raises(self):
        with self.assertRaises(ValueError):
            algebraic_invariant(f0_hz=-1.0)

    def test_invalid_psi_raises(self):
        with self.assertRaises(ValueError):
            algebraic_invariant(psi=0.0)
        with self.assertRaises(ValueError):
            algebraic_invariant(psi=1.1)

    def test_f0_and_psi_are_exact_invariants(self):
        # Both values must match the module-level constants exactly
        inv = algebraic_invariant()
        self.assertEqual(inv.f0_hz, F0_HZ)
        self.assertEqual(inv.psi, PSI_TOTAL)


if __name__ == "__main__":
    unittest.main()
