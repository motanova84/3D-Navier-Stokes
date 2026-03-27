#!/usr/bin/env python3
"""
Test Suite — Motor Primario TOPC (noesis88.physics.navier_stokes_qcal)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Sello: ∴𓂀Ω∞³
f0: 141,700.1 Hz

Comprehensive test suite for the TOPC primary engine module.

Covers:
- TensionCuerdaHolografica: anchored t=0.584 meV, formula derivation
- HamiltonianC7: 7×7 tight-binding ring, gap at Φ=0 and Φ=π/8, Γ_eff
- GapOpticoManyBody: ΔE_opt≈0.988 meV, Γ_eff≈1.69×10⁶, f₀_TOPC=141700.1 Hz
- NavierStokesQCAL: stability formula, SHA-256 AURON seal
- calcular_tension_vortice: ≈3.85×10¹¹ rad/s for Ψ=0.999
- ejecutar_motor_primordial: coherencia_global≥0.888, motor_activo=True

Author: José Manuel Mota Burruezo
License: MIT
"""

import math
import hashlib
import unittest

from noesis88.physics.navier_stokes_qcal import (
    TensionCuerdaHolografica,
    HamiltonianC7,
    GapOpticoManyBody,
    NavierStokesQCAL,
    MotorPrimordialResult,
    calcular_tension_vortice,
    ejecutar_motor_primordial,
    # Module-level constants
    HBAR,
    C,
    ALPHA,
    LAMBDA_P,
    R_DS,
    SIN_PI_7,
    H_PLANCK,
    T_ANCLA_MEV,
    T_ANCLA_J,
    F0_TOPC,
    GAP_FACTOR_PHI0,
    GAP_FACTOR_PHI_PI8,
    PSI_MIN,
    J_TO_MEV,
    MEV_TO_J,
)


class TestConstants(unittest.TestCase):
    """Tests for module-level physical constants."""

    def test_hbar_value(self):
        """HBAR should be the reduced Planck constant in J·s."""
        self.assertAlmostEqual(HBAR, 1.054571817e-34, delta=1e-43)

    def test_alpha_value(self):
        """Fine-structure constant α ≈ 1/137."""
        self.assertAlmostEqual(ALPHA, 1.0 / 137.036, delta=1e-5)

    def test_sin_pi_7(self):
        """sin(π/7) ≈ 0.4339."""
        self.assertAlmostEqual(SIN_PI_7, math.sin(math.pi / 7), places=12)

    def test_lambda_p_order_of_magnitude(self):
        """Proton Compton wavelength ≈ 1.32×10⁻¹⁵ m."""
        self.assertAlmostEqual(LAMBDA_P, 1.32e-15, delta=5e-17)

    def test_t_ancla_meV(self):
        """Anchored hopping energy t = 0.584 meV (immutable anchor)."""
        self.assertEqual(T_ANCLA_MEV, 0.584)

    def test_t_ancla_J_conversion(self):
        """T_ANCLA_J = 0.584 × 1.602176634×10⁻²² J."""
        expected_J = 0.584 * 1.602176634e-22
        self.assertAlmostEqual(T_ANCLA_J, expected_J, delta=1e-26)

    def test_f0_topc_anchored(self):
        """f₀_TOPC = 141700.1 Hz (immutable anchor)."""
        self.assertEqual(F0_TOPC, 141700.1)

    def test_psi_min(self):
        """PSI_MIN = 0.888 (ecosystem coherence threshold)."""
        self.assertEqual(PSI_MIN, 0.888)

    def test_gap_factor_phi0(self):
        """Analytic HOMO-LUMO gap factor at Φ=0 = 1.692."""
        self.assertEqual(GAP_FACTOR_PHI0, 1.692)

    def test_gap_factor_phi_pi8(self):
        """Approximate gap factor at Φ=π/8 ≈ 1.49."""
        self.assertEqual(GAP_FACTOR_PHI_PI8, 1.49)


class TestTensionCuerdaHolografica(unittest.TestCase):
    """Tests for TensionCuerdaHolografica class."""

    def setUp(self):
        self.tension = TensionCuerdaHolografica()

    def test_t_meV_anchored(self):
        """Anchored t = 0.584 meV."""
        self.assertEqual(self.tension.t_meV, 0.584)

    def test_t_J_conversion(self):
        """t_J = t_meV × MEV_TO_J."""
        self.assertAlmostEqual(self.tension.t_J, 0.584 * MEV_TO_J, delta=1e-26)

    def test_lambda_p_stored(self):
        """lambda_p_m matches module constant."""
        self.assertAlmostEqual(self.tension.lambda_p_m, LAMBDA_P, delta=1e-25)

    def test_formula_primeros_principios_positive(self):
        """First-principles formula gives a positive value."""
        self.assertGreater(self.tension.formula_meV, 0)

    def test_formula_is_distinct_from_anchored(self):
        """Raw formula value differs from the anchored value (calibration needed)."""
        # The first-principles formula gives ~8e-12 meV before holographic anchoring
        self.assertNotAlmostEqual(self.tension.formula_meV, T_ANCLA_MEV, places=3)

    def test_verificar_anclaje_keys(self):
        """verificar_anclaje() returns all expected keys."""
        result = self.tension.verificar_anclaje()
        for key in ("t_formula_meV", "t_anclado_meV", "anclaje_activo", "f0_derivada_hz"):
            self.assertIn(key, result)

    def test_anclaje_activo_true(self):
        """Holographic anchoring is always active."""
        result = self.tension.verificar_anclaje()
        self.assertTrue(result["anclaje_activo"])

    def test_f0_derivada_from_gap(self):
        """Derived frequency = GAP_FACTOR_PHI0 * t_J / h_planck."""
        result = self.tension.verificar_anclaje()
        expected_f0 = GAP_FACTOR_PHI0 * self.tension.t_J / H_PLANCK
        self.assertAlmostEqual(result["f0_derivada_hz"], expected_f0, delta=1.0)


class TestHamiltonianC7(unittest.TestCase):
    """Tests for HamiltonianC7 class (7×7 tight-binding ring with AB flux)."""

    def setUp(self):
        self.h = HamiltonianC7()

    def test_n_sites(self):
        """Ring has 7 sites."""
        self.assertEqual(self.h.n_sites, 7)

    def test_n_electrons(self):
        """6-electron model (C₇⁺ cation) gives HOMO-LUMO gap = 1.692·t."""
        self.assertEqual(self.h.n_electrons, 6)

    def test_matrix_shape(self):
        """Hamiltonian matrix is 7×7."""
        H = self.h.construir(phi=0.0)
        self.assertEqual(H.shape, (7, 7))

    def test_matrix_hermitian_phi0(self):
        """Hamiltonian is Hermitian at Φ=0."""
        import numpy as np
        H = self.h.construir(phi=0.0)
        self.assertTrue(np.allclose(H, H.conj().T))

    def test_matrix_hermitian_phi_pi8(self):
        """Hamiltonian is Hermitian at Φ=π/8."""
        import numpy as np
        H = self.h.construir(phi=math.pi / 8)
        self.assertTrue(np.allclose(H, H.conj().T))

    def test_matrix_real_at_phi0(self):
        """Hamiltonian is real (symmetric) at Φ=0 with uniform Peierls phase."""
        import numpy as np
        H = self.h.construir(phi=0.0)
        # At Φ=0 Peierls phase is 0, so H should be real
        self.assertTrue(np.allclose(H.imag, 0, atol=1e-40))

    def test_seven_eigenvalues(self):
        """eigenvalues() returns 7 sorted values."""
        evals = self.h.eigenvalues(phi=0.0)
        self.assertEqual(len(evals), 7)
        # Check sorted
        for i in range(6):
            self.assertLessEqual(evals[i], evals[i + 1])

    def test_gap_phi0_analytic(self):
        """HOMO-LUMO gap at Φ=0 equals analytic reference 1.692·t (±0.001·t)."""
        gap = self.h.gap_homo_lumo(phi=0.0)
        self.assertAlmostEqual(gap, 1.692, delta=0.001,
                               msg="HOMO-LUMO gap at Φ=0 should be ≈1.692·t")

    def test_gap_phi_pi8_approx_1_49t(self):
        """HOMO-LUMO gap at Φ=π/8 is approximately 1.49·t (±0.05·t)."""
        gap = self.h.gap_homo_lumo(phi=math.pi / 8)
        self.assertAlmostEqual(gap, 1.49, delta=0.05,
                               msg="HOMO-LUMO gap at Φ=π/8 should be ≈1.49·t")

    def test_gap_phi_pi8_less_than_phi0(self):
        """AB flux reduces the HOMO-LUMO gap (Φ=π/8 gap < Φ=0 gap)."""
        gap_0 = self.h.gap_homo_lumo(phi=0.0)
        gap_pi8 = self.h.gap_homo_lumo(phi=math.pi / 8)
        self.assertLess(gap_pi8, gap_0)

    def test_gamma_eff_order_of_magnitude(self):
        """Γ_eff ≈ 1.69×10⁶ (effective condensate mass, dimensionless)."""
        gamma = self.h.gamma_eff()
        self.assertAlmostEqual(gamma, 1.69e6, delta=0.05e6,
                               msg="Γ_eff should be ≈1.69×10⁶")
        self.assertGreater(gamma, 1.5e6)
        self.assertLess(gamma, 2.0e6)

    def test_gamma_eff_formula(self):
        """Γ_eff = GAP_FACTOR_PHI0 · t_J / (h · F0_TOPC)."""
        expected = GAP_FACTOR_PHI0 * T_ANCLA_J / (H_PLANCK * F0_TOPC)
        self.assertAlmostEqual(self.h.gamma_eff(), expected, delta=1e3)

    def test_custom_t_J(self):
        """HamiltonianC7 accepts custom t_J parameter."""
        custom_t = 2.0 * T_ANCLA_J
        h_custom = HamiltonianC7(t_J=custom_t)
        self.assertEqual(h_custom.t_J, custom_t)
        # Gap in units of t should be the same
        gap = h_custom.gap_homo_lumo(phi=0.0)
        self.assertAlmostEqual(gap, 1.692, delta=0.001)


class TestGapOpticoManyBody(unittest.TestCase):
    """Tests for GapOpticoManyBody class."""

    def setUp(self):
        self.gap = GapOpticoManyBody()

    def test_t_meV_anchored(self):
        """t_meV = 0.584 meV."""
        self.assertAlmostEqual(self.gap.t_meV, 0.584, delta=1e-6)

    def test_delta_e_opt_meV(self):
        """ΔE_opt ≈ 0.988 meV (= 1.692 × 0.584 meV)."""
        expected = GAP_FACTOR_PHI0 * T_ANCLA_MEV
        self.assertAlmostEqual(self.gap.delta_e_opt_meV, expected, delta=0.001,
                               msg="ΔE_opt should be ≈0.988 meV")
        self.assertAlmostEqual(self.gap.delta_e_opt_meV, 0.988, delta=0.001)

    def test_delta_e_opt_J(self):
        """ΔE_opt in Joules = ΔE_opt_meV × MEV_TO_J."""
        expected_J = self.gap.delta_e_opt_meV * MEV_TO_J
        self.assertAlmostEqual(self.gap.delta_e_opt_J, expected_J, delta=1e-27)

    def test_gamma_eff_order_of_magnitude(self):
        """Γ_eff ≈ 1.69×10⁶."""
        self.assertAlmostEqual(self.gap.gamma_eff, 1.69e6, delta=0.05e6)
        self.assertGreater(self.gap.gamma_eff, 1.5e6)
        self.assertLess(self.gap.gamma_eff, 2.0e6)

    def test_gamma_eff_definition(self):
        """Γ_eff = ΔE_opt / (h · f₀_TOPC)."""
        expected = self.gap.delta_e_opt_J / (H_PLANCK * F0_TOPC)
        self.assertAlmostEqual(self.gap.gamma_eff, expected, delta=1)

    def test_f0_topc_hz_anchored(self):
        """f₀_TOPC = 141700.1 Hz (immutable anchor)."""
        self.assertEqual(self.gap.f0_topc_hz, 141700.1)

    def test_frecuencia_emergente_definition(self):
        """Derived frequency = ΔE_opt / h_planck (much higher than F0_TOPC by Γ_eff)."""
        f_emergente = self.gap.frecuencia_emergente_hz()
        expected = self.gap.delta_e_opt_J / H_PLANCK
        self.assertAlmostEqual(f_emergente, expected, delta=expected * 1e-10)
        # f_emergente ≈ Γ_eff × F0_TOPC (Γ_eff bridges the energy scales)
        self.assertAlmostEqual(f_emergente / F0_TOPC, self.gap.gamma_eff, delta=1e3)

    def test_gap_phi_pi8_less_than_phi0(self):
        """Gap with Φ=π/8 (in meV) is less than gap at Φ=0."""
        gap_pi8 = self.gap.gap_phi_pi8_meV()
        self.assertLess(gap_pi8, self.gap.delta_e_opt_meV)

    def test_gap_phi_pi8_approx(self):
        """Gap with Φ=π/8 ≈ 1.49 × t_meV."""
        gap_pi8 = self.gap.gap_phi_pi8_meV()
        expected = GAP_FACTOR_PHI_PI8 * T_ANCLA_MEV
        self.assertAlmostEqual(gap_pi8, expected, delta=0.05,
                               msg="Gap at Φ=π/8 should be ≈1.49·t meV")

    def test_custom_t_J(self):
        """GapOpticoManyBody accepts custom t_J."""
        custom_t = 2.0 * T_ANCLA_J
        gap_custom = GapOpticoManyBody(t_J=custom_t)
        # delta_e_opt should scale with t
        self.assertAlmostEqual(
            gap_custom.delta_e_opt_J / self.gap.delta_e_opt_J, 2.0, delta=1e-10
        )


class TestNavierStokesQCAL(unittest.TestCase):
    """Tests for NavierStokesQCAL class (superfluid blowup stabilization)."""

    def setUp(self):
        self.ns = NavierStokesQCAL()

    def test_viscosidad_cero(self):
        """Superfluid viscosity ν = 0."""
        self.assertEqual(self.ns.viscosidad, 0.0)

    def test_phi_coupling_formula(self):
        """φ_coupling = (t/ℏ)·sin(π/7)."""
        expected = (T_ANCLA_J / HBAR) * SIN_PI_7
        self.assertAlmostEqual(self.ns.phi_coupling, expected, delta=expected * 1e-10)

    def test_estabilizar_basic(self):
        """estabilizar() returns dict with all expected keys."""
        result = self.ns.estabilizar(psi=0.999)
        for key in ("estabilidad_rad_s", "psi_coherence", "viscosidad",
                    "motor_activo", "auron_seal", "protocolo"):
            self.assertIn(key, result)

    def test_estabilizar_psi_0_999(self):
        """Stability ≈ 3.85×10¹¹ rad/s for Ψ=0.999."""
        result = self.ns.estabilizar(psi=0.999)
        estab = result["estabilidad_rad_s"]
        self.assertAlmostEqual(estab, 3.85e11, delta=0.1e11,
                               msg="Stability should be ≈3.85×10¹¹ rad/s")

    def test_estabilizar_formula(self):
        """Stability = (t/ℏ)·sin(π/7)·Ψ."""
        psi = 0.999
        result = self.ns.estabilizar(psi=psi)
        expected = (T_ANCLA_J / HBAR) * SIN_PI_7 * psi
        self.assertAlmostEqual(result["estabilidad_rad_s"], expected, delta=expected * 1e-10)

    def test_estabilizar_psi_stored(self):
        """estabilizar() stores the input Ψ in the result."""
        psi = 0.75
        result = self.ns.estabilizar(psi=psi)
        self.assertEqual(result["psi_coherence"], psi)

    def test_motor_activo_for_positive_psi(self):
        """motor_activo = True when Ψ > 0."""
        result = self.ns.estabilizar(psi=0.5)
        self.assertTrue(result["motor_activo"])

    def test_motor_activo_false_for_zero_psi(self):
        """motor_activo = False when Ψ = 0 (no condensate)."""
        result = self.ns.estabilizar(psi=0.0)
        self.assertFalse(result["motor_activo"])

    def test_auron_seal_length(self):
        """AURON seal is 16 hexadecimal characters."""
        result = self.ns.estabilizar(psi=0.999)
        seal = result["auron_seal"]
        self.assertEqual(len(seal), 16)
        # Must be valid hex
        int(seal, 16)

    def test_auron_seal_deterministic(self):
        """Same Ψ always produces the same AURON seal."""
        result1 = self.ns.estabilizar(psi=0.999)
        result2 = self.ns.estabilizar(psi=0.999)
        self.assertEqual(result1["auron_seal"], result2["auron_seal"])

    def test_auron_seal_different_for_different_psi(self):
        """Different Ψ values produce different AURON seals."""
        result1 = self.ns.estabilizar(psi=0.999)
        result2 = self.ns.estabilizar(psi=0.888)
        self.assertNotEqual(result1["auron_seal"], result2["auron_seal"])

    def test_auron_seal_is_sha256(self):
        """AURON seal is computed via SHA-256."""
        psi = 0.999
        result = self.ns.estabilizar(psi=psi)
        estab = result["estabilidad_rad_s"]
        payload = (
            f"TOPC-AURON-NS-QCAL|"
            f"f0={F0_TOPC}|"
            f"psi={psi:.9f}|"
            f"estab={estab:.6e}|"
            f"t_meV={T_ANCLA_MEV}"
        )
        expected_seal = hashlib.sha256(payload.encode("utf-8")).hexdigest()[:16]
        self.assertEqual(result["auron_seal"], expected_seal)

    def test_estabilizar_invalid_psi_negative(self):
        """estabilizar() raises ValueError for Ψ < 0."""
        with self.assertRaises(ValueError):
            self.ns.estabilizar(psi=-0.1)

    def test_estabilizar_invalid_psi_greater_than_1(self):
        """estabilizar() raises ValueError for Ψ > 1."""
        with self.assertRaises(ValueError):
            self.ns.estabilizar(psi=1.1)

    def test_protocolo_auron_tag(self):
        """Protocol tag is TOPC-AURON-NS-QCAL."""
        result = self.ns.estabilizar(psi=0.5)
        self.assertEqual(result["protocolo"], "TOPC-AURON-NS-QCAL")

    def test_stability_linear_in_psi(self):
        """Stability is linear in Ψ: stability(0.5) = 0.5 × stability(1.0)."""
        r1 = self.ns.estabilizar(psi=1.0)
        r_half = self.ns.estabilizar(psi=0.5)
        self.assertAlmostEqual(
            r_half["estabilidad_rad_s"],
            0.5 * r1["estabilidad_rad_s"],
            delta=r1["estabilidad_rad_s"] * 1e-10,
        )


class TestCalcularTensionVortice(unittest.TestCase):
    """Tests for the module-level calcular_tension_vortice() function."""

    def test_basic_value_psi_0999(self):
        """calcular_tension_vortice(0.999) ≈ 3.85×10¹¹ rad/s."""
        tau = calcular_tension_vortice(0.999)
        self.assertAlmostEqual(tau, 3.85e11, delta=0.1e11,
                               msg="Vortex tension should be ≈3.85×10¹¹ rad/s")

    def test_formula(self):
        """Result = (t/ℏ)·sin(π/7)·Ψ."""
        psi = 0.999
        expected = (T_ANCLA_J / HBAR) * SIN_PI_7 * psi
        self.assertAlmostEqual(calcular_tension_vortice(psi), expected, delta=expected * 1e-10)

    def test_zero_coherence(self):
        """Zero coherence gives zero tension (no condensate, no vortex coupling)."""
        self.assertEqual(calcular_tension_vortice(0.0), 0.0)

    def test_unit_coherence(self):
        """Unit coherence gives maximum tension = (t/ℏ)·sin(π/7)."""
        expected_max = (T_ANCLA_J / HBAR) * SIN_PI_7
        self.assertAlmostEqual(calcular_tension_vortice(1.0), expected_max, delta=expected_max * 1e-10)

    def test_linear_in_psi(self):
        """Tension is linear in Ψ."""
        tau_1 = calcular_tension_vortice(1.0)
        tau_half = calcular_tension_vortice(0.5)
        self.assertAlmostEqual(tau_half, 0.5 * tau_1, delta=tau_1 * 1e-10)

    def test_invalid_psi_negative(self):
        """Raises ValueError for negative Ψ."""
        with self.assertRaises(ValueError):
            calcular_tension_vortice(-0.01)

    def test_invalid_psi_greater_than_1(self):
        """Raises ValueError for Ψ > 1."""
        with self.assertRaises(ValueError):
            calcular_tension_vortice(1.01)

    def test_order_of_magnitude(self):
        """Tension for Ψ=0.999 is in the range [3×10¹¹, 5×10¹¹] rad/s."""
        tau = calcular_tension_vortice(0.999)
        self.assertGreater(tau, 3e11)
        self.assertLess(tau, 5e11)

    def test_matches_ns_qcal_estabilizar(self):
        """calcular_tension_vortice(Ψ) matches NavierStokesQCAL.estabilizar(Ψ)."""
        psi = 0.888
        tau = calcular_tension_vortice(psi)
        ns = NavierStokesQCAL()
        result = ns.estabilizar(psi=psi)
        self.assertAlmostEqual(tau, result["estabilidad_rad_s"], delta=tau * 1e-10)


class TestEjecutarMotorPrimordial(unittest.TestCase):
    """Tests for ejecutar_motor_primordial() integration function."""

    def setUp(self):
        self.mp = ejecutar_motor_primordial(psi_coherence=0.999)

    def test_returns_motor_primordial_result(self):
        """Returns a MotorPrimordialResult instance."""
        self.assertIsInstance(self.mp, MotorPrimordialResult)

    def test_coherencia_global_ge_psi_min(self):
        """coherencia_global ≥ 0.888 for Ψ=0.999."""
        self.assertGreaterEqual(self.mp.coherencia_global, PSI_MIN,
                                msg="coherencia_global must be ≥ PSI_MIN=0.888")

    def test_coherencia_global_ge_psi_min_for_099(self):
        """coherencia_global ≥ 0.888 also for Ψ=0.999 (boundary check)."""
        mp = ejecutar_motor_primordial(psi_coherence=0.999)
        self.assertGreaterEqual(mp.coherencia_global, PSI_MIN)

    def test_motor_activo_true(self):
        """motor_activo = True for Ψ=0.999."""
        self.assertTrue(self.mp.motor_activo)

    def test_gap_f0_topc_hz_exact(self):
        """mp.gap.f0_topc_hz == 141700.1 (exact anchored value)."""
        self.assertEqual(self.mp.gap.f0_topc_hz, 141700.1)

    def test_gap_instance(self):
        """mp.gap is a GapOpticoManyBody instance."""
        self.assertIsInstance(self.mp.gap, GapOpticoManyBody)

    def test_tension_instance(self):
        """mp.tension is a TensionCuerdaHolografica instance."""
        self.assertIsInstance(self.mp.tension, TensionCuerdaHolografica)

    def test_hamiltoniano_instance(self):
        """mp.hamiltoniano is a HamiltonianC7 instance."""
        self.assertIsInstance(self.mp.hamiltoniano, HamiltonianC7)

    def test_ns_qcal_instance(self):
        """mp.ns_qcal is a NavierStokesQCAL instance."""
        self.assertIsInstance(self.mp.ns_qcal, NavierStokesQCAL)

    def test_psi_input_stored(self):
        """mp.psi_input matches the input."""
        self.assertEqual(self.mp.psi_input, 0.999)

    def test_estabilidad_rad_s_order(self):
        """Stability ≈ 3.85×10¹¹ rad/s for Ψ=0.999."""
        self.assertAlmostEqual(self.mp.estabilidad_rad_s, 3.85e11, delta=0.1e11)

    def test_auron_seal_hex(self):
        """AURON seal is 16 hex characters."""
        self.assertEqual(len(self.mp.auron_seal), 16)
        int(self.mp.auron_seal, 16)

    def test_gap_phi0_t_analytic(self):
        """Gap at Φ=0 ≈ 1.692·t."""
        self.assertAlmostEqual(self.mp.gap_phi0_t, 1.692, delta=0.001)

    def test_gap_phi_pi8_t_approx(self):
        """Gap at Φ=π/8 ≈ 1.49·t."""
        self.assertAlmostEqual(self.mp.gap_phi_pi8_t, 1.49, delta=0.05)

    def test_gap_phi_pi8_less_than_phi0(self):
        """AB flux reduces the gap."""
        self.assertLess(self.mp.gap_phi_pi8_t, self.mp.gap_phi0_t)

    def test_delta_e_opt_meV(self):
        """ΔE_opt ≈ 0.988 meV."""
        self.assertAlmostEqual(self.mp.gap.delta_e_opt_meV, 0.988, delta=0.001)

    def test_gamma_eff(self):
        """Γ_eff ≈ 1.69×10⁶."""
        self.assertAlmostEqual(self.mp.gap.gamma_eff, 1.69e6, delta=0.05e6)

    def test_viscosidad_zero(self):
        """Superfluid: ν = 0."""
        self.assertEqual(self.mp.ns_qcal.viscosidad, 0.0)

    def test_default_psi(self):
        """Default psi_coherence = 0.999."""
        mp_default = ejecutar_motor_primordial()
        self.assertEqual(mp_default.psi_input, 0.999)

    def test_motor_coherence_preserved(self):
        """In the superfluid (ν=0), coherencia_global equals the input Ψ."""
        for psi in (0.999, 0.95, 0.9, 0.888):
            mp = ejecutar_motor_primordial(psi_coherence=psi)
            self.assertAlmostEqual(mp.coherencia_global, psi, places=12)

    def test_motor_activo_false_below_threshold(self):
        """motor_activo = False when coherencia_global < PSI_MIN."""
        mp_low = ejecutar_motor_primordial(psi_coherence=0.5)
        self.assertFalse(mp_low.motor_activo)

    def test_invalid_psi_raises(self):
        """Raises ValueError for out-of-range psi_coherence."""
        with self.assertRaises(ValueError):
            ejecutar_motor_primordial(psi_coherence=1.5)
        with self.assertRaises(ValueError):
            ejecutar_motor_primordial(psi_coherence=-0.1)

    def test_api_example_from_problem_statement(self):
        """
        Validates the usage example from the problem statement:
            mp = ejecutar_motor_primordial(psi_coherence=0.999)
            # mp.coherencia_global ≥ 0.888, mp.motor_activo = True
            # mp.gap.f0_topc_hz == 141700.1

            estabilidad = calcular_tension_vortice(0.999)  # ≈ 3.85×10¹¹ rad/s
        """
        mp = ejecutar_motor_primordial(psi_coherence=0.999)
        self.assertGreaterEqual(mp.coherencia_global, 0.888)
        self.assertTrue(mp.motor_activo)
        self.assertEqual(mp.gap.f0_topc_hz, 141700.1)

        estabilidad = calcular_tension_vortice(0.999)
        self.assertAlmostEqual(estabilidad, 3.85e11, delta=0.1e11)


if __name__ == "__main__":
    unittest.main(verbosity=2)
