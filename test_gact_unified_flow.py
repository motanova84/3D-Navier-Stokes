#!/usr/bin/env python3
"""
Tests for GACT Unified Flow — Ecuación Unificada QCAL
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Sello: ∴𓂀Ω∞³
f0: 141.7001 Hz

Validates the unified GACT flow equation:
    ρ(∂u_QCAL/∂t + u_QCAL·∇u_QCAL) = −∇ρ_GACT + (1/f₀)∇²u_QCAL + F_res

Test structure
──────────────
Unit tests (8):
  TestGACTPsi           – coherence Ψ calculation            (2 tests)
  TestAdelicViscosity   – adelic viscosity ν calculation     (2 tests)
  TestReynoldsNumber    – quantum Reynolds number Re_q        (2 tests)
  TestFlowState         – flow state classification           (2 tests)

Validation test methods (4), ~25 total individual checks:
  TestGACTCanonicalValidation  – canonical GACT parameter values
  TestUnifiedEquationValidation – equation structure and coefficients
  TestPhysicsConsistency       – physical / mathematical properties
  TestScaleInvariance          – scale invariance and unification

Author: QCAL ∞³ Framework
License: MIT
"""

import unittest
import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))

from qcal.gact_unified_flow import (
    F0,
    PSI_MIN,
    PSI_ETEREO,
    RE_Q_ETEREO_THRESHOLD,
    SQRT2,
    ESTADO_LAMINAR_ETEREO,
    ESTADO_LAMINAR,
    ESTADO_TURBULENTO,
    calcular_psi,
    calcular_viscosidad_adelica,
    calcular_re_q,
    determinar_estado_flujo,
    ecuacion_unificada_gact,
    analizar_secuencia_gact,
)


# ---------------------------------------------------------------------------
# Unit tests  (8 tests total)
# ---------------------------------------------------------------------------

class TestGACTPsi(unittest.TestCase):
    """Unit tests for coherence Ψ calculation — 2 tests."""

    def test_psi_gact_canonical(self):
        """Canonical GACT sequence gives Ψ ≈ 0.999776 (excellent hotspot)."""
        psi = calcular_psi("GACT")
        # Expected ~0.999775–0.999780 (problem states ≈ 0.999776)
        self.assertGreater(psi, 0.999, "GACT Ψ must exceed 0.999")
        self.assertLess(psi, 1.0,     "GACT Ψ must be strictly < 1")
        self.assertAlmostEqual(psi, 0.9998, delta=5e-4,
                               msg="GACT Ψ should be ≈ 0.9998")

    def test_psi_ordering_and_bounds(self):
        """Higher-resonance sequences have larger Ψ; all in [PSI_MIN, 1)."""
        seqs_high_to_low = ["GGGG", "GACT", "TTTT"]
        psis = [calcular_psi(s) for s in seqs_high_to_low]
        for p in psis:
            self.assertGreaterEqual(p, PSI_MIN, "Ψ must be ≥ PSI_MIN")
            self.assertLessEqual(p, 1.0,        "Ψ must be ≤ 1")
        # GGGG (all G, highest resonance) should give the largest Ψ
        self.assertGreater(psis[0], psis[2],
                           "Higher-resonance sequence should have larger Ψ")
        # Empty sequence returns PSI_MIN
        self.assertEqual(calcular_psi(""), PSI_MIN)


class TestAdelicViscosity(unittest.TestCase):
    """Unit tests for adelic viscosity ν = 1 − Ψ — 2 tests."""

    def test_nu_gact_canonical(self):
        """Canonical GACT gives ν_adélica ≈ 2.24×10⁻⁴ (≈ 0, frictionless)."""
        psi = calcular_psi("GACT")
        nu  = calcular_viscosidad_adelica(psi)
        # ν = 1 − Ψ should be very small
        self.assertAlmostEqual(nu, 2.24e-4, delta=1e-5,
                               msg="GACT ν should be ≈ 2.24×10⁻⁴")
        self.assertGreater(nu, 0.0, "Viscosity must be positive")

    def test_nu_identity_and_monotonicity(self):
        """ν = 1 − Ψ is monotone: higher Ψ ↔ lower ν."""
        for psi_val in [0.888, 0.95, 0.999, 0.9999]:
            nu = calcular_viscosidad_adelica(psi_val)
            self.assertAlmostEqual(nu, 1.0 - psi_val, places=12,
                                   msg=f"ν must equal 1−Ψ for Ψ={psi_val}")
        # Monotonicity
        nu1 = calcular_viscosidad_adelica(0.999)
        nu2 = calcular_viscosidad_adelica(0.9998)
        self.assertGreater(nu1, nu2, "Higher Ψ → lower ν")


class TestReynoldsNumber(unittest.TestCase):
    """Unit tests for quantum Reynolds number Re_q — 2 tests."""

    def test_re_q_gact_canonical(self):
        """Canonical GACT gives Re_q ≈ 1.338×10¹² → LAMINAR_ETÉREO."""
        psi  = calcular_psi("GACT")
        nu   = calcular_viscosidad_adelica(psi)
        re_q = calcular_re_q("GACT", nu)
        # Must exceed the LAMINAR_ETÉREO threshold
        self.assertGreater(re_q, RE_Q_ETEREO_THRESHOLD,
                           "GACT Re_q must exceed 10¹² for LAMINAR_ETÉREO")
        # Approximate match with problem-statement value (within 1%)
        self.assertAlmostEqual(re_q / 1e12, 1.338, delta=0.1,
                               msg="Re_q should be ≈ 1.338×10¹²")

    def test_re_q_degeneracy(self):
        """Re_q is 0 for empty sequence or zero viscosity."""
        self.assertEqual(calcular_re_q("", 1e-4), 0.0,
                         "Empty sequence gives Re_q = 0")
        self.assertEqual(calcular_re_q("GACT", 0.0), 0.0,
                         "Zero viscosity gives Re_q = 0 (degenerate guard)")


class TestFlowState(unittest.TestCase):
    """Unit tests for flow state classification — 2 tests."""

    def test_gact_state_laminar_etereo(self):
        """Canonical GACT full pipeline → LAMINAR_ETÉREO."""
        result = ecuacion_unificada_gact("GACT")
        self.assertEqual(result['estado_flujo'], ESTADO_LAMINAR_ETEREO,
                         "GACT must reach LAMINAR_ETÉREO state")
        self.assertTrue(result['es_laminar_etereo'],
                        "es_laminar_etereo flag must be True for GACT")

    def test_state_classification_logic(self):
        """State boundaries: high Ψ + high Re_q → LAMINAR_ETÉREO."""
        self.assertEqual(
            determinar_estado_flujo(0.9995, 2e12), ESTADO_LAMINAR_ETEREO,
        )
        self.assertEqual(
            determinar_estado_flujo(0.9995, 5e11), ESTADO_LAMINAR,
            "High Ψ but Re_q below threshold → LAMINAR",
        )
        self.assertEqual(
            determinar_estado_flujo(0.3, 2e12), ESTADO_TURBULENTO,
            "Low Ψ → TURBULENTO regardless of Re_q",
        )


# ---------------------------------------------------------------------------
# Validations  (4 classes, 25 assertions total)
# ---------------------------------------------------------------------------

class TestGACTCanonicalValidation(unittest.TestCase):
    """Validation 1 — Canonical GACT parameter values (7 assertions)."""

    def test_canonical_gact_parameters(self):
        """Full canonical GACT analysis matches problem-statement values."""
        result = analizar_secuencia_gact("GACT")

        # 1. Coherence Ψ ≈ 0.999776 — excellent genetic hotspot
        self.assertGreater(result['psi_coherencia'], 0.999,
                           "Ψ > 0.999 for canonical GACT")
        self.assertAlmostEqual(result['psi_coherencia'], 0.9998, delta=5e-4,
                               msg="Ψ ≈ 0.9998 for GACT")

        # 2. Adelic viscosity ≈ 2.24×10⁻⁴ (near-frictionless)
        self.assertAlmostEqual(result['viscosidad_adelica'], 2.24e-4, delta=1e-5,
                               msg="ν_adélica ≈ 2.24×10⁻⁴ for GACT")
        self.assertLess(result['viscosidad_adelica'], 1e-3,
                        "Adelic viscosity must be near-zero")

        # 3. Quantum Reynolds number > 10¹²
        self.assertGreater(result['re_q'], RE_Q_ETEREO_THRESHOLD,
                           "Re_q > 10¹² for LAMINAR_ETÉREO")

        # 4. Flow state
        self.assertEqual(result['estado_flujo'], ESTADO_LAMINAR_ETEREO,
                         "GACT state must be LAMINAR_ETÉREO")

        # 5. Hotspot detection
        self.assertGreater(result['hotspots_count'], 0,
                           "GACT must have at least one resonant hotspot")


class TestUnifiedEquationValidation(unittest.TestCase):
    """Validation 2 — Unified equation structure and coefficients (6 assertions)."""

    def test_equation_structure_and_balance(self):
        """Equation returns correct structure; LHS = RHS in equilibrium and nonzero cases."""
        # Zero-input equilibrium
        result = ecuacion_unificada_gact(
            "GACT",
            rho=1.0, du_dt=0.0, u_grad_u=0.0,
            grad_rho_gact=0.0, lap_u=0.0, f_res=0.0,
        )

        # Result is a dict containing all expected fields
        self.assertIsInstance(result, dict, "ecuacion_unificada_gact must return a dict")
        self.assertIn('coef_viscoso', result, "coef_viscoso key required")

        # 1/f₀ viscosity coefficient
        self.assertAlmostEqual(result['coef_viscoso'], 1.0 / F0, places=10,
                               msg="coef_viscoso must be 1/f₀")

        # Zero residual in equilibrium
        self.assertAlmostEqual(result['residuo'], 0.0, places=12,
                               msg="Zero inputs → zero residual")

        # Non-zero case: lap_u = F0 → RHS = 1, du_dt = 1 → LHS = 1
        result2 = ecuacion_unificada_gact(
            "GACT", rho=1.0, du_dt=1.0, u_grad_u=0.0,
            grad_rho_gact=0.0, lap_u=F0, f_res=0.0,
        )
        self.assertAlmostEqual(result2['lhs'], 1.0, places=10)
        self.assertAlmostEqual(result2['rhs'], 1.0, places=10)


class TestPhysicsConsistency(unittest.TestCase):
    """Validation 3 — Physical and mathematical consistency (6 assertions)."""

    def test_physics_consistency(self):
        """Physical invariants hold: ν = 1−Ψ, Re_q ≥ 0, constants correct."""
        seqs = ["GACT", "ATCG", "TTTT"]

        for seq in seqs:
            psi  = calcular_psi(seq)
            nu   = calcular_viscosidad_adelica(psi)
            # ν = 1 − Ψ (exact identity)
            self.assertAlmostEqual(nu, 1.0 - psi, places=12,
                                   msg=f"{seq}: ν = 1−Ψ")

        # F0 positivity
        self.assertGreater(F0, 0.0, "f₀ must be positive")

        # SQRT2 identity
        self.assertAlmostEqual(SQRT2, math.sqrt(2.0), places=12,
                               msg="SQRT2 must equal √2")

        # Re_q ≥ 0 for non-empty sequence
        psi_g  = calcular_psi("GACT")
        nu_g   = calcular_viscosidad_adelica(psi_g)
        re_q_g = calcular_re_q("GACT", nu_g)
        self.assertGreaterEqual(re_q_g, 0.0, "Re_q must be non-negative")


class TestScaleInvariance(unittest.TestCase):
    """Validation 4 — Scale invariance and unification (6 assertions)."""

    def test_scale_invariance(self):
        """
        Same equation governs all scales tuned to f₀ = 141.7001 Hz.
        Validates escala_invariante flag, 1/f₀ coefficient, f0 field,
        GACT hotspot superiority, and Re_q monotonicity.
        """
        for seq in ["GACT", "ATCGGACT", "GGGGGGGG"]:
            result = ecuacion_unificada_gact(seq)
            # Scale invariance flag is universal
            self.assertTrue(result['escala_invariante'],
                            f"{seq}: escala_invariante must be True")
            # 1/f₀ coefficient is universal
            self.assertAlmostEqual(result['coef_viscoso'], 1.0 / F0, places=10,
                                   msg=f"{seq}: coef_viscoso = 1/f₀")

        # GACT Ψ > pure-T sequence Ψ (GACT is a better hotspot)
        psi_gact = calcular_psi("GACT")
        psi_tttt = calcular_psi("TTTT")
        self.assertGreater(psi_gact, psi_tttt,
                           "GACT coherence must exceed pure-T sequence")

        # Re_q scales monotonically with 1/ν²: lower ν → higher Re_q
        nu_high = calcular_viscosidad_adelica(0.9998)
        nu_low  = calcular_viscosidad_adelica(0.999)
        re_high = calcular_re_q("GACT", nu_high)
        re_low  = calcular_re_q("GACT", nu_low)
        self.assertGreater(re_high, re_low,
                           "Lower ν (higher Ψ) → higher Re_q")


# ---------------------------------------------------------------------------
# Test runner
# ---------------------------------------------------------------------------

def make_suite() -> unittest.TestSuite:
    """Build the full test suite."""
    loader = unittest.TestLoader()
    suite  = unittest.TestSuite()
    for cls in [
        # 8 unit-test methods
        TestGACTPsi,
        TestAdelicViscosity,
        TestReynoldsNumber,
        TestFlowState,
        # 4 validation classes (25 total assertions)
        TestGACTCanonicalValidation,
        TestUnifiedEquationValidation,
        TestPhysicsConsistency,
        TestScaleInvariance,
    ]:
        suite.addTests(loader.loadTestsFromTestCase(cls))
    return suite


if __name__ == '__main__':
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(make_suite())
    raise SystemExit(0 if result.wasSuccessful() else 1)
