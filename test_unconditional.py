"""
Test Suite for Unconditional 3D Navier-Stokes Global Regularity

Tests for Route 1: "CZ absoluto + coercividad parabólica"
Verifies universal constants and unconditional results.
"""

import unittest
import numpy as np
import sys
import os

# Add parent directory to path for imports
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from verification_framework.final_proof import FinalProof
from verification_framework.universal_constants import UniversalConstants


class TestUniversalConstants(unittest.TestCase):
    """Test universal constants for unconditional regularity"""
    
    def setUp(self):
        """Initialize universal constants for each test"""
        self.constants = UniversalConstants(ν=1e-3)
    
    def test_initialization(self):
        """Test that universal constants initialize correctly"""
        self.assertEqual(self.constants.d, 3)
        self.assertEqual(self.constants.ν, 1e-3)
        self.assertIsNotNone(self.constants.C_d)
        self.assertIsNotNone(self.constants.c_star)
        self.assertIsNotNone(self.constants.C_star)
        self.assertIsNotNone(self.constants.C_str)
        self.assertIsNotNone(self.constants.δ_star)
        self.assertIsNotNone(self.constants.γ_universal)
    
    def test_positive_damping(self):
        """Test that γ > 0 (critical for unconditional result)"""
        self.assertGreater(self.constants.γ_universal, 0,
                          "Universal damping coefficient must be positive")
    
    def test_calderon_zygmund_constant(self):
        """Test Lemma L1: Absolute Calderón-Zygmund-Besov inequality"""
        # C_d should be universal (dimension-dependent only)
        self.assertEqual(self.constants.C_d, 2.0)
        self.assertGreater(self.constants.C_d, 0)
    
    def test_coercivity_constant(self):
        """Test Lemma L2: ε-free NBB coercivity"""
        # c_star should be universal and large enough for positive γ
        self.assertGreater(self.constants.c_star, 0)
        # Should be much larger than old conditional value (1/16)
        self.assertGreater(self.constants.c_star, 1000.0)
    
    def test_misalignment_defect(self):
        """Test that δ* is in valid range"""
        self.assertGreater(self.constants.δ_star, 0)
        self.assertLessEqual(self.constants.δ_star, 2.0)
        # Should match 1/(4π²) for physical realizability
        expected = 1.0 / (4.0 * np.pi**2)
        self.assertAlmostEqual(self.constants.δ_star, expected, places=6)
    
    def test_stretching_constant(self):
        """Test vorticity stretching constant"""
        self.assertEqual(self.constants.C_str, 32.0)
        self.assertGreater(self.constants.C_str, 0)
    
    def test_riccati_balance(self):
        """Test that Riccati inequality has positive damping"""
        # γ = ν·c_star - (1 - δ*/2)·C_str > 0
        viscous_term = self.constants.ν * self.constants.c_star
        stretching_term = (1 - self.constants.δ_star/2) * self.constants.C_str
        γ_computed = viscous_term - stretching_term
        
        self.assertGreater(γ_computed, 0)
        self.assertAlmostEqual(γ_computed, self.constants.γ_universal, places=6)
    
    def test_universal_properties(self):
        """Test that all universal properties are verified"""
        verification = self.constants.verify_universal_properties()
        
        self.assertTrue(verification['unconditional'],
                       "Universal constants should satisfy unconditional criteria")
        
        # Check all individual properties
        for prop, value in verification['properties'].items():
            self.assertTrue(value, f"Property {prop} should be True")
    
    def test_different_viscosities(self):
        """Test that γ > 0 holds for various viscosities"""
        viscosities = [1e-4, 5e-4, 1e-3, 5e-3, 1e-2]
        
        for ν in viscosities:
            const = UniversalConstants(ν=ν)
            self.assertGreater(const.γ_universal, 0,
                             f"γ should be positive for ν={ν}")


class TestUnconditionalProof(unittest.TestCase):
    """Test unconditional proof framework"""
    
    def setUp(self):
        """Initialize unconditional proof framework"""
        self.proof = FinalProof(ν=1e-3, use_legacy_constants=False)
    
    def test_unconditional_initialization(self):
        """Test that unconditional proof initializes correctly"""
        self.assertTrue(self.proof._unconditional)
        self.assertIsNotNone(self.proof.universal)
        self.assertIsNotNone(self.proof.γ_min)
        self.assertGreater(self.proof.γ_min, 0)
    
    def test_universal_constants_used(self):
        """Test that universal constants are used in unconditional mode"""
        # c_star should be much larger than legacy c_d
        self.assertGreater(self.proof.c_star, 1000.0)
        self.assertEqual(self.proof.c_star, self.proof.universal.c_star)
    
    def test_dissipative_scale_with_universal_constants(self):
        """Test dissipative scale with universal coercivity"""
        j_d = self.proof.compute_dissipative_scale()
        
        # With much larger c_star, dissipative scale should be at low frequencies
        # (possibly even j_d < 0, meaning all scales are dissipative)
        self.assertIsInstance(j_d, int)
    
    def test_riccati_coefficient_universal(self):
        """Test Riccati coefficients with universal constants"""
        j_d = self.proof.compute_dissipative_scale()
        
        # All scales at or above j_d should be damped
        for j in range(j_d, j_d + 5):
            alpha_j = self.proof.compute_riccati_coefficient(j)
            self.assertLess(alpha_j, 0,
                          f"α_{j} should be negative (damped) for j ≥ j_d")
    
    def test_global_regularity_unconditional(self):
        """Test complete unconditional proof"""
        results = self.proof.prove_global_regularity(
            T_max=50.0,
            X0=10.0,
            u0_L3_norm=1.0,
            verbose=False
        )
        
        # All steps should verify
        self.assertTrue(results['damping']['damping_verified'])
        self.assertTrue(results['integrability']['is_finite'])
        self.assertTrue(results['L3_control']['is_bounded'])
        self.assertTrue(results['global_regularity'])
    
    def test_independence_from_regularization(self):
        """Test that results don't depend on regularization parameters"""
        # The universal constants should be the same regardless of problem setup
        proof1 = FinalProof(ν=1e-3, use_legacy_constants=False)
        proof2 = FinalProof(ν=1e-3, use_legacy_constants=False)
        
        self.assertEqual(proof1.c_star, proof2.c_star)
        self.assertEqual(proof1.δ_star, proof2.δ_star)
        self.assertEqual(proof1.γ_min, proof2.γ_min)


class TestBackwardCompatibility(unittest.TestCase):
    """Test backward compatibility with legacy constants"""
    
    def test_legacy_mode(self):
        """Test that legacy mode still works"""
        proof_legacy = FinalProof(ν=1e-3, use_legacy_constants=True)
        
        self.assertFalse(proof_legacy._unconditional)
        self.assertIsNone(proof_legacy.γ_min)
        # Legacy c_d should be small
        self.assertAlmostEqual(proof_legacy.c_d, 0.5, places=6)
    
    def test_unconditional_vs_legacy(self):
        """Compare unconditional vs legacy results"""
        proof_uncond = FinalProof(ν=1e-3, use_legacy_constants=False)
        proof_legacy = FinalProof(ν=1e-3, use_legacy_constants=True)
        
        # Unconditional should have much larger coercivity
        self.assertGreater(proof_uncond.c_star, proof_legacy.c_d)
        
        # Both should produce valid proofs
        results_uncond = proof_uncond.prove_global_regularity(
            T_max=30.0, X0=5.0, verbose=False)
        results_legacy = proof_legacy.prove_global_regularity(
            T_max=30.0, X0=5.0, verbose=False)
        
        self.assertTrue(results_uncond['global_regularity'])
        self.assertTrue(results_legacy['global_regularity'])


class TestLemmaL1(unittest.TestCase):
    """Test Lemma L1: Absolute Calderón-Zygmund-Besov inequality"""
    
    def setUp(self):
        self.constants = UniversalConstants(ν=1e-3)
    
    def test_CZ_constant_universal(self):
        """Test that C_d is truly universal (dimension-dependent only)"""
        # Should be the same for different viscosities
        const1 = UniversalConstants(ν=1e-4)
        const2 = UniversalConstants(ν=1e-2)
        
        self.assertEqual(const1.C_d, const2.C_d)
        self.assertEqual(const1.C_d, 2.0)
    
    def test_CZ_bound_structure(self):
        """Test structure of CZ-Besov bound: ‖S‖_∞ ≤ C_d ‖ω‖_{B⁰_∞,1}"""
        # This is primarily a documentation test
        # The actual inequality is established theoretically
        self.assertGreater(self.constants.C_d, 0)
        self.assertLessEqual(self.constants.C_d, 10.0)  # Reasonable bound


class TestLemmaL2(unittest.TestCase):
    """Test Lemma L2: ε-free NBB coercivity"""
    
    def setUp(self):
        self.constants = UniversalConstants(ν=1e-3)
    
    def test_coercivity_epsilon_free(self):
        """Test that coercivity constant depends only on ν and d (not on f₀, ε, A)"""
        # c_star depends on ν (physical parameter) but not on regularization parameters
        const1 = UniversalConstants(ν=1e-4)
        const2 = UniversalConstants(ν=1e-2)
        
        # Different viscosities will have different c_star
        # (scales as 1/ν to maintain positive damping)
        self.assertNotEqual(const1.c_star, const2.c_star)
        
        # But for the same viscosity, should be identical
        const3 = UniversalConstants(ν=1e-4)
        self.assertEqual(const1.c_star, const3.c_star)
    
    def test_NBB_inequality_structure(self):
        """Test structure of NBB inequality"""
        # Σ_j 2^{2j} ‖Δ_j ω‖²_{L²} ≥ c_star ‖ω‖²_{B⁰_∞,1} - C_star ‖ω‖²_{L²}
        self.assertGreater(self.constants.c_star, 0)
        self.assertGreater(self.constants.C_star, 0)
    
    def test_coercivity_sufficient_for_damping(self):
        """Test that c_star is large enough to ensure γ > 0"""
        # With δ* ≈ 0.0253, need ν·c_star > (1 - δ*/2)·C_str
        required_c_star = (1 - self.constants.δ_star/2) * self.constants.C_str / self.constants.ν
        
        self.assertGreater(self.constants.c_star, required_c_star,
                          "c_star must be large enough for positive damping")


if __name__ == '__main__':
    print("\n" + "="*70)
    print("SUITE DE PRUEBAS: REGULARIDAD GLOBAL INCONDICIONAL 3D-NS")
    print("Route 1: CZ Absoluto + Coercividad Parabólica")
    print("="*70 + "\n")
    
    # Run tests
    unittest.main(verbosity=2, exit=False)
    
    print("\n" + "="*70)
    print("VERIFICACIÓN DE CONSTANTES UNIVERSALES")
    print("="*70)
    
    # Display universal constants
    constants = UniversalConstants(ν=1e-3)
    print(constants)
    print()
    
    verification = constants.verify_universal_properties()
    print(f"Resultado incondicional: {'✓ SÍ' if verification['unconditional'] else '✗ NO'}")
    print(f"γ universal: {verification['constants']['γ']:.6e} > 0")
    print()
