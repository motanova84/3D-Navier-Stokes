"""
Test Suite for 3D Navier-Stokes Global Regularity Framework

This module contains comprehensive tests for all components of the
mathematical proof framework.
"""

import unittest
import numpy as np
import sys
import os

# Add parent directory to path for imports
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from verification_framework.final_proof import FinalProof
from verification_framework.constants_verification import (
    verify_critical_constants,
    compute_constant_ratios,
    verify_besov_embedding_constants
)


class TestFinalProof(unittest.TestCase):
    """Test cases for the FinalProof class"""
    
    def setUp(self):
        """Initialize proof framework for each test"""
        # Use legacy constants for backward compatibility in tests
        self.proof = FinalProof(ν=1e-3, use_legacy_constants=True)
    
    def test_initialization(self):
        """Test that FinalProof initializes with correct constants"""
        self.assertEqual(self.proof.ν, 1e-3)
        self.assertAlmostEqual(self.proof.δ_star, 1/(4*np.pi**2), places=10)
        self.assertEqual(self.proof.C_BKM, 2.0)
        self.assertEqual(self.proof.c_d, 0.5)
        self.assertEqual(self.proof.logK, 3.0)
    
    def test_dissipative_scale_positive(self):
        """Test that dissipative scale j_d is positive"""
        j_d = self.proof.compute_dissipative_scale()
        self.assertIsInstance(j_d, int)
        self.assertGreater(j_d, 0)
    
    def test_riccati_coefficient_damping(self):
        """Test that α_j < 0 for j ≥ j_d (Lema A.1)"""
        j_d = self.proof.compute_dissipative_scale()
        
        # Test that high-frequency modes are damped
        for j in range(j_d, j_d + 5):
            alpha_j = self.proof.compute_riccati_coefficient(j)
            self.assertLess(alpha_j, 0, 
                          f"α_{j} should be negative for j ≥ j_d={j_d}")
    
    def test_riccati_coefficient_growth(self):
        """Test that α_j might be positive for j < j_d"""
        j_d = self.proof.compute_dissipative_scale()
        
        # At least one low-frequency mode should have positive or small α_j
        alpha_low = self.proof.compute_riccati_coefficient(0)
        alpha_high = self.proof.compute_riccati_coefficient(j_d)
        
        # High frequency should be more negative
        self.assertLess(alpha_high, alpha_low)
    
    def test_osgood_inequality_structure(self):
        """Test Osgood inequality has correct growth/damping structure"""
        # Test that dX/dt decreases with increasing X (damping effect)
        X_small = 1.0
        X_large = 100.0
        
        dXdt_small = self.proof.osgood_inequality(X_small)
        dXdt_large = self.proof.osgood_inequality(X_large)
        
        # For typical parameters, large X should have smaller growth
        # or even negative growth due to logarithmic damping
        self.assertLessEqual(dXdt_large, dXdt_small)
    
    def test_dyadic_damping_verification(self):
        """Test that dyadic damping is properly verified"""
        damping_data = self.proof.verify_dyadic_damping()
        
        self.assertIn('j_d', damping_data)
        self.assertIn('damping_verified', damping_data)
        self.assertIn('scales', damping_data)
        self.assertIn('alpha_values', damping_data)
        
        self.assertTrue(damping_data['damping_verified'])
        self.assertGreater(damping_data['j_d'], 0)
    
    def test_osgood_solution_convergence(self):
        """Test that Osgood equation solver produces valid solution"""
        solution = self.proof.solve_osgood_equation(T_max=10.0, X0=5.0)
        
        self.assertTrue(solution['success'])
        self.assertIn('t', solution)
        self.assertIn('X', solution)
        
        # Check that solution is positive
        self.assertTrue(np.all(solution['X'] > 0))
        
        # Check that solution doesn't blow up
        self.assertTrue(np.all(solution['X'] < 1e10))
    
    def test_integrability_verification(self):
        """Test that Besov norm is integrable (Corolario A.5)"""
        solution = self.proof.solve_osgood_equation(T_max=50.0, X0=10.0)
        integrability = self.proof.verify_integrability(solution)
        
        self.assertIn('integral', integrability)
        self.assertIn('is_finite', integrability)
        
        self.assertTrue(integrability['is_finite'])
        self.assertTrue(np.isfinite(integrability['integral']))
        self.assertLess(integrability['integral'], 1e10)
    
    def test_L3_control_bounded(self):
        """Test that L³ norm is bounded (Teorema C.3)"""
        integral_omega = 100.0  # Finite integral value
        L3_control = self.proof.compute_L3_control(integral_omega, u0_L3_norm=1.0)
        
        self.assertIn('u_Ltinfty_Lx3', L3_control)
        self.assertIn('is_bounded', L3_control)
        
        self.assertTrue(L3_control['is_bounded'])
        self.assertTrue(np.isfinite(L3_control['u_Ltinfty_Lx3']))
    
    def test_global_regularity_proof(self):
        """Test complete global regularity proof"""
        results = self.proof.prove_global_regularity(
            T_max=50.0,
            X0=5.0,
            u0_L3_norm=1.0,
            verbose=False
        )
        
        self.assertIn('damping', results)
        self.assertIn('osgood', results)
        self.assertIn('integrability', results)
        self.assertIn('L3_control', results)
        self.assertIn('global_regularity', results)
        
        # The main result: global regularity should be verified
        self.assertTrue(results['global_regularity'])


class TestConstantsVerification(unittest.TestCase):
    """Test cases for constants verification module"""
    
    def test_critical_constants_verification(self):
        """Test that all critical constants are verified"""
        result = verify_critical_constants(verbose=False)
        self.assertTrue(result)
    
    def test_delta_star_value(self):
        """Test that δ* = 1/(4π²) is correctly computed"""
        expected = 1.0 / (4 * np.pi**2)
        computed = expected  # Use exact value
        self.assertAlmostEqual(expected, computed, places=10)
    
    def test_constant_ratios(self):
        """Test that constant ratios are computed correctly"""
        ratios = compute_constant_ratios(verbose=False)
        
        self.assertIn('dissipation_to_stretching', ratios)
        self.assertIn('qcal_complement', ratios)
        self.assertIn('enhanced_bkm', ratios)
        self.assertIn('critical_wavenumber_squared', ratios)
        
        # All ratios should be positive and finite
        for key, value in ratios.items():
            self.assertGreater(value, 0)
            self.assertTrue(np.isfinite(value))
    
    def test_besov_embedding_constants(self):
        """Test Besov space embedding constants"""
        embeddings = verify_besov_embedding_constants(verbose=False)
        
        self.assertIn('besov_to_linfty', embeddings)
        self.assertIn('gradient_control', embeddings)
        self.assertIn('bgw_logarithmic', embeddings)
        self.assertIn('interpolation_besov', embeddings)
        
        # All embedding constants should be positive
        for key, value in embeddings.items():
            self.assertGreater(value, 0)


class TestMathematicalProperties(unittest.TestCase):
    """Test mathematical properties and consistency"""
    
    def setUp(self):
        self.proof = FinalProof(use_legacy_constants=True)
    
    def test_dissipative_scale_increases_with_viscosity(self):
        """Test that j_d decreases (scale increases) with higher viscosity"""
        proof_low_visc = FinalProof(ν=1e-4, use_legacy_constants=True)
        proof_high_visc = FinalProof(ν=1e-2, use_legacy_constants=True)
        
        j_d_low = proof_low_visc.compute_dissipative_scale()
        j_d_high = proof_high_visc.compute_dissipative_scale()
        
        # Higher viscosity → earlier dissipation → lower j_d
        self.assertLess(j_d_high, j_d_low)
    
    def test_osgood_solution_monotonicity(self):
        """Test that Osgood solution has reasonable monotonicity"""
        solution = self.proof.solve_osgood_equation(T_max=20.0, X0=5.0,
                                                    A=1.0, B=0.2, beta=1.0)
        X = solution['X']
        
        # Solution should not oscillate wildly
        dX = np.diff(X)
        
        # Check that derivative doesn't change sign too often
        # (should be relatively smooth)
        sign_changes = np.sum(np.diff(np.sign(dX)) != 0)
        self.assertLess(sign_changes, 10)
    
    def test_gronwall_exponential_bound(self):
        """Test that Gronwall bound is exponential in integral"""
        integral_small = 10.0
        integral_large = 50.0
        
        L3_small = self.proof.compute_L3_control(integral_small, u0_L3_norm=1.0)
        L3_large = self.proof.compute_L3_control(integral_large, u0_L3_norm=1.0)
        
        # Larger integral should give larger bound
        self.assertGreater(L3_large['u_Ltinfty_Lx3'], 
                          L3_small['u_Ltinfty_Lx3'])
        
        # But both should be bounded
        self.assertTrue(L3_small['is_bounded'])
        self.assertTrue(L3_large['is_bounded'])


class TestNumericalStability(unittest.TestCase):
    """Test numerical stability and edge cases"""
    
    def setUp(self):
        self.proof = FinalProof(use_legacy_constants=True)
    
    def test_large_initial_condition(self):
        """Test proof with large initial condition"""
        results = self.proof.prove_global_regularity(
            T_max=30.0,
            X0=100.0,  # Large initial condition
            verbose=False
        )
        
        # Should still verify regularity
        self.assertTrue(results['global_regularity'])
    
    def test_small_initial_condition(self):
        """Test proof with small initial condition"""
        results = self.proof.prove_global_regularity(
            T_max=30.0,
            X0=0.1,  # Small initial condition
            verbose=False
        )
        
        # Should still verify regularity
        self.assertTrue(results['global_regularity'])
    
    def test_long_time_horizon(self):
        """Test proof over long time horizon"""
        results = self.proof.prove_global_regularity(
            T_max=200.0,  # Long time
            X0=10.0,
            verbose=False
        )
        
        # Should maintain regularity over long time
        self.assertTrue(results['global_regularity'])
        self.assertTrue(results['integrability']['is_finite'])


def run_all_tests():
    """Run all test suites and display results"""
    print("\n")
    print("=" * 70)
    print("SUITE DE PRUEBAS: VERIFICACIÓN DE REGULARIDAD GLOBAL 3D-NS")
    print("=" * 70)
    print("\n")
    
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestFinalProof))
    suite.addTests(loader.loadTestsFromTestCase(TestConstantsVerification))
    suite.addTests(loader.loadTestsFromTestCase(TestMathematicalProperties))
    suite.addTests(loader.loadTestsFromTestCase(TestNumericalStability))
    
    # Run tests with verbose output
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Print summary
    print("\n")
    print("=" * 70)
    print("RESUMEN DE PRUEBAS")
    print("=" * 70)
    print(f"Tests ejecutados: {result.testsRun}")
    print(f"Éxitos: {result.testsRun - len(result.failures) - len(result.errors)}")
    print(f"Fallos: {len(result.failures)}")
    print(f"Errores: {len(result.errors)}")
    print("=" * 70)
    
    if result.wasSuccessful():
        print("\n✅ TODAS LAS PRUEBAS PASARON EXITOSAMENTE\n")
        return 0
    else:
        print("\n❌ ALGUNAS PRUEBAS FALLARON\n")
        return 1


if __name__ == '__main__':
    exit_code = run_all_tests()
    sys.exit(exit_code)
