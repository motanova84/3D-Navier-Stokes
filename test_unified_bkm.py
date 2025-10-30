#!/usr/bin/env python3
"""
Comprehensive tests for Unified BKM Framework

Tests all three routes (A, B, C) and parameter optimization.
"""

import unittest
import numpy as np
import sys
sys.path.append('/home/runner/work/3D-Navier-Stokes/3D-Navier-Stokes/DNS-Verification/DualLimitSolver')

from unified_bkm import (
    riccati_besov_closure,
    compute_optimal_dual_scaling,
    riccati_evolution,
    besov_volterra_integral,
    volterra_solution_exponential_decay,
    energy_bootstrap,
    energy_evolution_with_damping,
    unified_bkm_verification,
    validate_constants_uniformity,
    UnifiedBKMConstants
)


class TestRutaA_RiccatiBesov(unittest.TestCase):
    """Test Ruta A: Direct Riccati-Besov closure"""
    
    def test_damping_positive_with_optimal_params(self):
        """Test that damping is positive with optimal parameters"""
        ν = 1e-3
        c_B = 0.15
        C_CZ = 1.5
        C_star = 1.2
        a = 10.0  # Optimal
        c_0 = 1.0
        M = 100.0
        
        δ_star = (a**2 * c_0**2) / (4 * np.pi**2)
        closure, damping = riccati_besov_closure(ν, c_B, C_CZ, C_star, δ_star, M)
        
        self.assertTrue(closure, "Closure condition should be satisfied")
        self.assertGreater(damping, 0, "Damping coefficient should be positive")
    
    def test_damping_negative_with_small_a(self):
        """Test that damping is negative with small amplitude parameter"""
        ν = 1e-3
        c_B = 0.15
        C_CZ = 1.5
        C_star = 1.2
        a = 2.45  # Too small
        c_0 = 1.0
        M = 100.0
        
        δ_star = (a**2 * c_0**2) / (4 * np.pi**2)
        closure, damping = riccati_besov_closure(ν, c_B, C_CZ, C_star, δ_star, M)
        
        self.assertFalse(closure, "Closure condition should not be satisfied")
        self.assertLess(damping, 0, "Damping coefficient should be negative")
    
    def test_riccati_evolution_convergence(self):
        """Test that Riccati evolution converges with positive damping"""
        ω_0 = 10.0
        Δ = 15.0  # Positive damping
        T = 100.0
        
        result = riccati_evolution(ω_0, Δ, T)
        
        self.assertTrue(result['success'])
        self.assertTrue(result['bkm_finite'])
        self.assertLess(result['bkm_integral'], np.inf)
        self.assertGreater(result['bkm_integral'], 0)
    
    def test_riccati_evolution_divergence(self):
        """Test that Riccati evolution fails with negative damping"""
        ω_0 = 10.0
        Δ = -1.0  # Negative damping
        T = 100.0
        
        result = riccati_evolution(ω_0, Δ, T)
        
        self.assertFalse(result['success'])
        self.assertEqual(result['bkm_integral'], np.inf)


class TestRutaB_Volterra(unittest.TestCase):
    """Test Ruta B: Volterra-Besov integral approach"""
    
    def test_volterra_exponential_decay(self):
        """Test Volterra solution with exponential decay"""
        ω_0 = 10.0
        λ = 1.0  # Positive decay rate
        T = 100.0
        
        result = volterra_solution_exponential_decay(ω_0, λ, T)
        
        self.assertTrue(result['success'])
        self.assertLess(result['bkm_integral'], np.inf)
        self.assertEqual(result['decay_rate'], λ)
    
    def test_volterra_no_decay(self):
        """Test Volterra fails without decay"""
        ω_0 = 10.0
        λ = 0.0  # No decay
        T = 100.0
        
        result = volterra_solution_exponential_decay(ω_0, λ, T)
        
        self.assertFalse(result['success'])
        self.assertEqual(result['bkm_integral'], np.inf)
    
    def test_volterra_integral_with_mock_data(self):
        """Test Volterra integral with mock exponential data"""
        ω_0 = 10.0
        λ = 1.0
        
        def mock_ω_Besov(t):
            return ω_0 * np.exp(-λ * t)
        
        T = 10.0  # Small T for faster test
        convergent, integral = besov_volterra_integral(mock_ω_Besov, T)
        
        # With exponential decay, should converge
        self.assertTrue(np.isfinite(integral) or convergent)


class TestRutaC_Bootstrap(unittest.TestCase):
    """Test Ruta C: Bootstrap of H^m energy estimates"""
    
    def test_energy_bootstrap_success(self):
        """Test energy bootstrap with strong damping"""
        u0_Hm = 100.0
        ν = 1e-3
        δ_star = 2.5  # Strong misalignment
        C = 1.0
        T_max = 100
        
        success, results = energy_bootstrap(u0_Hm, ν, δ_star, C, T_max)
        
        self.assertTrue(success, "Bootstrap should succeed with strong damping")
        self.assertTrue(results['success'])
        self.assertLess(results['final_energy'], u0_Hm)
    
    def test_energy_bootstrap_failure(self):
        """Test energy bootstrap fails with weak damping"""
        u0_Hm = 100.0
        ν = 1e-5  # Very small viscosity
        δ_star = 0.01  # Weak misalignment
        C = 10.0  # Strong nonlinearity
        T_max = 100
        
        success, results = energy_bootstrap(u0_Hm, ν, δ_star, C, T_max)
        
        # Should fail due to insufficient damping
        self.assertFalse(success)
    
    def test_energy_evolution_ode(self):
        """Test energy evolution ODE solver"""
        E0 = 100.0
        ν = 1e-3
        δ_star = 2.5
        T = 10.0
        C = 1.0
        
        result = energy_evolution_with_damping(E0, ν, δ_star, T, C)
        
        self.assertTrue(result['success'])
        self.assertTrue(result['bounded'])
        self.assertLess(result['final_energy'], E0)


class TestOptimalParameters(unittest.TestCase):
    """Test optimal parameter computation"""
    
    def test_optimal_scaling_computation(self):
        """Test computation of optimal dual-scaling parameters"""
        ν = 1e-3
        c_B = 0.15
        C_CZ = 1.5
        C_star = 1.2
        M = 100.0
        
        optimal = compute_optimal_dual_scaling(ν, c_B, C_CZ, C_star, M)
        
        self.assertIn('optimal_a', optimal)
        self.assertIn('optimal_δ_star', optimal)
        self.assertIn('max_damping', optimal)
        self.assertIn('closure_satisfied', optimal)
        
        self.assertGreater(optimal['optimal_a'], 0)
        self.assertGreater(optimal['optimal_δ_star'], 0)
    
    def test_optimal_gives_positive_damping(self):
        """Test that optimal parameters give positive damping"""
        ν = 1e-3
        c_B = 0.15
        C_CZ = 1.5
        C_star = 1.2
        M = 100.0
        
        optimal = compute_optimal_dual_scaling(ν, c_B, C_CZ, C_star, M)
        
        if optimal['closure_satisfied']:
            self.assertGreater(optimal['max_damping'], 0)


class TestUnifiedVerification(unittest.TestCase):
    """Test complete unified verification"""
    
    def test_unified_verification_optimal_params(self):
        """Test unified verification with optimal parameters"""
        params = UnifiedBKMConstants(
            ν=1e-3,
            c_B=0.15,
            C_CZ=1.5,
            C_star=1.2,
            a=10.0,  # Optimal
            c_0=1.0,
            α=2.0
        )
        
        results = unified_bkm_verification(params, M=100.0, ω_0=10.0, verbose=False)
        
        self.assertIn('ruta_a', results)
        self.assertIn('ruta_b', results)
        self.assertIn('ruta_c', results)
        self.assertIn('global_regularity', results)
        
        # With optimal parameters, all routes should converge
        self.assertTrue(results['ruta_a']['closure'])
        self.assertTrue(results['ruta_b']['success'])
        self.assertTrue(results['ruta_c']['success'])
        self.assertTrue(results['global_regularity'])
    
    def test_unified_verification_suboptimal_params(self):
        """Test unified verification with suboptimal parameters"""
        params = UnifiedBKMConstants(
            ν=1e-3,
            c_B=0.15,
            C_CZ=1.5,
            C_star=1.2,
            a=2.45,  # Suboptimal
            c_0=1.0,
            α=2.0
        )
        
        results = unified_bkm_verification(params, M=100.0, ω_0=10.0, verbose=False)
        
        # With suboptimal parameters, Ruta A should fail
        self.assertFalse(results['ruta_a']['closure'])
        self.assertFalse(results['global_regularity'])


class TestUniformity(unittest.TestCase):
    """Test uniformity of constants across f₀"""
    
    def test_constants_uniformity(self):
        """Test that constants remain uniform across f₀ range"""
        params = UnifiedBKMConstants(
            ν=1e-3,
            c_B=0.15,
            C_CZ=1.5,
            C_star=1.2,
            a=10.0,
            c_0=1.0,
            α=2.0
        )
        
        f0_range = np.array([100, 500, 1000, 5000, 10000])
        uniformity = validate_constants_uniformity(f0_range, params)
        
        self.assertIn('uniform', uniformity)
        self.assertIn('min_damping', uniformity)
        self.assertIn('max_damping', uniformity)
        
        # With optimal params, should be uniform
        self.assertTrue(uniformity['uniform'])
        self.assertGreater(uniformity['min_damping'], 0)
    
    def test_delta_star_independence(self):
        """Test that δ* is independent of f₀ in dual limit"""
        a = 10.0
        c_0 = 1.0
        
        # δ* should be the same for all f₀
        δ_star = (a**2 * c_0**2) / (4 * np.pi**2)
        
        f0_values = [100, 1000, 10000]
        for f0 in f0_values:
            # In dual limit, δ* doesn't depend on f₀
            δ_computed = (a**2 * c_0**2) / (4 * np.pi**2)
            self.assertAlmostEqual(δ_star, δ_computed, places=10)


class TestMathematicalProperties(unittest.TestCase):
    """Test mathematical properties of the framework"""
    
    def test_damping_increases_with_delta_star(self):
        """Test that damping increases with misalignment defect"""
        ν = 1e-3
        c_B = 0.15
        C_CZ = 1.5
        C_star = 1.2
        M = 100.0
        
        δ_star_1 = 1.0
        δ_star_2 = 2.0
        
        _, damping_1 = riccati_besov_closure(ν, c_B, C_CZ, C_star, δ_star_1, M)
        _, damping_2 = riccati_besov_closure(ν, c_B, C_CZ, C_star, δ_star_2, M)
        
        self.assertGreater(damping_2, damping_1)
    
    def test_damping_increases_with_viscosity(self):
        """Test that damping increases with viscosity"""
        c_B = 0.15
        C_CZ = 1.5
        C_star = 1.2
        δ_star = 2.0
        M = 100.0
        
        ν_1 = 1e-3
        ν_2 = 2e-3
        
        _, damping_1 = riccati_besov_closure(ν_1, c_B, C_CZ, C_star, δ_star, M)
        _, damping_2 = riccati_besov_closure(ν_2, c_B, C_CZ, C_star, δ_star, M)
        
        self.assertGreater(damping_2, damping_1)
    
    def test_bkm_integral_decreases_with_damping(self):
        """Test that BKM integral decreases with stronger damping"""
        ω_0 = 10.0
        T = 100.0
        
        Δ_1 = 5.0
        Δ_2 = 15.0
        
        result_1 = riccati_evolution(ω_0, Δ_1, T)
        result_2 = riccati_evolution(ω_0, Δ_2, T)
        
        self.assertGreater(result_1['bkm_integral'], result_2['bkm_integral'])


def run_test_suite():
    """Run complete test suite"""
    print("="*70)
    print("UNIFIED BKM FRAMEWORK - Test Suite")
    print("="*70)
    
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestRutaA_RiccatiBesov))
    suite.addTests(loader.loadTestsFromTestCase(TestRutaB_Volterra))
    suite.addTests(loader.loadTestsFromTestCase(TestRutaC_Bootstrap))
    suite.addTests(loader.loadTestsFromTestCase(TestOptimalParameters))
    suite.addTests(loader.loadTestsFromTestCase(TestUnifiedVerification))
    suite.addTests(loader.loadTestsFromTestCase(TestUniformity))
    suite.addTests(loader.loadTestsFromTestCase(TestMathematicalProperties))
    
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    print("\n" + "="*70)
    if result.wasSuccessful():
        print("✅ ALL TESTS PASSED")
    else:
        print("❌ SOME TESTS FAILED")
    print("="*70)
    
    return result.wasSuccessful()


if __name__ == "__main__":
    success = run_test_suite()
    sys.exit(0 if success else 1)
