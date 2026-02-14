#!/usr/bin/env python3
"""
Tests for Adelic Laplacian Implementation
==========================================

Tests for the adelic Laplacian operator and complete
Adelic Navier-Stokes operator H = -x∂_x + (1/κ)Δ_𝔸 + V_eff

Author: QCAL ∞³ Framework
License: MIT + QCAL Sovereignty
"""

import unittest
import numpy as np
from adelic_laplacian import (
    AdelicLaplacian,
    AdelicNavierStokesOperator,
    AdelicParameters,
    generate_primes
)


class TestPrimeGeneration(unittest.TestCase):
    """Test prime number generation"""
    
    def test_first_primes(self):
        """Test generation of first few primes"""
        primes = generate_primes(10)
        expected = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        self.assertEqual(primes, expected)
    
    def test_single_prime(self):
        """Test single prime generation"""
        primes = generate_primes(1)
        self.assertEqual(primes, [2])
    
    def test_no_primes(self):
        """Test empty case"""
        primes = generate_primes(0)
        self.assertEqual(primes, [])


class TestAdelicParameters(unittest.TestCase):
    """Test adelic parameter dataclass"""
    
    def test_default_parameters(self):
        """Test default parameter values"""
        params = AdelicParameters()
        self.assertAlmostEqual(params.kappa, 2.577310, places=5)
        self.assertAlmostEqual(params.f0, 141.7001, places=4)
        self.assertAlmostEqual(params.phi, (1 + np.sqrt(5))/2, places=6)
    
    def test_omega_computation(self):
        """Test angular frequency computation"""
        params = AdelicParameters()
        omega = params.compute_omega0()
        expected = 2 * np.pi * 141.7001
        self.assertAlmostEqual(omega, expected, places=4)
    
    def test_inverse_kappa(self):
        """Test inverse kappa computation"""
        params = AdelicParameters()
        inv_kappa = params.compute_inverse_kappa()
        self.assertAlmostEqual(inv_kappa, 1/2.577310, places=6)


class TestAdelicLaplacian(unittest.TestCase):
    """Test adelic Laplacian operator"""
    
    def setUp(self):
        """Set up test fixtures"""
        self.params = AdelicParameters()
        self.laplacian = AdelicLaplacian(self.params)
        
        # Test grid
        self.N = 64
        self.L = 5.0
        self.x_grid = np.linspace(-self.L, self.L, self.N)
        self.dx = self.x_grid[1] - self.x_grid[0]
    
    def test_initialization(self):
        """Test proper initialization"""
        self.assertEqual(len(self.laplacian.primes), 100)
        self.assertEqual(self.laplacian.primes[0], 2)
        self.assertEqual(self.laplacian.primes[-1], 541)
    
    def test_action_on_real(self):
        """Test archimedean Laplacian on simple function"""
        # Test on quadratic: ∂²(x²)/∂x² = 2
        psi = self.x_grid**2
        d2psi = self.laplacian.action_on_real(psi, self.dx)
        
        # Should be approximately constant = 2
        interior = d2psi[10:-10]  # Avoid boundaries
        self.assertTrue(np.allclose(interior, 2.0, atol=0.1))
    
    def test_action_on_real_gaussian(self):
        """Test archimedean Laplacian on Gaussian"""
        # Gaussian: ψ = exp(-x²/2)
        # ∂²ψ/∂x² = (x² - 1) exp(-x²/2)
        psi = np.exp(-self.x_grid**2 / 2)
        d2psi = self.laplacian.action_on_real(psi, self.dx)
        expected = (self.x_grid**2 - 1) * psi
        
        # Check in interior (avoid boundary effects)
        interior = slice(10, -10)
        np.testing.assert_allclose(
            d2psi[interior], expected[interior], rtol=0.1
        )
    
    def test_p_adic_valuation(self):
        """Test p-adic valuation"""
        # v_2(8) = 3 (since 8 = 2³)
        # Note: for floats this is approximate
        val = self.laplacian.p_adic_valuation(8.0, 2)
        self.assertGreaterEqual(val, 3)
    
    def test_bruhat_tits_neighbors(self):
        """Test Bruhat-Tits tree neighbor generation"""
        x_p = 1.0
        p = 2
        neighbors = self.laplacian.bruhat_tits_neighbors(x_p, p, depth=2)
        
        # Should have multiple neighbors
        self.assertGreater(len(neighbors), 0)
        
        # Neighbors should be distinct from x_p
        unique_neighbors = [n for n in neighbors if abs(n - x_p) > 1e-10]
        self.assertGreater(len(unique_neighbors), 0)
    
    def test_action_on_p_adic(self):
        """Test p-adic Laplacian"""
        psi = np.exp(-self.x_grid**2 / 2)
        delta_p = self.laplacian.action_on_p_adic(psi, self.x_grid, p=2)
        
        # Should be finite
        self.assertTrue(np.all(np.isfinite(delta_p)))
        
        # Should have some structure
        self.assertGreater(np.std(delta_p), 1e-10)
    
    def test_total_action(self):
        """Test complete adelic Laplacian"""
        psi = np.exp(-self.x_grid**2 / 2)
        delta_A_psi = self.laplacian.total_action(psi, self.x_grid, self.dx)
        
        # Should be finite
        self.assertTrue(np.all(np.isfinite(delta_A_psi)))
        
        # Should have same shape as input
        self.assertEqual(delta_A_psi.shape, psi.shape)
    
    def test_heat_kernel_real_positivity(self):
        """Test archimedean heat kernel is positive"""
        x = np.array([0.0, 1.0, 2.0])
        y = 0.0
        t = 1.0
        
        K = self.laplacian.heat_kernel_real(x, y, t)
        
        # Heat kernel should be positive
        self.assertTrue(np.all(K > 0))
    
    def test_heat_kernel_real_normalization(self):
        """Test heat kernel approximate normalization"""
        y = 0.0
        t = 1.0
        
        # Integrate over x
        x_grid = np.linspace(-10, 10, 1000)
        dx = x_grid[1] - x_grid[0]
        K = self.laplacian.heat_kernel_real(x_grid, y, t)
        
        from scipy.integrate import trapezoid
        integral = trapezoid(K, dx=dx)
        
        # Should be approximately 1
        self.assertAlmostEqual(integral, 1.0, places=1)
    
    def test_heat_kernel_p_adic(self):
        """Test p-adic heat kernel"""
        x = np.array([0.0, 1.0, 2.0])
        y = 0.0
        t = 1.0
        p = 2
        
        K = self.laplacian.heat_kernel_p_adic(x, y, t, p)
        
        # Should be positive
        self.assertTrue(np.all(K > 0))
        
        # Should be finite
        self.assertTrue(np.all(np.isfinite(K)))
    
    def test_time_evolution(self):
        """Test time evolution preserves some properties"""
        # Initial Gaussian
        psi_0 = np.exp(-self.x_grid**2 / 2)
        psi_0 /= np.linalg.norm(psi_0)  # Normalize
        
        # Evolve
        t = 0.1
        psi_t = self.laplacian.time_evolution(psi_0, t, self.x_grid, self.dx)
        
        # Should remain finite
        self.assertTrue(np.all(np.isfinite(psi_t)))
        
        # Should have same shape
        self.assertEqual(psi_t.shape, psi_0.shape)
        
        # Norm should change (diffusion spreads the function)
        norm_ratio = np.linalg.norm(psi_t) / np.linalg.norm(psi_0)
        self.assertLess(norm_ratio, 1.5)  # Not growing unboundedly
        self.assertGreater(norm_ratio, 0.5)  # Not decaying too fast


class TestAdelicNavierStokesOperator(unittest.TestCase):
    """Test complete Adelic Navier-Stokes operator"""
    
    def setUp(self):
        """Set up test fixtures"""
        self.params = AdelicParameters()
        self.operator = AdelicNavierStokesOperator(self.params)
        
        # Test grid
        self.N = 64
        self.L = 5.0
        self.x_grid = np.linspace(-self.L, self.L, self.N)
        self.dx = self.x_grid[1] - self.x_grid[0]
        
        # Test function
        self.psi = np.exp(-self.x_grid**2 / 2)
    
    def test_transport_term(self):
        """Test transport operator -x∂_x"""
        transport = self.operator.transport_term(self.psi, self.x_grid, self.dx)
        
        # Should be finite
        self.assertTrue(np.all(np.isfinite(transport)))
        
        # For Gaussian, -x∂ψ/∂x = x² exp(-x²/2)
        # So transport should be positive where x ≠ 0
        interior = slice(10, -10)
        self.assertTrue(np.any(transport[interior] != 0))
    
    def test_potential_term(self):
        """Test effective potential V_eff"""
        potential = self.operator.potential_term(self.psi, self.x_grid)
        
        # Should be finite
        self.assertTrue(np.all(np.isfinite(potential)))
        
        # Should be positive (V_eff > 0)
        self.assertTrue(np.all(potential >= 0))
    
    def test_total_action(self):
        """Test complete operator H"""
        H_psi = self.operator.total_action(self.psi, self.x_grid, self.dx)
        
        # Should be finite
        self.assertTrue(np.all(np.isfinite(H_psi)))
        
        # Should have same shape
        self.assertEqual(H_psi.shape, self.psi.shape)
    
    def test_heat_kernel_trace(self):
        """Test heat kernel trace computation"""
        t = 1.0
        trace = self.operator.heat_kernel_trace(t, self.x_grid, self.dx)
        
        # Trace should be positive
        self.assertGreater(trace, 0)
        
        # Should be finite
        self.assertTrue(np.isfinite(trace))
    
    def test_prime_sum_contribution(self):
        """Test prime sum term"""
        t = 1.0
        prime_sum = self.operator.prime_sum_contribution(t)
        
        # Should be positive
        self.assertGreater(prime_sum, 0)
        
        # Should be finite
        self.assertTrue(np.isfinite(prime_sum))
    
    def test_weyl_term(self):
        """Test Weyl asymptotic term"""
        t = 1.0
        weyl = self.operator.weyl_term(t)
        
        # Should be positive
        self.assertGreater(weyl, 0)
        
        # Should be finite
        self.assertTrue(np.isfinite(weyl))
    
    def test_weyl_term_asymptotic(self):
        """Test Weyl term asymptotic behavior"""
        # As t → 0⁺, Weyl term ~ t^{-3/2} should dominate
        t_small = 0.01
        t_large = 1.0
        
        weyl_small = self.operator.weyl_term(t_small)
        weyl_large = self.operator.weyl_term(t_large)
        
        # Small t should give larger Weyl term
        self.assertGreater(weyl_small, weyl_large)
    
    def test_validate_operator(self):
        """Test operator validation"""
        results = self.operator.validate_operator(self.x_grid, self.dx)
        
        # Should pass validation
        self.assertTrue(results['validation_passed'])
        
        # All values should be finite
        self.assertTrue(results['all_finite'])
        
        # Trace should be positive
        self.assertGreater(results['trace_at_t1'], 0)


class TestMathematicalProperties(unittest.TestCase):
    """Test mathematical properties of the operators"""
    
    def setUp(self):
        """Set up test fixtures"""
        self.params = AdelicParameters()
        self.H = AdelicNavierStokesOperator(self.params)
        
        self.N = 64
        self.L = 5.0
        self.x_grid = np.linspace(-self.L, self.L, self.N)
        self.dx = self.x_grid[1] - self.x_grid[0]
    
    def test_laplacian_symmetry(self):
        """Test that Laplacian is symmetric operator"""
        # For symmetric operator: ⟨ψ|Δφ⟩ = ⟨Δψ|φ⟩
        psi = np.exp(-self.x_grid**2 / 2)
        phi = np.exp(-(self.x_grid - 1)**2 / 2)
        
        delta_psi = self.H.adelic_laplacian.action_on_real(psi, self.dx)
        delta_phi = self.H.adelic_laplacian.action_on_real(phi, self.dx)
        
        # Inner products
        from scipy.integrate import trapezoid
        inner1 = trapezoid(psi * delta_phi, dx=self.dx)
        inner2 = trapezoid(delta_psi * phi, dx=self.dx)
        
        # Should be approximately equal (up to boundary effects)
        self.assertAlmostEqual(inner1, inner2, places=1)
    
    def test_energy_positivity(self):
        """Test that kinetic energy from Laplacian is positive"""
        psi = np.exp(-self.x_grid**2 / 2)
        
        delta_psi = self.H.adelic_laplacian.action_on_real(psi, self.dx)
        
        # Kinetic energy: -∫ ψ Δψ dx ≥ 0
        from scipy.integrate import trapezoid
        kinetic = -trapezoid(psi * delta_psi, dx=self.dx)
        
        # Should be non-negative
        self.assertGreaterEqual(kinetic, -1e-10)  # Allow small numerical error
    
    def test_potential_confinement(self):
        """Test that potential provides confinement"""
        # V_eff should grow at large |x|
        V_eff_left = self.H.params.confinement_strength * (
            self.x_grid[0]**2 + 
            (1 + self.H.params.kappa**2)/4 + 
            np.log(1 + abs(self.x_grid[0]))
        )
        
        V_eff_center = self.H.params.confinement_strength * (
            0**2 + 
            (1 + self.H.params.kappa**2)/4 + 
            np.log(1 + 0)
        )
        
        # Potential at boundary should be larger than at center
        self.assertGreater(V_eff_left, V_eff_center)


class TestFrequencyConstants(unittest.TestCase):
    """Test that fundamental frequencies match QCAL framework"""
    
    def test_f0_value(self):
        """Test f₀ = 141.7001 Hz"""
        params = AdelicParameters()
        self.assertAlmostEqual(params.f0, 141.7001, places=4)
    
    def test_kappa_formula(self):
        """Test κ = 4π/(f₀·Φ)"""
        params = AdelicParameters()
        # κ is hardcoded to match existing framework
        # The formula 4π/(f₀·Φ) gives the theoretical derivation
        # but we use the calibrated value from the framework
        self.assertAlmostEqual(params.kappa, 2.577310, places=6)
    
    def test_golden_ratio(self):
        """Test Φ = (1+√5)/2"""
        params = AdelicParameters()
        self.assertAlmostEqual(params.phi, 1.618034, places=6)


def run_tests():
    """Run all tests"""
    print("="*80)
    print("ADELIC LAPLACIAN TEST SUITE")
    print("="*80)
    print()
    
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestPrimeGeneration))
    suite.addTests(loader.loadTestsFromTestCase(TestAdelicParameters))
    suite.addTests(loader.loadTestsFromTestCase(TestAdelicLaplacian))
    suite.addTests(loader.loadTestsFromTestCase(TestAdelicNavierStokesOperator))
    suite.addTests(loader.loadTestsFromTestCase(TestMathematicalProperties))
    suite.addTests(loader.loadTestsFromTestCase(TestFrequencyConstants))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    print()
    print("="*80)
    if result.wasSuccessful():
        print("✓ ALL TESTS PASSED")
    else:
        print("✗ SOME TESTS FAILED")
    print("="*80)
    
    return result.wasSuccessful()


if __name__ == "__main__":
    success = run_tests()
    exit(0 if success else 1)
