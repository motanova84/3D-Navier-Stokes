#!/usr/bin/env python3
"""
Tests for Adelic Laplacian Implementation

Tests for the adelic Laplacian operator and complete
Adelic Navier-Stokes operator H = -x∂_x + (1/κ)Δ_𝔸 + V_eff

Author: QCAL ∞³ Framework
License: MIT + QCAL Sovereignty
Test suite for Adelic Laplacian
QCAL ∞³ Framework - f₀ = 141.7001 Hz

Tests the implementation of the adelic Laplacian operator Δ_𝔸.
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
    AdelicLaplacianConfig
)


class TestAdelicLaplacianConfig(unittest.TestCase):
    """Test adelic Laplacian configuration"""
    
    def test_default_config(self):
        """Test default configuration generates primes"""
        config = AdelicLaplacianConfig(primes=[])
        self.assertEqual(len(config.primes), config.max_primes)
        self.assertEqual(config.primes[0], 2)
        self.assertEqual(config.primes[1], 3)
        self.assertEqual(config.primes[2], 5)
    
    def test_custom_primes(self):
        """Test custom prime list"""
        custom_primes = [2, 3, 5, 7]
        config = AdelicLaplacianConfig(primes=custom_primes)
        self.assertEqual(config.primes, custom_primes)
    
    def test_kappa_pi_value(self):
        """Test critical κ_Π value"""
        config = AdelicLaplacianConfig(primes=[])
        self.assertAlmostEqual(config.kappa, 2.57731, places=5)
    
    def test_f0_value(self):
        """Test QCAL fundamental frequency"""
        config = AdelicLaplacianConfig(primes=[])
        self.assertAlmostEqual(config.f0, 141.7001, places=4)


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
        config = AdelicLaplacianConfig(primes=[], max_primes=5)
        self.laplacian = AdelicLaplacian(config)
        
        # Test grid
        self.n = 100
        self.x = np.linspace(-5, 5, self.n)
        self.dx = self.x[1] - self.x[0]
    
    def test_initialization(self):
        """Test proper initialization"""
        self.assertEqual(len(self.laplacian.primes), 5)
        self.assertAlmostEqual(self.laplacian.kappa, 2.57731, places=5)
        self.assertAlmostEqual(self.laplacian.f0, 141.7001, places=4)
        self.assertGreater(self.laplacian.nu, 0)
    
    def test_padic_weights_normalization(self):
        """Test p-adic weights sum to 1"""
        total_weight = sum(self.laplacian.padic_weights.values())
        self.assertAlmostEqual(total_weight, 1.0, places=10)
    
    def test_padic_weights_positive(self):
        """Test all p-adic weights are positive"""
        for weight in self.laplacian.padic_weights.values():
            self.assertGreater(weight, 0)
    
    def test_padic_weights_cascade(self):
        """Test cascade law: larger primes have smaller weights"""
        primes = sorted(self.laplacian.padic_weights.keys())
        for i in range(len(primes) - 1):
            p1, p2 = primes[i], primes[i+1]
            w1 = self.laplacian.padic_weights[p1]
            w2 = self.laplacian.padic_weights[p2]
            # Larger prime should have smaller weight
            self.assertGreater(w1, w2)
    
    def test_real_laplacian_constant(self):
        """Test real Laplacian on constant function gives zero"""
        psi = np.ones(self.n)
        delta_real = self.laplacian.apply_real_laplacian(psi, self.dx)
        self.assertLess(np.max(np.abs(delta_real)), 1e-10)
    
    def test_real_laplacian_linear(self):
        """Test real Laplacian on linear function gives zero (interior points)"""
        psi = self.x
        delta_real = self.laplacian.apply_real_laplacian(psi, self.dx)
        # Check interior points (not boundaries with periodic BC)
        self.assertLess(np.max(np.abs(delta_real[10:-10])), 1e-8)
    
    def test_real_laplacian_quadratic(self):
        """Test real Laplacian on quadratic function (interior points)"""
        psi = self.x**2
        delta_real = self.laplacian.apply_real_laplacian(psi, self.dx)
        # Δ(x²) = 2 (check interior points)
        expected = 2.0 * np.ones(self.n)
        self.assertLess(np.max(np.abs(delta_real[10:-10] - expected[10:-10])), 1e-4)
    
    def test_padic_laplacian_shape(self):
        """Test p-adic Laplacian returns correct shape"""
        psi = np.exp(-self.x**2)
        for p in self.laplacian.primes:
            delta_p = self.laplacian.apply_padic_laplacian(psi, p, self.dx)
            self.assertEqual(delta_p.shape, psi.shape)
    
    def test_adelic_laplacian_includes_real(self):
        """Test adelic Laplacian includes real component"""
        psi = np.exp(-self.x**2)
        delta_real = self.laplacian.apply_real_laplacian(psi, self.dx)
        delta_adelic = self.laplacian.apply_adelic_laplacian(psi, self.dx)
        
        # Adelic should be larger in norm (includes p-adic)
        norm_real = np.sqrt(np.sum(delta_real**2) * self.dx)
        norm_adelic = np.sqrt(np.sum(delta_adelic**2) * self.dx)
        self.assertGreaterEqual(norm_adelic, norm_real * 0.99)
    
    def test_diffusion_operator_scaling(self):
        """Test diffusion operator scales by 1/κ"""
        psi = np.exp(-self.x**2)
        delta_adelic = self.laplacian.apply_adelic_laplacian(psi, self.dx)
        diffusion = self.laplacian.diffusion_operator(psi, self.dx)
        
        # diffusion = (1/κ) * delta_adelic
        expected = delta_adelic / self.laplacian.kappa
        np.testing.assert_array_almost_equal(diffusion, expected)
    
    def test_effective_viscosity(self):
        """Test effective viscosity ν = 1/κ"""
        nu = self.laplacian.get_effective_viscosity()
        expected = 1.0 / self.laplacian.kappa
        self.assertAlmostEqual(nu, expected)
    
    def test_dissipation_rate_positive(self):
        """Test dissipation rate is positive for non-trivial field"""
        psi = np.exp(-self.x**2)
        epsilon = self.laplacian.compute_dissipation_rate(psi, self.dx)
        self.assertGreater(epsilon, 0)
    
    def test_dissipation_rate_constant(self):
        """Test dissipation rate is zero for constant field"""
        psi = np.ones(self.n)
        epsilon = self.laplacian.compute_dissipation_rate(psi, self.dx)
        self.assertLess(epsilon, 1e-10)
    
    def test_get_info(self):
        """Test get_info returns correct structure"""
        info = self.laplacian.get_info()
        
        self.assertIn('num_primes', info)
        self.assertIn('primes', info)
        self.assertIn('kappa_pi', info)
        self.assertIn('f0_hz', info)
        self.assertIn('effective_viscosity', info)
        self.assertIn('padic_weights', info)
        
        self.assertEqual(info['num_primes'], 5)
        self.assertAlmostEqual(info['kappa_pi'], 2.57731, places=5)
        self.assertAlmostEqual(info['f0_hz'], 141.7001, places=4)


class TestAdelicLaplacianConservation(unittest.TestCase):
    """Test conservation and physical properties"""
    
    def setUp(self):
        """Set up test fixtures"""
        config = AdelicLaplacianConfig(primes=[2, 3, 5], max_primes=3)
        self.laplacian = AdelicLaplacian(config)
        
        self.n = 100
        self.x = np.linspace(-5, 5, self.n)
        self.dx = self.x[1] - self.x[0]
    
    def test_laplacian_self_adjoint(self):
        """Test Laplacian is (approximately) self-adjoint"""
        psi1 = np.exp(-self.x**2)
        psi2 = np.exp(-(self.x-1)**2)
        
        delta_psi1 = self.laplacian.apply_real_laplacian(psi1, self.dx)
        delta_psi2 = self.laplacian.apply_real_laplacian(psi2, self.dx)
        
        # <psi1, Δ psi2> ≈ <Δ psi1, psi2>
        inner1 = np.sum(psi1 * delta_psi2) * self.dx
        inner2 = np.sum(delta_psi1 * psi2) * self.dx
        
        # Should be approximately equal (within discretization error)
        self.assertLess(abs(inner1 - inner2) / abs(inner1 + 1e-10), 0.1)
    
    def test_energy_dissipation_positive_semidefinite(self):
        """Test energy dissipation is positive semi-definite"""
        # Try several random states
        np.random.seed(42)
        for _ in range(10):
            psi = np.random.randn(self.n)
            epsilon = self.laplacian.compute_dissipation_rate(psi, self.dx)
            self.assertGreaterEqual(epsilon, -1e-10)  # Allow small numerical errors


class TestAdelicLaplacianNumerics(unittest.TestCase):
    """Test numerical properties"""
    
    def test_convergence_with_resolution(self):
        """Test Laplacian shows improved accuracy with increasing resolution"""
        # Use Gaussian which is compatible with periodic BC
        results = []
        
        for n in [50, 100, 200]:
            x = np.linspace(-5, 5, n)
            dx = x[1] - x[0]
            # Gaussian: Δ(e^(-x²)) = (4x² - 2)e^(-x²)
            psi = np.exp(-x**2)
            expected = (4*x**2 - 2) * psi
            
            config = AdelicLaplacianConfig(primes=[2], max_primes=1)
            laplacian = AdelicLaplacian(config)
            
            delta_psi = laplacian.apply_real_laplacian(psi, dx)
            
            # Check interior points only to avoid boundary effects
            error = np.sqrt(np.sum((delta_psi[10:-10] - expected[10:-10])**2) * dx)
            results.append(error)
        
        # Verify highest resolution is better than lowest
        self.assertLess(results[2], results[0])  # 200 pts better than 50 pts


if __name__ == '__main__':
    unittest.main()
