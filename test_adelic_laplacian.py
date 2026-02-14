#!/usr/bin/env python3
"""
Test suite for Adelic Laplacian
QCAL ∞³ Framework - f₀ = 141.7001 Hz

Tests the implementation of the adelic Laplacian operator Δ_𝔸.
"""

import unittest
import numpy as np
from adelic_laplacian import (
    AdelicLaplacian,
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
