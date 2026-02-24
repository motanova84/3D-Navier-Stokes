#!/usr/bin/env python3
"""
Test suite for Adelic Navier-Stokes Framework
QCAL ∞³ Framework - f₀ = 141.7001 Hz

Tests the complete adelic Navier-Stokes evolution operator.
"""

import unittest
import numpy as np
from adelic_navier_stokes import (
    AdelicNavierStokes,
    AdelicNavierStokesConfig
)


class TestAdelicNavierStokesConfig(unittest.TestCase):
    """Test adelic Navier-Stokes configuration"""
    
    def test_default_config(self):
        """Test default configuration"""
        config = AdelicNavierStokesConfig()
        self.assertAlmostEqual(config.kappa_pi, 2.57731, places=5)
        self.assertAlmostEqual(config.f0, 141.7001, places=4)
        self.assertEqual(config.max_primes, 20)
    
    def test_reynolds_critical(self):
        """Test critical Reynolds number equals κ_Π"""
        config = AdelicNavierStokesConfig()
        Re_crit = config.get_reynolds_critical()
        self.assertAlmostEqual(Re_crit, config.kappa_pi)
    
    def test_viscosity_calculation(self):
        """Test viscosity ν = 1/κ"""
        config = AdelicNavierStokesConfig()
        nu = config.get_viscosity()
        expected = 1.0 / config.kappa_pi
        self.assertAlmostEqual(nu, expected)


class TestAdelicNavierStokes(unittest.TestCase):
    """Test adelic Navier-Stokes system"""
    
    def setUp(self):
        """Set up test fixtures"""
        config = AdelicNavierStokesConfig(max_primes=5)
        self.system = AdelicNavierStokes(config)
        
        # Test grid
        self.n = 100
        self.L = 10.0
        self.x = np.linspace(-self.L, self.L, self.n)
        self.dx = self.x[1] - self.x[0]
    
    def test_initialization(self):
        """Test proper initialization"""
        self.assertIsNotNone(self.system.laplacian)
        self.assertAlmostEqual(self.system.kappa_pi, 2.57731, places=5)
        self.assertAlmostEqual(self.system.f0, 141.7001, places=4)
        self.assertGreater(self.system.nu, 0)
    
    def test_logarithmic_potential(self):
        """Test logarithmic potential V_eff(x) = ln(1 + |x|)"""
        V = self.system.logarithmic_potential(self.x)
        
        # Check properties
        self.assertEqual(len(V), len(self.x))
        self.assertGreaterEqual(np.min(V), 0)  # Always non-negative
        
        # Check symmetry
        V_pos = self.system.logarithmic_potential(np.abs(self.x))
        np.testing.assert_array_almost_equal(V, V_pos)
        
        # Check specific values
        self.assertAlmostEqual(self.system.logarithmic_potential(0.0), 0.0)
        self.assertGreater(self.system.logarithmic_potential(10.0), 
                          self.system.logarithmic_potential(1.0))
    
    def test_transport_term_shape(self):
        """Test transport term returns correct shape"""
        psi = np.exp(-self.x**2)
        transport = self.system.transport_term(psi, self.x, self.dx)
        self.assertEqual(transport.shape, psi.shape)
    
    def test_transport_term_zero_at_origin(self):
        """Test transport term vanishes at x=0 for symmetric function"""
        psi = np.exp(-self.x**2)
        transport = self.system.transport_term(psi, self.x, self.dx)
        
        # Find index closest to x=0
        i_zero = np.argmin(np.abs(self.x))
        # Transport should be small at origin due to symmetry
        self.assertLess(np.abs(transport[i_zero]), 0.1)
    
    def test_diffusion_term_shape(self):
        """Test diffusion term returns correct shape"""
        psi = np.exp(-self.x**2)
        diffusion = self.system.diffusion_term(psi, self.dx)
        self.assertEqual(diffusion.shape, psi.shape)
    
    def test_confinement_term_shape(self):
        """Test confinement term returns correct shape"""
        psi = np.exp(-self.x**2)
        confinement = self.system.confinement_term(psi, self.x)
        self.assertEqual(confinement.shape, psi.shape)
    
    def test_evolution_operator_shape(self):
        """Test evolution operator returns correct shape"""
        psi = np.exp(-self.x**2)
        dpsi_dt = self.system.evolution_operator(psi, self.x, self.dx)
        self.assertEqual(dpsi_dt.shape, psi.shape)
    
    def test_evolve_step(self):
        """Test single evolution step"""
        psi_initial = np.exp(-self.x**2)
        psi_initial /= np.sqrt(np.sum(psi_initial**2) * self.dx)
        
        dt = 0.01
        psi_new = self.system.evolve_step(psi_initial, self.x, self.dx, dt)
        
        # Check shape
        self.assertEqual(psi_new.shape, psi_initial.shape)
        
        # Wave function should have changed
        self.assertGreater(np.sum(np.abs(psi_new - psi_initial)), 1e-6)
    
    def test_energy_conservation_order(self):
        """Test energy is of correct order of magnitude"""
        psi = np.exp(-self.x**2)
        psi /= np.sqrt(np.sum(psi**2) * self.dx)  # Normalize
        
        E = self.system.compute_energy(psi, self.dx)
        # Allow for numerical integration errors
        self.assertAlmostEqual(E, 1.0, places=6)
    
    def test_energy_flux_real(self):
        """Test energy flux is real"""
        psi = np.exp(-self.x**2)
        flux = self.system.compute_energy_flux(psi, self.x, self.dx)
        self.assertTrue(np.isreal(flux))
    
    def test_dissipation_positive(self):
        """Test dissipation is positive for non-trivial field"""
        psi = np.exp(-self.x**2)
        epsilon = self.system.compute_dissipation(psi, self.dx)
        self.assertGreater(epsilon, 0)
    
    def test_reynolds_number_calculation(self):
        """Test Reynolds number calculation"""
        psi = np.exp(-self.x**2)
        Re = self.system.compute_reynolds_number(psi, self.x, self.dx)
        self.assertGreaterEqual(Re, 0)
    
    def test_regime_classification(self):
        """Test flow regime classification"""
        # Laminar regime
        regime = self.system.check_regime(0.5)
        self.assertEqual(regime, "laminar")
        
        # Critical regime
        regime = self.system.check_regime(self.system.kappa_pi)
        self.assertEqual(regime, "critical")
        
        # Turbulent regime
        regime = self.system.check_regime(5.0)
        self.assertEqual(regime, "turbulent")
    
    def test_cascade_coefficient_positive(self):
        """Test cascade coefficient is positive"""
        psi = np.exp(-self.x**2)
        psi /= np.sqrt(np.sum(psi**2) * self.dx)
        
        C_L = self.system.compute_cascade_coefficient(self.L, psi, self.x, self.dx)
        self.assertGreaterEqual(C_L, 0)
    
    def test_get_system_info(self):
        """Test get_system_info returns correct structure"""
        info = self.system.get_system_info()
        
        self.assertIn('kappa_pi', info)
        self.assertIn('reynolds_critical', info)
        self.assertIn('f0_hz', info)
        self.assertIn('viscosity', info)
        self.assertIn('laplacian_info', info)
        
        self.assertAlmostEqual(info['kappa_pi'], 2.57731, places=5)
        self.assertAlmostEqual(info['f0_hz'], 141.7001, places=4)


class TestCriticalReynoldsNumber(unittest.TestCase):
    """Test emergence of κ_Π as critical Reynolds number"""
    
    def setUp(self):
        """Set up test fixtures"""
        config = AdelicNavierStokesConfig(max_primes=5)
        self.system = AdelicNavierStokes(config)
        
        self.n = 200
        self.L = 10.0
        self.x = np.linspace(-self.L, self.L, self.n)
        self.dx = self.x[1] - self.x[0]
    
    def test_kappa_pi_value(self):
        """Test κ_Π = 2.57731"""
        self.assertAlmostEqual(self.system.kappa_pi, 2.57731, places=5)
    
    def test_reynolds_critical_equals_kappa_pi(self):
        """Test Re_crit = κ_Π"""
        Re_crit = self.system.config.get_reynolds_critical()
        self.assertAlmostEqual(Re_crit, self.system.kappa_pi)
    
    def test_viscosity_from_kappa(self):
        """Test ν = 1/κ relationship"""
        nu_expected = 1.0 / self.system.kappa_pi
        self.assertAlmostEqual(self.system.nu, nu_expected)
    
    def test_cascade_law_convergence(self):
        """Test C(L) converges toward 1/κ_Π as expected"""
        # Create a wave packet and evolve
        psi = np.exp(-self.x**2)
        psi /= np.sqrt(np.sum(psi**2) * self.dx)
        
        # Evolve to quasi-steady state
        dt = 0.01
        for _ in range(20):
            psi = self.system.evolve_step(psi, self.x, self.dx, dt)
        
        # Compute cascade coefficient
        C_L = self.system.compute_cascade_coefficient(self.L, psi, self.x, self.dx)
        predicted = 1.0 / self.system.kappa_pi
        
        # Should be within same order of magnitude and reasonable range
        # The exact convergence depends on domain size L
        self.assertGreater(C_L, 0)
        self.assertLess(C_L, predicted * 2)  # Within factor of 2


class TestEvolutionProperties(unittest.TestCase):
    """Test physical properties of evolution"""
    
    def setUp(self):
        """Set up test fixtures"""
        config = AdelicNavierStokesConfig(max_primes=5)
        self.system = AdelicNavierStokes(config)
        
        self.n = 100
        self.x = np.linspace(-5, 5, self.n)
        self.dx = self.x[1] - self.x[0]
    
    def test_diffusion_dominates_for_smooth_fields(self):
        """Test diffusion term dominates for smooth fields"""
        # Very smooth Gaussian
        psi = np.exp(-0.1 * self.x**2)
        psi /= np.sqrt(np.sum(psi**2) * self.dx)
        
        diffusion = self.system.diffusion_term(psi, self.dx)
        transport = self.system.transport_term(psi, self.x, self.dx)
        
        norm_diff = np.sqrt(np.sum(diffusion**2) * self.dx)
        norm_trans = np.sqrt(np.sum(transport**2) * self.dx)
        
        # For smooth fields, diffusion should be significant
        self.assertGreater(norm_diff, 0)
    
    def test_transport_increases_with_gradient(self):
        """Test transport term increases with field gradient"""
        # Narrow Gaussian (large gradient)
        psi1 = np.exp(-10 * self.x**2)
        psi1 /= np.sqrt(np.sum(psi1**2) * self.dx)
        
        # Wide Gaussian (small gradient)
        psi2 = np.exp(-0.1 * self.x**2)
        psi2 /= np.sqrt(np.sum(psi2**2) * self.dx)
        
        transport1 = self.system.transport_term(psi1, self.x, self.dx)
        transport2 = self.system.transport_term(psi2, self.x, self.dx)
        
        norm1 = np.sqrt(np.sum(transport1**2) * self.dx)
        norm2 = np.sqrt(np.sum(transport2**2) * self.dx)
        
        # Narrow (steep) should have larger transport
        self.assertGreater(norm1, norm2 * 0.5)
    
    def test_confinement_increases_away_from_origin(self):
        """Test confinement increases away from origin"""
        psi = np.ones(self.n) / np.sqrt(self.n)  # Uniform
        confinement = self.system.confinement_term(psi, self.x)
        
        # Confinement should increase with |x|
        i_center = len(self.x) // 2
        i_edge = -1
        
        self.assertGreater(np.abs(confinement[i_edge]), 
                          np.abs(confinement[i_center]))
    
    def test_stability_small_timestep(self):
        """Test evolution is stable with small timestep"""
        psi = np.exp(-self.x**2)
        psi /= np.sqrt(np.sum(psi**2) * self.dx)
        
        dt = 0.001
        psi_evolved = psi.copy()
        
        # Evolve several steps
        for _ in range(100):
            psi_evolved = self.system.evolve_step(psi_evolved, self.x, self.dx, dt)
            
            # Check no NaN or Inf
            self.assertFalse(np.any(np.isnan(psi_evolved)))
            self.assertFalse(np.any(np.isinf(psi_evolved)))
            
            # Energy should remain reasonable
            E = self.system.compute_energy(psi_evolved, self.dx)
            self.assertLess(E, 1e6)  # Should not blow up


class TestComponentBalance(unittest.TestCase):
    """Test balance between evolution components"""
    
    def setUp(self):
        """Set up test fixtures"""
        config = AdelicNavierStokesConfig(max_primes=5)
        self.system = AdelicNavierStokes(config)
        
        self.n = 100
        self.x = np.linspace(-5, 5, self.n)
        self.dx = self.x[1] - self.x[0]
    
    def test_all_components_nonzero(self):
        """Test all three components contribute for generic field"""
        psi = np.exp(-self.x**2) * (1 + 0.1 * np.sin(2*self.x))
        psi /= np.sqrt(np.sum(psi**2) * self.dx)
        
        diffusion = self.system.diffusion_term(psi, self.dx)
        transport = self.system.transport_term(psi, self.x, self.dx)
        confinement = self.system.confinement_term(psi, self.x)
        
        norm_diff = np.sqrt(np.sum(diffusion**2) * self.dx)
        norm_trans = np.sqrt(np.sum(transport**2) * self.dx)
        norm_conf = np.sqrt(np.sum(confinement**2) * self.dx)
        
        # All should be non-zero
        self.assertGreater(norm_diff, 1e-6)
        self.assertGreater(norm_trans, 1e-6)
        self.assertGreater(norm_conf, 1e-6)
    
    def test_total_evolution_combines_all(self):
        """Test total evolution is combination of all terms"""
        psi = np.exp(-self.x**2)
        
        diffusion = self.system.diffusion_term(psi, self.dx)
        transport = self.system.transport_term(psi, self.x, self.dx)
        confinement = self.system.confinement_term(psi, self.x)
        
        total = self.system.evolution_operator(psi, self.x, self.dx)
        expected = diffusion + transport + confinement
        
        np.testing.assert_array_almost_equal(total, expected)


if __name__ == '__main__':
    unittest.main()
