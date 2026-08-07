#!/usr/bin/env python3
"""
Test Suite for Stable-by-Design DNS Framework
==============================================

Tests for the quantum-geometric regularized DNS/CFD solver.
"""

import unittest
import numpy as np
import sys
import os

# Add current directory to path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from stable_dns_framework import (
    StableByDesignDNS,
    StableDNSConfig,
    create_taylor_green_initial_conditions
)


class TestStableDNSConfig(unittest.TestCase):
    """Test configuration dataclass"""
    
    def test_default_config(self):
        """Test default configuration values"""
        config = StableDNSConfig()
        
        self.assertEqual(config.N, 64)
        self.assertEqual(config.L, 2 * np.pi)
        self.assertEqual(config.dt, 0.001)
        self.assertEqual(config.T_max, 10.0)
        self.assertEqual(config.nu, 1e-3)
        self.assertTrue(config.use_quantum_regularization)
        
    def test_derived_quantities(self):
        """Test that derived quantities are computed correctly"""
        config = StableDNSConfig(N=32, L=2*np.pi, T_max=5.0, dt=0.01)
        
        expected_dx = (2 * np.pi) / 32
        expected_n_steps = int(5.0 / 0.01)
        
        self.assertAlmostEqual(config.dx, expected_dx, places=10)
        self.assertEqual(config.n_steps, expected_n_steps)
        
    def test_custom_config(self):
        """Test custom configuration"""
        config = StableDNSConfig(
            N=128,
            T_max=20.0,
            nu=5e-4,
            use_quantum_regularization=False,
            phi_coupling_strength=0.5
        )
        
        self.assertEqual(config.N, 128)
        self.assertEqual(config.T_max, 20.0)
        self.assertEqual(config.nu, 5e-4)
        self.assertFalse(config.use_quantum_regularization)
        self.assertEqual(config.phi_coupling_strength, 0.5)


class TestStableByDesignDNS(unittest.TestCase):
    """Test DNS solver"""
    
    def setUp(self):
        """Setup test solver"""
        config = StableDNSConfig(
            N=16,  # Small for fast tests
            T_max=0.1,
            dt=0.001,
            monitor_interval=5,
            use_quantum_regularization=True
        )
        self.solver = StableByDesignDNS(config)
        
    def test_initialization(self):
        """Test solver initialization"""
        self.assertIsNotNone(self.solver.config)
        self.assertIsNotNone(self.solver.KX)
        self.assertIsNotNone(self.solver.KY)
        self.assertIsNotNone(self.solver.KZ)
        self.assertIsNotNone(self.solver.K2)
        self.assertIsNotNone(self.solver.phi_tensor)
        
    def test_spectral_grid_setup(self):
        """Test spectral grid is properly configured"""
        N = self.solver.config.N
        
        self.assertEqual(self.solver.X.shape, (N, N, N))
        self.assertEqual(self.solver.KX.shape, (N, N, N))
        self.assertEqual(self.solver.K2.shape, (N, N, N))
        
        # Check that K2[0,0,0] is set to avoid division by zero
        self.assertEqual(self.solver.K2[0, 0, 0], 1)
        
    def test_quantum_regularizer_initialization(self):
        """Test quantum regularizer is properly initialized"""
        self.assertIsNotNone(self.solver.phi_tensor)
        self.assertEqual(self.solver.phi_tensor.params.f0, 141.7001)
        
    def test_quantum_regularizer_disabled(self):
        """Test that quantum regularizer can be disabled"""
        config = StableDNSConfig(
            N=16,
            T_max=0.1,
            use_quantum_regularization=False
        )
        solver = StableByDesignDNS(config)
        
        self.assertIsNone(solver.phi_tensor)
        
    def test_initial_conditions(self):
        """Test setting initial conditions"""
        u0, v0, w0 = create_taylor_green_initial_conditions(
            self.solver.X, self.solver.Y, self.solver.Z
        )
        
        self.solver.set_initial_conditions(u0, v0, w0)
        
        self.assertIsNotNone(self.solver.u_hat)
        self.assertIsNotNone(self.solver.v_hat)
        self.assertIsNotNone(self.solver.w_hat)
        self.assertIsNotNone(self.solver.u)
        self.assertIsNotNone(self.solver.v)
        self.assertIsNotNone(self.solver.w)
        
    def test_divergence_free_projection(self):
        """Test that velocity field is divergence-free after projection"""
        u0, v0, w0 = create_taylor_green_initial_conditions(
            self.solver.X, self.solver.Y, self.solver.Z
        )
        
        self.solver.set_initial_conditions(u0, v0, w0)
        
        # Compute divergence in spectral space
        div_hat = 1j * (self.solver.KX * self.solver.u_hat + 
                       self.solver.KY * self.solver.v_hat + 
                       self.solver.KZ * self.solver.w_hat)
        
        div_phys = np.real(np.fft.ifftn(div_hat))
        
        # Check that divergence is numerically zero
        self.assertLess(np.max(np.abs(div_phys)), 1e-12)
        
    def test_energy_computation(self):
        """Test energy computation"""
        u0, v0, w0 = create_taylor_green_initial_conditions(
            self.solver.X, self.solver.Y, self.solver.Z
        )
        
        self.solver.set_initial_conditions(u0, v0, w0)
        
        E = self.solver._compute_energy()
        
        self.assertGreater(E, 0)
        self.assertLess(E, np.inf)
        
    def test_enstrophy_computation(self):
        """Test enstrophy computation"""
        u0, v0, w0 = create_taylor_green_initial_conditions(
            self.solver.X, self.solver.Y, self.solver.Z
        )
        
        self.solver.set_initial_conditions(u0, v0, w0)
        
        enstrophy = self.solver._compute_enstrophy()
        
        self.assertGreater(enstrophy, 0)
        self.assertLess(enstrophy, np.inf)
        
    def test_nonlinear_term_computation(self):
        """Test nonlinear term computation"""
        u0, v0, w0 = create_taylor_green_initial_conditions(
            self.solver.X, self.solver.Y, self.solver.Z
        )
        
        Nx, Ny, Nz = self.solver._compute_nonlinear_term(u0, v0, w0)
        
        self.assertEqual(Nx.shape, u0.shape)
        self.assertEqual(Ny.shape, v0.shape)
        self.assertEqual(Nz.shape, w0.shape)
        
    def test_quantum_coupling_computation(self):
        """Test quantum coupling term computation"""
        u0, v0, w0 = create_taylor_green_initial_conditions(
            self.solver.X, self.solver.Y, self.solver.Z
        )
        
        t = 0.0
        Qx, Qy, Qz = self.solver._compute_quantum_coupling(t, u0, v0, w0)
        
        self.assertEqual(Qx.shape, u0.shape)
        self.assertEqual(Qy.shape, v0.shape)
        self.assertEqual(Qz.shape, w0.shape)
        
    def test_quantum_coupling_disabled(self):
        """Test that quantum coupling is zero when disabled"""
        config = StableDNSConfig(
            N=16,
            T_max=0.1,
            use_quantum_regularization=False
        )
        solver = StableByDesignDNS(config)
        
        u0, v0, w0 = create_taylor_green_initial_conditions(
            solver.X, solver.Y, solver.Z
        )
        
        t = 0.0
        Qx, Qy, Qz = solver._compute_quantum_coupling(t, u0, v0, w0)
        
        self.assertEqual(np.max(np.abs(Qx)), 0.0)
        self.assertEqual(np.max(np.abs(Qy)), 0.0)
        self.assertEqual(np.max(np.abs(Qz)), 0.0)
        
    def test_single_time_step(self):
        """Test single RK4 time step"""
        u0, v0, w0 = create_taylor_green_initial_conditions(
            self.solver.X, self.solver.Y, self.solver.Z
        )
        
        self.solver.set_initial_conditions(u0, v0, w0)
        
        E0 = self.solver._compute_energy()
        
        self.solver._rk4_step(0.0)
        
        E1 = self.solver._compute_energy()
        
        # Energy should change (decrease due to viscosity)
        self.assertNotEqual(E0, E1)
        
    def test_short_simulation(self):
        """Test short simulation runs without errors"""
        u0, v0, w0 = create_taylor_green_initial_conditions(
            self.solver.X, self.solver.Y, self.solver.Z
        )
        
        self.solver.set_initial_conditions(u0, v0, w0)
        
        results = self.solver.run(verbose=False)
        
        self.assertIsNotNone(results)
        self.assertIn('time', results)
        self.assertIn('energy', results)
        self.assertIn('enstrophy', results)
        self.assertIn('blow_up', results)
        
    def test_diagnostics_updated(self):
        """Test that diagnostics are properly updated"""
        u0, v0, w0 = create_taylor_green_initial_conditions(
            self.solver.X, self.solver.Y, self.solver.Z
        )
        
        self.solver.set_initial_conditions(u0, v0, w0)
        
        results = self.solver.run(verbose=False)
        
        # Check that diagnostics have been recorded
        self.assertGreater(results['step_count'], 0)
        self.assertGreater(results['energy'][0], 0)
        
    def test_stability_indicator(self):
        """Test stability indicator computation"""
        # Use lower coupling strength for this test to ensure stability
        self.solver.config.phi_coupling_strength = 0.01
        
        u0, v0, w0 = create_taylor_green_initial_conditions(
            self.solver.X, self.solver.Y, self.solver.Z
        )
        
        self.solver.set_initial_conditions(u0, v0, w0)
        
        results = self.solver.run(verbose=False)
        
        # Check that stability indicator is computed (can be any value)
        # The actual value depends on coupling strength
        max_indicator = np.max(results['stability_indicator'][:results['step_count']])
        self.assertGreater(max_indicator, 0.0)
        self.assertLess(max_indicator, np.inf)


class TestTaylorGreenVortex(unittest.TestCase):
    """Test Taylor-Green vortex initial conditions"""
    
    def test_taylor_green_creation(self):
        """Test Taylor-Green vortex generation"""
        N = 16
        L = 2 * np.pi
        x = np.linspace(0, L, N, endpoint=False)
        X, Y, Z = np.meshgrid(x, x, x, indexing='ij')
        
        u, v, w = create_taylor_green_initial_conditions(X, Y, Z, U0=1.0)
        
        self.assertEqual(u.shape, (N, N, N))
        self.assertEqual(v.shape, (N, N, N))
        self.assertEqual(w.shape, (N, N, N))
        
    def test_taylor_green_properties(self):
        """Test Taylor-Green vortex satisfies expected properties"""
        N = 32
        L = 2 * np.pi
        x = np.linspace(0, L, N, endpoint=False)
        X, Y, Z = np.meshgrid(x, x, x, indexing='ij')
        
        u, v, w = create_taylor_green_initial_conditions(X, Y, Z, U0=1.0)
        
        # Check periodicity (u(0) ≈ u(L))
        self.assertAlmostEqual(np.mean(u[0, :, :]), np.mean(u[-1, :, :]), places=5)
        self.assertAlmostEqual(np.mean(v[:, 0, :]), np.mean(v[:, -1, :]), places=5)
        
        # Check that w = 0
        self.assertAlmostEqual(np.max(np.abs(w)), 0.0, places=10)
        
        # Check energy is positive
        E = 0.5 * np.mean(u**2 + v**2 + w**2)
        self.assertGreater(E, 0)


class TestQuantumRegularization(unittest.TestCase):
    """Test quantum regularization effects"""
    
    def test_quantum_vs_classical(self):
        """Test that quantum regularization affects simulation"""
        config = StableDNSConfig(
            N=16,
            T_max=0.5,
            dt=0.001,
            monitor_interval=10,
            use_quantum_regularization=False
        )
        
        # Classical simulation
        solver_classical = StableByDesignDNS(config)
        u0, v0, w0 = create_taylor_green_initial_conditions(
            solver_classical.X, solver_classical.Y, solver_classical.Z
        )
        solver_classical.set_initial_conditions(u0, v0, w0)
        results_classical = solver_classical.run(verbose=False)
        
        # Quantum simulation
        config.use_quantum_regularization = True
        config.phi_coupling_strength = 0.1
        solver_quantum = StableByDesignDNS(config)
        solver_quantum.set_initial_conditions(u0, v0, w0)
        results_quantum = solver_quantum.run(verbose=False)
        
        # Energy evolution should differ
        E_classical = results_classical['energy'][:results_classical['step_count']]
        E_quantum = results_quantum['energy'][:results_quantum['step_count']]
        
        # Should have different energy profiles (not testing which is higher/lower,
        # just that they're different due to quantum coupling)
        energy_difference = np.max(np.abs(E_classical - E_quantum))
        self.assertGreater(energy_difference, 1e-10)
        
    def test_quantum_energy_rate(self):
        """Test that quantum coupling energy rate is recorded"""
        config = StableDNSConfig(
            N=16,
            T_max=0.2,
            dt=0.001,
            monitor_interval=5,
            use_quantum_regularization=True
        )
        
        solver = StableByDesignDNS(config)
        u0, v0, w0 = create_taylor_green_initial_conditions(
            solver.X, solver.Y, solver.Z
        )
        solver.set_initial_conditions(u0, v0, w0)
        results = solver.run(verbose=False)
        
        # Check that phi_energy_rate is being recorded
        phi_rate = results['phi_energy_rate'][:results['step_count']]
        
        # Should have non-zero values (coupling is active)
        self.assertGreater(np.max(np.abs(phi_rate)), 0.0)


def run_tests():
    """Run all tests"""
    print("\n" + "="*70)
    print("  TEST SUITE: STABLE-BY-DESIGN DNS FRAMEWORK")
    print("  Quantum-Geometric Regularization via Φ_ij(Ψ)")
    print("="*70 + "\n")
    
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add test cases
    suite.addTests(loader.loadTestsFromTestCase(TestStableDNSConfig))
    suite.addTests(loader.loadTestsFromTestCase(TestStableByDesignDNS))
    suite.addTests(loader.loadTestsFromTestCase(TestTaylorGreenVortex))
    suite.addTests(loader.loadTestsFromTestCase(TestQuantumRegularization))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Print summary
    print("\n" + "="*70)
    if result.wasSuccessful():
        print("  ✓ ALL TESTS PASSED")
        print(f"  {result.testsRun} tests completed successfully")
    else:
        print("  ✗ SOME TESTS FAILED")
        print(f"  Failures: {len(result.failures)}")
        print(f"  Errors: {len(result.errors)}")
    print("="*70 + "\n")
    
    return result.wasSuccessful()


if __name__ == "__main__":
    success = run_tests()
    exit(0 if success else 1)
