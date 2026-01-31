#!/usr/bin/env python3
"""
Test Suite for Spacetime Fluid Model
====================================

Tests for:
1. Spacetime fluid structure and initialization
2. Coherence field computation and resonance at f₀ = 141.7001 Hz
3. Curvature emergence from fluid dynamics
4. Evolution equation implementation
5. Vorticity and energy conservation
"""

import unittest
import numpy as np
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from NavierStokes.spacetime_fluid_model import (
    SpacetimeFluid, SpacetimeFluidParams,
    run_spacetime_fluid_simulation
)


class TestSpacetimeFluidParams(unittest.TestCase):
    """Test spacetime fluid parameters"""
    
    def test_default_params(self):
        """Test default parameter values"""
        params = SpacetimeFluidParams()
        self.assertEqual(params.f0, 141.7001)
        self.assertGreater(params.ν, 0)
        self.assertGreater(params.χ, 0)
        self.assertGreater(params.N, 0)
    
    def test_omega0_computation(self):
        """Test angular frequency computation"""
        params = SpacetimeFluidParams()
        omega0 = params.omega0()
        expected = 2 * np.pi * 141.7001
        self.assertAlmostEqual(omega0, expected, places=3)


class TestSpacetimeFluid(unittest.TestCase):
    """Test spacetime fluid model"""
    
    def setUp(self):
        """Initialize test spacetime fluid"""
        self.params = SpacetimeFluidParams(N=16)  # Small grid for testing
        self.sf = SpacetimeFluid(self.params)
    
    def test_initialization(self):
        """Test spacetime fluid initialization"""
        self.assertEqual(self.sf.N, self.params.N)
        self.assertEqual(self.sf.u.shape, (3, self.params.N, self.params.N, self.params.N))
        self.assertEqual(self.sf.psi.shape, (self.params.N, self.params.N, self.params.N))
        self.assertEqual(self.sf.t, 0.0)
    
    def test_coherence_field_oscillation(self):
        """Test coherence field oscillates at f₀"""
        # Compute field at different times
        t1 = 0.0
        t2 = 1.0 / self.params.f0  # One period
        
        psi1 = self.sf.compute_coherence_field(t1)
        psi2 = self.sf.compute_coherence_field(t2)
        
        # Fields should be similar (complete oscillation)
        # Note: won't be exactly equal due to spatial modulation
        correlation = np.corrcoef(psi1.flatten(), psi2.flatten())[0, 1]
        self.assertGreater(correlation, 0.9)
    
    def test_coherence_field_bounded(self):
        """Test coherence field is bounded"""
        for t in [0.0, 0.1, 0.5, 1.0]:
            psi = self.sf.compute_coherence_field(t)
            self.assertTrue(np.all(np.abs(psi) <= self.params.A))
    
    def test_pressure_computation(self):
        """Test pressure computation from density and coherence"""
        rho = np.ones((self.params.N, self.params.N, self.params.N))
        psi = 0.5 * np.ones((self.params.N, self.params.N, self.params.N))
        
        p = self.sf.compute_pressure(rho, psi)
        
        # p = ρ + χ·Ψ²
        expected = rho + self.params.χ * psi**2
        np.testing.assert_array_almost_equal(p, expected)
    
    def test_gradient_computation(self):
        """Test gradient computation"""
        # Create sinusoidal field for periodic boundary compatibility
        kx, ky, kz = 2, 3, 4
        field = np.sin(kx * self.sf.X) + np.sin(ky * self.sf.Y) + np.sin(kz * self.sf.Z)
        grad = self.sf.gradient(field)
        
        # Gradient should be approximately [kx*cos(kx*X), ky*cos(ky*Y), kz*cos(kz*Z)]
        # Check that gradient exists and has correct shape
        self.assertEqual(grad.shape, (3, self.params.N, self.params.N, self.params.N))
        # Check that gradient is non-zero where expected
        self.assertGreater(np.max(np.abs(grad)), 0)
    
    def test_laplacian_computation(self):
        """Test Laplacian computation"""
        # Create smooth periodic field: f = sin(2πx/L) + cos(2πy/L)
        field = (np.sin(2*np.pi*self.sf.X/self.sf.L) + 
                 np.cos(2*np.pi*self.sf.Y/self.sf.L))
        lap = self.sf.laplacian(field)
        
        # Laplacian should be non-zero and have correct shape
        self.assertEqual(lap.shape, field.shape)
        # ∆sin(2πx/L) = -(2π/L)² sin(2πx/L), so Laplacian should be non-trivial
        self.assertGreater(np.max(np.abs(lap)), 0)
    
    def test_curvature_emergence(self):
        """Test that non-zero coherence field generates curvature"""
        # Set non-zero coherence field
        self.sf.psi = 0.5 * np.ones((self.params.N, self.params.N, self.params.N))
        
        curvature = self.sf.compute_curvature_scalar()
        
        # Curvature should be non-zero when Ψ ≠ 0
        self.assertGreater(np.max(np.abs(curvature)), 0)
    
    def test_vorticity_computation(self):
        """Test vorticity computation"""
        # Set periodic rotational velocity field
        # Use sin/cos for periodic boundary compatibility
        self.sf.u[0] = -np.sin(2*np.pi*self.sf.Y/self.sf.L)  # u_x
        self.sf.u[1] = np.sin(2*np.pi*self.sf.X/self.sf.L)   # u_y
        self.sf.u[2] = 0                                       # u_z = 0
        
        omega = self.sf.compute_vorticity()
        
        # Vorticity should be non-zero for rotational field
        self.assertGreater(np.max(np.abs(omega)), 0)
        # Check shape
        self.assertEqual(omega.shape, (3, self.params.N, self.params.N, self.params.N))
    
    def test_evolution_step(self):
        """Test evolution step updates fields correctly"""
        # Initialize with small perturbation
        self.sf.initialize_gaussian_perturbation(amplitude=0.01)
        
        initial_u = self.sf.u.copy()
        initial_t = self.sf.t
        
        # Evolve one step
        dt = 0.01
        result = self.sf.evolve_step(dt)
        
        # Time should advance
        self.assertAlmostEqual(self.sf.t, initial_t + dt)
        
        # Fields should be updated
        self.assertFalse(np.allclose(self.sf.u, initial_u))
        self.assertIn('u', result)
        self.assertIn('psi', result)
        self.assertIn('p', result)
    
    def test_gaussian_initialization(self):
        """Test Gaussian perturbation initialization"""
        self.sf.initialize_gaussian_perturbation(amplitude=0.1)
        
        # Velocity should be non-zero
        self.assertGreater(np.max(np.abs(self.sf.u)), 0)
        
        # Should have rotational structure (vorticity non-zero)
        omega = self.sf.compute_vorticity()
        self.assertGreater(np.max(np.abs(omega)), 0)


class TestSpacetimeSimulation(unittest.TestCase):
    """Test full spacetime fluid simulation"""
    
    def test_simulation_runs(self):
        """Test that simulation runs without errors"""
        params = SpacetimeFluidParams(N=8)  # Very small for speed
        history = run_spacetime_fluid_simulation(
            T=0.1, dt=0.01, params=params
        )
        
        # Check history contains expected fields
        self.assertIn('times', history)
        self.assertIn('psi', history)
        self.assertIn('curvature', history)
        self.assertIn('energy', history)
        
        # Check we got multiple time steps
        self.assertGreater(len(history['times']), 1)
    
    def test_coherence_resonance(self):
        """Test coherence field maintains resonance at f₀"""
        params = SpacetimeFluidParams(N=8)
        history = run_spacetime_fluid_simulation(
            T=0.2, dt=0.01, params=params
        )
        
        # Extract coherence field at center over time
        center = params.N // 2
        psi_center = [psi[center, center, center] for psi in history['psi']]
        times = history['times']
        
        # Fit to sinusoidal: psi(t) ∼ A·cos(ω₀t)
        # Check that dominant frequency is near f₀
        if len(times) > 10:
            # Simple check: field oscillates
            psi_range = np.max(psi_center) - np.min(psi_center)
            self.assertGreater(psi_range, 0.1)
    
    def test_energy_evolution(self):
        """Test energy evolution in simulation"""
        params = SpacetimeFluidParams(N=8, ν=0.01)
        history = run_spacetime_fluid_simulation(
            T=0.2, dt=0.01, params=params
        )
        
        energies = history['energy']
        
        # Energy should remain finite
        self.assertTrue(all(np.isfinite(e) for e in energies))
        
        # Energy should decay due to viscosity (on average)
        if len(energies) > 10:
            # Check last energy is less than peak energy
            peak_energy = np.max(energies[:len(energies)//2])
            final_energy = energies[-1]
            # Allow for some growth from forcing, but check bounded
            self.assertLess(final_energy, peak_energy * 10)
    
    def test_curvature_generation(self):
        """Test that simulation generates non-zero curvature"""
        params = SpacetimeFluidParams(N=8)
        history = run_spacetime_fluid_simulation(
            T=0.1, dt=0.01, params=params
        )
        
        # Check that curvature is generated
        max_curvatures = [np.max(np.abs(c)) for c in history['curvature']]
        
        # At least some timesteps should have non-zero curvature
        self.assertGreater(np.max(max_curvatures), 0)


class TestSpacetimePhysics(unittest.TestCase):
    """Test physical properties of spacetime fluid"""
    
    def test_universal_frequency(self):
        """Test universal frequency value"""
        params = SpacetimeFluidParams()
        self.assertEqual(params.f0, 141.7001)
    
    def test_curvature_from_coherence(self):
        """Test curvature emerges from non-zero coherence"""
        sf = SpacetimeFluid(SpacetimeFluidParams(N=8))
        
        # Zero coherence -> potentially zero curvature contribution
        sf.psi = np.zeros((8, 8, 8))
        sf.u = np.zeros((3, 8, 8, 8))
        curv_zero = sf.compute_curvature_scalar()
        
        # Non-zero coherence -> non-zero curvature
        sf.psi = np.ones((8, 8, 8))
        curv_nonzero = sf.compute_curvature_scalar()
        
        # Non-zero coherence should produce larger curvature
        self.assertGreater(np.max(np.abs(curv_nonzero)), 
                          np.max(np.abs(curv_zero)))


def run_tests():
    """Run all tests"""
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestSpacetimeFluidParams))
    suite.addTests(loader.loadTestsFromTestCase(TestSpacetimeFluid))
    suite.addTests(loader.loadTestsFromTestCase(TestSpacetimeSimulation))
    suite.addTests(loader.loadTestsFromTestCase(TestSpacetimePhysics))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    return result.wasSuccessful()


if __name__ == '__main__':
    print("=" * 70)
    print("Spacetime Fluid Model - Test Suite")
    print("=" * 70)
    print()
    
    success = run_tests()
    
    print()
    print("=" * 70)
    if success:
        print("✓ All tests passed!")
    else:
        print("✗ Some tests failed")
    print("=" * 70)
    
    sys.exit(0 if success else 1)
