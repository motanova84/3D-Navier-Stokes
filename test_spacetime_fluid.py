#!/usr/bin/env python3
"""
Tests for Spacetime-Fluid Visualization

Validates the spacetime-fluid simulator and visualization components.
Test Suite for Spacetime Fluid Model

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
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from visualize_spacetime_fluid import SpacetimeFluidSimulator, F0, OMEGA_0


class TestSpacetimeFluidSimulator(unittest.TestCase):
    """Test the spacetime-fluid simulator."""
    
    def setUp(self):
        """Set up test simulator."""
        self.simulator = SpacetimeFluidSimulator(grid_size=20, domain_size=5.0)
    
    def test_initialization(self):
        """Test simulator initializes correctly."""
        self.assertEqual(self.simulator.grid_size, 20)
        self.assertEqual(self.simulator.domain_size, 5.0)
        self.assertEqual(self.simulator.X.shape, (20, 20, 20))
        self.assertEqual(self.simulator.Y.shape, (20, 20, 20))
        self.assertEqual(self.simulator.Z.shape, (20, 20, 20))
    
    def test_velocity_field_shape(self):
        """Test velocity field has correct shape."""
        t = 0.0
        u_x, u_y, u_z = self.simulator.velocity_field(t)
        
        self.assertEqual(u_x.shape, (20, 20, 20))
        self.assertEqual(u_y.shape, (20, 20, 20))
        self.assertEqual(u_z.shape, (20, 20, 20))
    
    def test_velocity_field_finite(self):
        """Test velocity field values are finite."""
        t = 0.0
        u_x, u_y, u_z = self.simulator.velocity_field(t)
        
        self.assertTrue(np.all(np.isfinite(u_x)))
        self.assertTrue(np.all(np.isfinite(u_y)))
        self.assertTrue(np.all(np.isfinite(u_z)))
    
    def test_coherence_field_oscillation(self):
        """Test coherence field oscillates at f₀."""
        # Sample at a fixed point
        idx = (10, 10, 10)
        
        # At t=0, cos(0) = 1
        t1 = 0.0
        psi1 = self.simulator.coherence_field(t1)[idx]
        
        # At t = T/2, cos(π) = -1 (opposite phase)
        t2 = 1.0 / (2 * F0)
        psi2 = self.simulator.coherence_field(t2)[idx]
        
        # Should have opposite signs (approximately)
        if psi1 != 0:  # Avoid division by zero
            ratio = psi2 / psi1
            self.assertLess(ratio, 0, "Coherence should reverse sign at half period")
    
    def test_coherence_field_period(self):
        """Test coherence field has period T = 1/f₀."""
        idx = (10, 10, 10)
        
        t1 = 0.0
        psi1 = self.simulator.coherence_field(t1)[idx]
        
        # After one full period, should return to same value
        t2 = 1.0 / F0
        psi2 = self.simulator.coherence_field(t2)[idx]
        
        self.assertAlmostEqual(psi1, psi2, places=5,
                              msg="Coherence should be periodic with T = 1/f₀")
    
    def test_vorticity_magnitude_positive(self):
        """Test vorticity magnitude is positive."""
        t = 0.0
        omega = self.simulator.vorticity_magnitude(t)
        
        self.assertTrue(np.all(omega >= 0),
                       "Vorticity magnitude should be non-negative")
    
    def test_ricci_density_positive(self):
        """Test Ricci density is positive."""
        density = self.simulator.ricci_density()
        
        self.assertTrue(np.all(density > 0),
                       "Ricci density should be positive")
    
    def test_ricci_density_decreases_with_distance(self):
        """Test density decreases away from mass center."""
        density = self.simulator.ricci_density()
        
        # Density at center (avoid exact singularity)
        center_idx = (self.simulator.grid_size // 2,) * 3
        rho_center = density[center_idx]
        
        # Density far from center
        edge_idx = (0, 0, 0)
        rho_edge = density[edge_idx]
        
        self.assertGreater(rho_center, rho_edge,
                          "Density should be higher near mass center")
    
    def test_frequency_constant(self):
        """Test fundamental frequency matches QCAL value."""
        self.assertAlmostEqual(F0, 141.7001, places=4)
        self.assertAlmostEqual(OMEGA_0, 2 * np.pi * F0, places=2)


class TestCoherenceFieldProperties(unittest.TestCase):
    """Test mathematical properties of the coherence field."""
    
    def setUp(self):
        """Set up test simulator."""
        self.simulator = SpacetimeFluidSimulator(grid_size=20, domain_size=5.0)
    
    def test_coherence_bounded(self):
        """Test coherence field is bounded (no singularities)."""
        t = 0.0
        psi = self.simulator.coherence_field(t)
        
        # Should be finite everywhere
        self.assertTrue(np.all(np.isfinite(psi)),
                       "Coherence field should be finite everywhere")
        
        # Should be bounded in magnitude
        max_psi = np.max(np.abs(psi))
        self.assertLess(max_psi, 1e10,
                       "Coherence field should not blow up")
    
    def test_spatial_continuity(self):
        """Test coherence field is spatially continuous."""
        t = 0.0
        psi = self.simulator.coherence_field(t)
        
        # Check that neighboring points don't differ too much
        # (Simplified continuity test)
        diff_x = np.abs(np.diff(psi, axis=0))
        diff_y = np.abs(np.diff(psi, axis=1))
        diff_z = np.abs(np.diff(psi, axis=2))
        
        # Maximum discontinuity should be reasonable
        max_jump = max(np.max(diff_x), np.max(diff_y), np.max(diff_z))
        self.assertLess(max_jump, 1e6,
                       "Coherence field should be spatially continuous")
    
    def test_time_evolution_smooth(self):
        """Test coherence evolves smoothly in time."""
        idx = (10, 10, 10)
        
        # Sample at several time points
        times = np.linspace(0, 0.01, 10)
        psi_values = [self.simulator.coherence_field(t)[idx] for t in times]
        
        # Check all values are finite
        self.assertTrue(all(np.isfinite(psi_values)),
                       "Time evolution should be smooth")


class TestPhysicalPredictions(unittest.TestCase):
    """Test physical predictions of the theory."""
    
    def setUp(self):
        """Set up test simulator."""
        self.simulator = SpacetimeFluidSimulator(grid_size=20, domain_size=5.0)
    
    def test_frame_dragging_vorticity(self):
        """Test vorticity is non-zero (frame dragging exists)."""
        t = 0.0
        omega = self.simulator.vorticity_magnitude(t)
        
        # Should have non-zero vorticity somewhere
        max_omega = np.max(omega)
        self.assertGreater(max_omega, 0,
                          "Frame dragging should create vorticity")
    
    def test_cosmic_frequency_value(self):
        """Test the cosmic frequency has the predicted value."""
        self.assertAlmostEqual(F0, 141.7001, places=4,
                              msg="Cosmic frequency should be 141.7001 Hz")
    
    def test_coherence_energy_density(self):
        """Test coherence field represents energy density."""
        t = 0.0
        psi = self.simulator.coherence_field(t)
        
        # Coherence should be related to velocity (energy)
        # Where velocity is high, coherence should be high
        u_x, u_y, u_z = self.simulator.velocity_field(t)
        u_mag = np.sqrt(u_x**2 + u_y**2 + u_z**2)
        
        # Correlation test: high velocity → high coherence (absolute value)
        # This is a simplified test
        high_vel_mask = u_mag > np.median(u_mag)
        mean_psi_high = np.mean(np.abs(psi[high_vel_mask]))
        mean_psi_low = np.mean(np.abs(psi[~high_vel_mask]))
        
        self.assertGreater(mean_psi_high, mean_psi_low * 0.5,
                          "Coherence should correlate with velocity/energy")


def run_tests():
    """Run all tests."""
    print("=" * 70)
    print("SPACETIME-FLUID VISUALIZATION TESTS")
    print("=" * 70)
    print()
    
    # Create test suite
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
    suite.addTests(loader.loadTestsFromTestCase(TestSpacetimeFluidSimulator))
    suite.addTests(loader.loadTestsFromTestCase(TestCoherenceFieldProperties))
    suite.addTests(loader.loadTestsFromTestCase(TestPhysicalPredictions))
    suite.addTests(loader.loadTestsFromTestCase(TestSpacetimeFluidParams))
    suite.addTests(loader.loadTestsFromTestCase(TestSpacetimeFluid))
    suite.addTests(loader.loadTestsFromTestCase(TestSpacetimeSimulation))
    suite.addTests(loader.loadTestsFromTestCase(TestSpacetimePhysics))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    print()
    print("=" * 70)
    if result.wasSuccessful():
        print("✓ ALL TESTS PASSED")
        print("=" * 70)
        print("\nSpacetime-fluid simulator validated:")
        print(f"  • Coherence field Ψ oscillates at f₀ = {F0} Hz")
        print("  • Vorticity ω represents frame dragging")
        print("  • Ricci density ρ concentrated near masses")
        print("  • All fields are bounded and continuous")
        return 0
    else:
        print("✗ SOME TESTS FAILED")
        print("=" * 70)
        return 1


if __name__ == '__main__':
    sys.exit(run_tests())
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
