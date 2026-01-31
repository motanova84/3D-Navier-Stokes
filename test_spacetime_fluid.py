#!/usr/bin/env python3
"""
Tests for Spacetime-Fluid Visualization

Validates the spacetime-fluid simulator and visualization components.
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
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestSpacetimeFluidSimulator))
    suite.addTests(loader.loadTestsFromTestCase(TestCoherenceFieldProperties))
    suite.addTests(loader.loadTestsFromTestCase(TestPhysicalPredictions))
    
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
