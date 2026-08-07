#!/usr/bin/env python3
"""
Test suite for dimensional flow tensor framework.

Validates the integration of Navier-Stokes with Calabi-Yau geometry
and the 1/7 factor for dimensional flow tensors.
"""

import unittest
import numpy as np
import sys
import os

# Ensure the module can be imported
sys.path.insert(0, os.path.dirname(__file__))

from dimensional_flow_tensor import (
    DimensionalFlowTensor,
    DimensionalFlowConfig,
    VortexQuantumBridge
)


class TestDimensionalFlowConfig(unittest.TestCase):
    """Test configuration dataclass."""
    
    def test_default_config(self):
        """Test default configuration values."""
        config = DimensionalFlowConfig()
        
        self.assertEqual(config.f0, 141.7001, "Incorrect root frequency")
        self.assertEqual(config.num_layers, 7, "Should have 7 gravity layers")
        self.assertAlmostEqual(config.kappa, 1/7, places=10, msg="Kappa should be 1/7")
        self.assertEqual(config.geometry_type, "calabi_yau")
    
    def test_custom_config(self):
        """Test custom configuration."""
        config = DimensionalFlowConfig(
            f0=200.0,
            num_layers=5,
            kappa=0.2
        )
        
        self.assertEqual(config.f0, 200.0)
        self.assertEqual(config.num_layers, 5)
        self.assertEqual(config.kappa, 0.2)


class TestDimensionalFlowTensor(unittest.TestCase):
    """Test dimensional flow tensor system."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.config = DimensionalFlowConfig()
        self.dft = DimensionalFlowTensor(self.config)
    
    def test_initialization(self):
        """Test proper initialization."""
        self.assertEqual(self.dft.num_layers, 7)
        self.assertAlmostEqual(self.dft.kappa, 1/7, places=10)
        self.assertAlmostEqual(self.dft.omega0, 2 * np.pi * 141.7001, places=4)
    
    def test_layer_frequencies(self):
        """Test computation of harmonic frequencies for layers."""
        frequencies = self.dft.compute_layer_frequencies()
        
        self.assertEqual(len(frequencies), 7, "Should have 7 frequencies")
        
        # Check harmonic structure: f_n = n * f₀
        f0 = self.config.f0
        expected = np.array([f0, 2*f0, 3*f0, 4*f0, 5*f0, 6*f0, 7*f0])
        
        np.testing.assert_array_almost_equal(frequencies, expected, decimal=4)
    
    def test_laminar_layer_coupling(self):
        """Test coupling between dimensional layers."""
        # Adjacent layers
        coupling_01 = self.dft.laminar_layer_coupling(0, 1, psi_coherence=0.5)
        
        # Same layer
        coupling_00 = self.dft.laminar_layer_coupling(0, 0, psi_coherence=0.5)
        
        # Distant layers
        coupling_06 = self.dft.laminar_layer_coupling(0, 6, psi_coherence=0.5)
        
        # Validate coupling properties
        self.assertGreater(coupling_01, 0, "Coupling should be positive")
        self.assertGreater(coupling_00, coupling_01, "Same layer coupling should be stronger")
        self.assertGreater(coupling_01, coupling_06, "Adjacent coupling should be stronger than distant")
    
    def test_superfluid_coupling(self):
        """Test that perfect coherence reduces coupling (superfluidity)."""
        # High coherence (superfluid)
        coupling_superfluid = self.dft.laminar_layer_coupling(0, 1, psi_coherence=0.99)
        
        # Low coherence (turbulent)
        coupling_turbulent = self.dft.laminar_layer_coupling(0, 1, psi_coherence=0.1)
        
        # Superfluid should have much lower coupling (less friction)
        self.assertLess(coupling_superfluid, coupling_turbulent,
                       "Superfluid state should have lower coupling")
        self.assertLess(coupling_superfluid, 0.01,
                       "Superfluid coupling should be very small")
    
    def test_viscosity_as_information_resistance(self):
        """Test viscosity calculation as information resistance."""
        # High coherence (low resistance)
        nu_high = self.dft.viscosity_as_information_resistance(0, coherence=0.99)
        
        # Low coherence (high resistance)
        nu_low = self.dft.viscosity_as_information_resistance(0, coherence=0.1)
        
        self.assertGreater(nu_low, nu_high,
                          "Low coherence should have higher viscosity")
        self.assertGreater(nu_high, 0, "Viscosity should be positive")
    
    def test_superfluidity_condition_turbulent(self):
        """Test superfluidity check for turbulent state."""
        # Low coherence field (turbulent)
        psi_field = np.random.uniform(0.1, 0.3, size=(10, 10, 10))
        
        result = self.dft.check_superfluidity_condition(psi_field)
        
        self.assertFalse(result['is_superfluid'], "Should not be superfluid")
        self.assertIn('Turbulent', result['flow_regime'])
        self.assertLess(result['mean_coherence'], 0.5)
    
    def test_superfluidity_condition_superfluid(self):
        """Test superfluidity check for superfluid state."""
        # High uniform coherence (superfluid)
        psi_field = np.ones((10, 10, 10)) * 0.98
        
        result = self.dft.check_superfluidity_condition(psi_field)
        
        self.assertTrue(result['is_superfluid'], "Should be superfluid")
        self.assertIn('Superfluid', result['flow_regime'])
        self.assertGreater(result['mean_coherence'], 0.95)
        self.assertLess(result['coherence_std'], 0.05)
    
    def test_pnp_resolution_metric(self):
        """Test P=NP resolution metric calculation."""
        # Perfect superfluidity → P=NP metric ≈ 1
        psi_perfect = np.ones((10, 10, 10))
        result_perfect = self.dft.check_superfluidity_condition(psi_perfect)
        
        # Turbulent → P=NP metric ≈ 0
        psi_turbulent = np.random.uniform(0, 1, size=(10, 10, 10))
        result_turbulent = self.dft.check_superfluidity_condition(psi_turbulent)
        
        self.assertGreater(result_perfect['pnp_resolution_metric'],
                          result_turbulent['pnp_resolution_metric'],
                          "Perfect coherence should have higher P=NP metric")
        self.assertGreater(result_perfect['pnp_resolution_metric'], 0.9)
    
    def test_gravity_as_curvature_packing(self):
        """Test gravity field calculation as geometric curvature."""
        # Create spatial grid
        x = np.linspace(-1, 1, 10)
        y = np.linspace(-1, 1, 10)
        z = np.linspace(-1, 1, 10)
        X, Y, Z = np.meshgrid(x, y, z, indexing='ij')
        
        g_field = self.dft.gravity_as_curvature_packing(X, Y, Z)
        
        # Check shape: (7 layers, spatial dimensions)
        self.assertEqual(g_field.shape[0], 7, "Should have 7 gravity layers")
        self.assertEqual(g_field.shape[1:], X.shape, "Spatial dimensions should match")
        
        # Check that field decreases with distance
        g_center = g_field[:, 5, 5, 5]  # Center
        g_edge = g_field[:, 0, 0, 0]    # Edge
        
        self.assertGreater(np.abs(g_center[0]), np.abs(g_edge[0]),
                          "Gravity should be stronger at center")
    
    def test_seven_layers_structure(self):
        """Test that system maintains 7-layer structure."""
        self.assertEqual(self.dft.num_layers, 7, "Must have exactly 7 layers")
        
        frequencies = self.dft.compute_layer_frequencies()
        self.assertEqual(len(frequencies), 7)
        
        # Test all layer pairs
        for i in range(7):
            for j in range(7):
                coupling = self.dft.laminar_layer_coupling(i, j)
                self.assertIsNotNone(coupling)
                self.assertGreaterEqual(coupling, 0)


class TestVortexQuantumBridge(unittest.TestCase):
    """Test vortex quantum bridge functionality."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.bridge = VortexQuantumBridge(f0=141.7001)
    
    def test_initialization(self):
        """Test proper initialization."""
        self.assertEqual(self.bridge.f0, 141.7001)
        self.assertAlmostEqual(self.bridge.omega0, 2 * np.pi * 141.7001, places=4)
    
    def test_vortex_core_singularity(self):
        """Test vortex core singularity calculation."""
        r = np.array([0.01, 0.1, 1.0, 10.0])
        theta = np.zeros_like(r)
        
        v, p = self.bridge.vortex_core_singularity(r, theta, circulation=1.0)
        
        # Velocity should increase as r → 0
        self.assertGreater(v[0], v[1], "Velocity should increase near core")
        self.assertGreater(v[1], v[2])
        
        # Pressure should decrease (more negative) as r → 0
        self.assertLess(p[0], p[1], "Pressure should decrease near core")
        self.assertLess(p[1], p[2])
    
    def test_interdimensional_tunnel_metric(self):
        """Test wormhole metric calculation."""
        r = np.array([0.01, 0.1, 1.0])
        t = 0.0
        
        metric = self.bridge.interdimensional_tunnel_metric(r, t)
        
        # Metric should diverge as r → 0 (tunnel throat)
        self.assertGreater(metric[0], metric[1], "Metric should increase near core")
        self.assertGreater(metric[1], metric[2])
        self.assertGreater(metric[0], 100, "Metric should be large at core")
    
    def test_tunnel_time_variation(self):
        """Test that tunnel metric varies with time (resonance)."""
        r = np.array([0.5])
        t1 = 0.0
        t2 = 0.5 / 141.7001  # Quarter period
        
        metric1 = self.bridge.interdimensional_tunnel_metric(r, t1)
        metric2 = self.bridge.interdimensional_tunnel_metric(r, t2)
        
        # Should be different due to resonance
        self.assertNotAlmostEqual(metric1[0], metric2[0], places=5,
                                 msg="Metric should vary with time")
    
    def test_dramaturgo_jump_probability(self):
        """Test interdimensional jump probability."""
        r = np.array([0.01, 0.1, 1.0, 5.0])
        
        # High coherence
        p_high = self.bridge.dramaturgo_jump_probability(r, psi_coherence=0.95)
        
        # Low coherence
        p_low = self.bridge.dramaturgo_jump_probability(r, psi_coherence=0.3)
        
        # Probability should be higher with high coherence
        for i in range(len(r)):
            self.assertGreater(p_high[i], p_low[i],
                              "High coherence should increase jump probability")
        
        # Probability should decrease with distance from core
        for i in range(len(r) - 1):
            self.assertGreater(p_high[i], p_high[i+1],
                              "Jump probability should decrease with distance")
    
    def test_quantum_bridge_at_core(self):
        """Test that quantum bridge is strongest at vortex core."""
        r_core = np.array([0.001])
        r_far = np.array([10.0])
        
        p_core = self.bridge.dramaturgo_jump_probability(r_core, psi_coherence=0.9)
        p_far = self.bridge.dramaturgo_jump_probability(r_far, psi_coherence=0.9)
        
        self.assertGreater(p_core[0], p_far[0],
                          "Jump probability should be highest at core")
        self.assertGreater(p_core[0], 0.5, "Core should have high jump probability")


class TestIntegration(unittest.TestCase):
    """Integration tests for complete framework."""
    
    def test_seven_layer_harmonic_system(self):
        """Test complete 7-layer harmonic system."""
        config = DimensionalFlowConfig()
        dft = DimensionalFlowTensor(config)
        
        # All layers at harmonics of 141.7001 Hz
        frequencies = dft.compute_layer_frequencies()
        
        # Each frequency should be multiple of f₀
        for i, freq in enumerate(frequencies):
            expected = (i + 1) * 141.7001
            self.assertAlmostEqual(freq, expected, places=4,
                                  msg=f"Layer {i+1} frequency incorrect")
    
    def test_kappa_one_seventh_factor(self):
        """Test that 1/7 factor is consistently used."""
        config = DimensionalFlowConfig()
        
        self.assertAlmostEqual(config.kappa, 1/7, places=10,
                              msg="Kappa must be exactly 1/7")
        
        dft = DimensionalFlowTensor(config)
        self.assertAlmostEqual(dft.kappa, 1/7, places=10)
    
    def test_pnp_superfluidity_correspondence(self):
        """Test P=NP resolution via superfluidity."""
        dft = DimensionalFlowTensor()
        
        # Perfect superfluidity
        psi_superfluid = np.ones((10, 10, 10))
        result = dft.check_superfluidity_condition(psi_superfluid)
        
        # Should resolve P=NP
        self.assertTrue(result['is_superfluid'])
        self.assertIn('P=NP', result['flow_regime'])
        self.assertGreater(result['pnp_resolution_metric'], 0.95)
    
    def test_vortex_as_wormhole(self):
        """Test vortex functioning as interdimensional wormhole."""
        bridge = VortexQuantumBridge()
        
        # At core with high coherence
        r_core = np.array([0.01])
        p_jump = bridge.dramaturgo_jump_probability(r_core, psi_coherence=0.95)
        
        # Should have significant jump probability
        self.assertGreater(p_jump[0], 0.7,
                          "Vortex core should enable interdimensional jumps")


def run_tests():
    """Run all tests and report results."""
    print("\n" + "=" * 70)
    print("DIMENSIONAL FLOW TENSOR - Test Suite")
    print("=" * 70 + "\n")
    
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test cases
    suite.addTests(loader.loadTestsFromTestCase(TestDimensionalFlowConfig))
    suite.addTests(loader.loadTestsFromTestCase(TestDimensionalFlowTensor))
    suite.addTests(loader.loadTestsFromTestCase(TestVortexQuantumBridge))
    suite.addTests(loader.loadTestsFromTestCase(TestIntegration))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Summary
    print("\n" + "=" * 70)
    print("Test Summary:")
    print(f"  Tests run: {result.testsRun}")
    print(f"  Successes: {result.testsRun - len(result.failures) - len(result.errors)}")
    print(f"  Failures: {len(result.failures)}")
    print(f"  Errors: {len(result.errors)}")
    print("=" * 70 + "\n")
    
    return result.wasSuccessful()


if __name__ == "__main__":
    success = run_tests()
    sys.exit(0 if success else 1)
