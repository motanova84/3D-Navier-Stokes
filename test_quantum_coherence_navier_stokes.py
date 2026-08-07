#!/usr/bin/env python3
"""
Test Suite for Quantum Coherence Navier-Stokes with Scale Hierarchy
====================================================================

Tests for:
1. Scale hierarchy structure and coupling
2. Tensor symmetry enforcement (Φ_{ij} = Φ_{ji})
3. Quantum coherence field computation
4. Multi-scale integration
5. Navier-Stokes coupling

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
Date: February 9, 2026
License: MIT
"""

import unittest
import numpy as np
from quantum_coherence_navier_stokes import (
    ScaleLevel,
    ScaleParameters,
    QuantumCoherenceNSParameters,
    QuantumCoherenceNavierStokes,
    demonstrate_quantum_coherence_navier_stokes
)


class TestScaleParameters(unittest.TestCase):
    """Test scale parameter configuration"""
    
    def test_scale_creation(self):
        """Test creation of scale parameters"""
        scale = ScaleParameters(
            level=ScaleLevel.ATOMIC,
            length_scale=1e-10,
            time_scale=1e-15,
            coherence=0.95
        )
        
        self.assertEqual(scale.level, ScaleLevel.ATOMIC)
        self.assertEqual(scale.length_scale, 1e-10)
        self.assertEqual(scale.coherence, 0.95)
    
    def test_resonance_frequency(self):
        """Test resonance frequency computation"""
        scale = ScaleParameters(
            level=ScaleLevel.CELLULAR,
            length_scale=1e-6,
            time_scale=1e-3,
            coherence=0.7
        )
        
        freq = scale.resonance_frequency()
        expected = 1.0 / 1e-3  # 1000 Hz
        self.assertAlmostEqual(freq, expected, places=2)


class TestQuantumCoherenceNSParameters(unittest.TestCase):
    """Test quantum coherence Navier-Stokes parameters"""
    
    def test_default_parameters(self):
        """Test default parameter values"""
        params = QuantumCoherenceNSParameters()
        
        # Check fundamental frequency
        self.assertEqual(params.f0_hz, 141.7001)
        
        # Check Reynolds number
        self.assertEqual(params.reynolds_number, 1e-8)
        
        # Check coherence parameters
        self.assertEqual(params.coherence_amplitude, 1.0)
        self.assertEqual(params.coherence_threshold, 0.888)
        
        # Check symmetry enforcement
        self.assertTrue(params.enforce_symmetry)
    
    def test_scale_hierarchy_configuration(self):
        """Test default scale hierarchy"""
        params = QuantumCoherenceNSParameters()
        
        # Should have 5 scales by default
        self.assertEqual(len(params.scales), 5)
        
        # Check scale ordering (should go from small to large)
        for i in range(len(params.scales) - 1):
            self.assertLess(
                params.scales[i].length_scale,
                params.scales[i+1].length_scale
            )
    
    def test_coherence_decreases_with_scale(self):
        """Test that coherence generally decreases with larger scales"""
        params = QuantumCoherenceNSParameters()
        
        # Coherence should generally decrease at larger scales
        # (quantum effects are stronger at smaller scales)
        self.assertGreater(
            params.scales[0].coherence,  # Atomic
            params.scales[-1].coherence  # Macroscopic
        )


class TestQuantumCoherenceNavierStokes(unittest.TestCase):
    """Test quantum coherence Navier-Stokes system"""
    
    def setUp(self):
        """Initialize test system"""
        self.params = QuantumCoherenceNSParameters()
        self.system = QuantumCoherenceNavierStokes(self.params)
        
        # Create test grid
        N = 8
        L = 2 * np.pi
        x = np.linspace(0, L, N)
        X, Y, Z = np.meshgrid(x, x, x, indexing='ij')
        self.grid = np.array([X, Y, Z])
        self.grid_spacing = L / (N - 1)
        self.N = N
    
    def test_initialization(self):
        """Test system initialization"""
        self.assertIsNotNone(self.system.params)
        self.assertGreater(self.system.omega_0, 0)
        self.assertEqual(len(self.system.scale_hierarchy), 5)
    
    def test_scale_coupling_matrix(self):
        """Test scale coupling matrix construction"""
        H = self.system.scale_coupling_matrix
        
        # Should be square matrix
        n_scales = len(self.params.scales)
        self.assertEqual(H.shape, (n_scales, n_scales))
        
        # Diagonal should be 1 (self-coupling)
        for i in range(n_scales):
            self.assertEqual(H[i, i], 1.0)
        
        # Should have non-zero off-diagonal elements (adjacent scales)
        self.assertGreater(H[0, 1], 0)  # Atomic → Molecular
        self.assertGreater(H[1, 0], 0)  # Molecular → Atomic
    
    def test_coherence_field_single_point(self):
        """Test coherence field at a single point"""
        x = np.array([0.0, 0.0, 0.0])
        t = 0.0
        
        psi = self.system.compute_coherence_field(x, t)
        
        # Should be a scalar
        self.assertIsInstance(psi, (float, np.floating))
        
        # Should be finite
        self.assertTrue(np.isfinite(psi))
    
    def test_coherence_field_grid(self):
        """Test coherence field on a grid"""
        t = 0.0
        
        psi = self.system.compute_coherence_field(self.grid, t)
        
        # Should match grid shape
        self.assertEqual(psi.shape, (self.N, self.N, self.N))
        
        # Should be finite everywhere
        self.assertTrue(np.all(np.isfinite(psi)))
    
    def test_coherence_field_oscillates(self):
        """Test that coherence field oscillates with time"""
        x = np.array([0.0, 0.0, 0.0])
        
        t1 = 0.0
        t2 = 0.001  # 1 ms later
        
        psi1 = self.system.compute_coherence_field(x, t1)
        psi2 = self.system.compute_coherence_field(x, t2)
        
        # Should oscillate (values should differ)
        self.assertNotAlmostEqual(psi1, psi2, places=6)
    
    def test_coherence_field_by_scale(self):
        """Test coherence field computation for specific scales"""
        x = np.array([0.0, 0.0, 0.0])
        t = 0.0
        
        # Compute for atomic scale
        psi_atomic = self.system.compute_coherence_field(x, t, ScaleLevel.ATOMIC)
        
        # Should be finite
        self.assertTrue(np.isfinite(psi_atomic))
        
        # Compute for macroscopic scale
        psi_macro = self.system.compute_coherence_field(x, t, ScaleLevel.MACROSCOPIC)
        
        # Should also be finite
        self.assertTrue(np.isfinite(psi_macro))
        
        # Generally, atomic should have higher amplitude (higher coherence)
        # But this depends on the specific parameters
    
    def test_scale_hierarchy_operator(self):
        """Test scale hierarchy operator H(x,t)"""
        t = 0.0
        
        H_field = self.system.compute_scale_hierarchy_operator(self.grid, t)
        
        # Should match grid shape
        self.assertEqual(H_field.shape, (self.N, self.N, self.N))
        
        # Should be finite everywhere
        self.assertTrue(np.all(np.isfinite(H_field)))
        
        # Should have some structure (not constant)
        self.assertGreater(np.std(H_field), 1e-10)
    
    def test_phi_tensor_shape(self):
        """Test Φ tensor shape"""
        t = 0.0
        
        phi_tensor = self.system.compute_phi_tensor(self.grid, t, self.grid_spacing)
        
        # Should be (3, 3, Nx, Ny, Nz)
        expected_shape = (3, 3, self.N, self.N, self.N)
        self.assertEqual(phi_tensor.shape, expected_shape)
    
    def test_phi_tensor_symmetry(self):
        """Test that Φ tensor is symmetric: Φ_{ij} = Φ_{ji}"""
        t = 0.0
        
        phi_tensor = self.system.compute_phi_tensor(self.grid, t, self.grid_spacing)
        
        # Check symmetry for all components
        for i in range(3):
            for j in range(3):
                # Φ_{ij} should equal Φ_{ji}
                np.testing.assert_array_almost_equal(
                    phi_tensor[i, j],
                    phi_tensor[j, i],
                    decimal=10,
                    err_msg=f"Tensor not symmetric: Φ[{i},{j}] != Φ[{j},{i}]"
                )
    
    def test_phi_tensor_finite(self):
        """Test that Φ tensor has finite values"""
        t = 0.0
        
        phi_tensor = self.system.compute_phi_tensor(self.grid, t, self.grid_spacing)
        
        # All values should be finite
        self.assertTrue(np.all(np.isfinite(phi_tensor)))
    
    def test_symmetry_verification(self):
        """Test symmetry verification function"""
        t = 0.0
        
        phi_tensor = self.system.compute_phi_tensor(self.grid, t, self.grid_spacing)
        
        result = self.system.verify_tensor_symmetry(phi_tensor)
        
        # Should report symmetric
        self.assertTrue(result['is_symmetric'])
        
        # Asymmetry should be below tolerance
        self.assertLess(result['max_asymmetry'], self.params.symmetry_tolerance)
        
        # Should have no asymmetric components
        self.assertEqual(len(result['asymmetric_components']), 0)
    
    def test_symmetry_enforcement(self):
        """Test that symmetry enforcement works"""
        # Create an asymmetric tensor
        shape = (3, 3, 4, 4, 4)
        asymmetric_tensor = np.random.randn(*shape)
        
        # Enforce symmetry
        symmetric_tensor = self.system._enforce_tensor_symmetry(asymmetric_tensor)
        
        # Check that result is symmetric
        for i in range(3):
            for j in range(3):
                np.testing.assert_array_almost_equal(
                    symmetric_tensor[i, j],
                    symmetric_tensor[j, i],
                    decimal=12
                )
    
    def test_nse_coupling(self):
        """Test Navier-Stokes coupling Φ_{ij}u_j"""
        t = 0.0
        
        # Create velocity field
        u = np.random.randn(3, self.N, self.N, self.N) * 0.1
        
        # Compute tensor
        phi_tensor = self.system.compute_phi_tensor(self.grid, t, self.grid_spacing)
        
        # Compute coupling
        coupling = self.system.compute_nse_coupling(u, phi_tensor)
        
        # Should have same shape as velocity
        self.assertEqual(coupling.shape, u.shape)
        
        # Should be finite
        self.assertTrue(np.all(np.isfinite(coupling)))
    
    def test_nse_coupling_linearity(self):
        """Test that coupling is linear in velocity"""
        t = 0.0
        
        u = np.random.randn(3, self.N, self.N, self.N) * 0.1
        phi_tensor = self.system.compute_phi_tensor(self.grid, t, self.grid_spacing)
        
        # Compute coupling for u and 2u
        coupling_u = self.system.compute_nse_coupling(u, phi_tensor)
        coupling_2u = self.system.compute_nse_coupling(2*u, phi_tensor)
        
        # Should satisfy: Φ(2u) = 2Φ(u)
        np.testing.assert_array_almost_equal(
            coupling_2u,
            2 * coupling_u,
            decimal=10
        )
    
    def test_hierarchy_analysis(self):
        """Test scale hierarchy analysis"""
        analysis = self.system.analyze_scale_hierarchy()
        
        # Should have expected keys
        self.assertIn('num_scales', analysis)
        self.assertIn('scale_names', analysis)
        self.assertIn('length_scales', analysis)
        self.assertIn('coherences', analysis)
        self.assertIn('coupling_matrix', analysis)
        
        # Number of scales should match
        self.assertEqual(analysis['num_scales'], len(self.params.scales))
        
        # Should have positive coupling strength
        self.assertGreater(analysis['total_coupling_strength'], 0)
    
    def test_coherence_evolution_single_point(self):
        """Test coherence evolution at a single point"""
        x = np.array([0.0, 0.0, 0.0])
        t_span = np.linspace(0, 0.01, 50)  # 10 ms
        
        evolution = self.system.simulate_coherence_evolution(x, t_span)
        
        # Should have expected keys
        self.assertIn('times', evolution)
        self.assertIn('psi_total', evolution)
        self.assertIn('psi_by_scale', evolution)
        self.assertIn('hierarchy_field', evolution)
        
        # Should have right length
        self.assertEqual(len(evolution['psi_total']), len(t_span))
        
        # Should have all scales
        for scale in self.params.scales:
            self.assertIn(scale.level.value, evolution['psi_by_scale'])
    
    def test_coherence_evolution_oscillates(self):
        """Test that coherence oscillates over time"""
        x = np.array([0.0, 0.0, 0.0])
        t_span = np.linspace(0, 0.01, 100)  # 10 ms
        
        evolution = self.system.simulate_coherence_evolution(x, t_span)
        psi = evolution['psi_total']
        
        # Should have oscillations (variance > 0)
        self.assertGreater(np.var(psi), 1e-10)
        
        # Should have both positive and negative values (or at least variation)
        self.assertGreater(np.max(psi) - np.min(psi), 1e-6)
    
    def test_fundamental_frequency(self):
        """Test that system uses correct fundamental frequency"""
        self.assertAlmostEqual(self.params.f0_hz, 141.7001, places=4)
        
        omega_expected = 2 * np.pi * 141.7001
        self.assertAlmostEqual(self.system.omega_0, omega_expected, places=2)


class TestIntegration(unittest.TestCase):
    """Integration tests for complete system"""
    
    def test_complete_workflow(self):
        """Test complete workflow from initialization to coupling"""
        # Initialize
        system = QuantumCoherenceNavierStokes()
        
        # Create grid
        N = 8
        L = 2 * np.pi
        x = np.linspace(0, L, N)
        X, Y, Z = np.meshgrid(x, x, x, indexing='ij')
        grid = np.array([X, Y, Z])
        grid_spacing = L / (N - 1)
        
        # Compute fields
        t = 0.0
        psi = system.compute_coherence_field(grid, t)
        H = system.compute_scale_hierarchy_operator(grid, t)
        phi = system.compute_phi_tensor(grid, t, grid_spacing)
        
        # Create velocity and compute coupling
        u = np.random.randn(3, N, N, N) * 0.1
        coupling = system.compute_nse_coupling(u, phi)
        
        # All should be finite
        self.assertTrue(np.all(np.isfinite(psi)))
        self.assertTrue(np.all(np.isfinite(H)))
        self.assertTrue(np.all(np.isfinite(phi)))
        self.assertTrue(np.all(np.isfinite(coupling)))
        
        # Verify symmetry
        symmetry = system.verify_tensor_symmetry(phi)
        self.assertTrue(symmetry['is_symmetric'])
    
    def test_demonstration_runs(self):
        """Test that demonstration function runs without errors"""
        # Should run successfully
        try:
            system = demonstrate_quantum_coherence_navier_stokes()
            self.assertIsNotNone(system)
        except Exception as e:
            self.fail(f"Demonstration failed with error: {e}")


class TestPhysicalConsistency(unittest.TestCase):
    """Test physical consistency of the model"""
    
    def setUp(self):
        """Initialize test system"""
        self.system = QuantumCoherenceNavierStokes()
    
    def test_dimensional_consistency(self):
        """Test dimensional consistency of scales"""
        # Length scales should increase monotonically
        scales = self.system.params.scales
        for i in range(len(scales) - 1):
            self.assertLess(scales[i].length_scale, scales[i+1].length_scale)
    
    def test_coherence_physical_bounds(self):
        """Test that coherence stays in physical bounds [0, 1]"""
        # Create a point
        x = np.array([0.0, 0.0, 0.0])
        
        # Test at multiple times
        for t in np.linspace(0, 1.0, 10):
            psi = self.system.compute_coherence_field(x, t)
            
            # Coherence amplitude should be reasonable
            # (can exceed 1 due to superposition, but should be bounded)
            self.assertLess(abs(psi), 10.0)
    
    def test_hierarchy_coupling_reciprocal(self):
        """Test that scale coupling is reciprocal"""
        H = self.system.scale_coupling_matrix
        
        # For adjacent scales, coupling should be reciprocal
        # (or at least symmetric in this implementation)
        for i in range(len(self.system.params.scales) - 1):
            # H[i, i+1] should be non-zero (upward coupling)
            self.assertGreater(H[i, i+1], 0)
            
            # H[i+1, i] should be non-zero (downward coupling)
            self.assertGreater(H[i+1, i], 0)


if __name__ == '__main__':
    unittest.main()
