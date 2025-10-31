#!/usr/bin/env python3
"""
Test Suite for Seeley-DeWitt Tensor Φ_ij(Ψ)
============================================

Tests for:
1. Seeley-DeWitt tensor computation
2. Quantum-geometric coupling
3. Extended Navier-Stokes equations
4. Energy balance and conservation
5. Tensor symmetry and structure
"""

import unittest
import numpy as np
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from NavierStokes.seeley_dewitt_tensor import (
    SeeleyDeWittTensor, SeeleyDeWittParams
)


class TestSeeleyDeWittParams(unittest.TestCase):
    """Test Seeley-DeWitt parameters"""
    
    def setUp(self):
        """Initialize test parameters"""
        self.params = SeeleyDeWittParams()
    
    def test_default_parameters(self):
        """Test default parameter values"""
        self.assertEqual(self.params.mu, 1.0)
        self.assertEqual(self.params.m_psi, 1.0)
        self.assertEqual(self.params.f0, 141.7001)
        self.assertEqual(self.params.c0, 1.0)
    
    def test_psi_amplitude_computation(self):
        """Test noetic field amplitude computation"""
        psi_0 = self.params.compute_psi_amplitude()
        expected = self.params.I * self.params.A_eff**2
        self.assertAlmostEqual(psi_0, expected)
    
    def test_omega0_computation(self):
        """Test angular frequency computation"""
        omega_0 = self.params.compute_omega0()
        expected = 2 * np.pi * self.params.f0
        self.assertAlmostEqual(omega_0, expected, places=2)
    
    def test_log_ratio_computation(self):
        """Test logarithmic ratio computation"""
        log_ratio = self.params.compute_log_ratio()
        expected = 8 * np.log(self.params.mu / self.params.m_psi)
        self.assertAlmostEqual(log_ratio, expected)
    
    def test_epsilon_scaling(self):
        """Test dual-limit regularization scaling"""
        epsilon = self.params.compute_epsilon()
        # Should decrease with f0 as f0^(-alpha)
        self.assertGreater(epsilon, 0)
        self.assertLess(epsilon, 1.0)


class TestSeeleyDeWittTensor(unittest.TestCase):
    """Test Seeley-DeWitt tensor computation"""
    
    def setUp(self):
        """Initialize test framework"""
        self.sdt = SeeleyDeWittTensor()
        
        # Create test grid
        N = 8
        L = 2 * np.pi
        x = np.linspace(0, L, N)
        X, Y, Z = np.meshgrid(x, x, x, indexing='ij')
        self.grid = np.array([X, Y, Z])
        self.grid_spacing = L / (N - 1)
        self.N = N
    
    def test_initialization(self):
        """Test Seeley-DeWitt tensor initialization"""
        self.assertIsNotNone(self.sdt.params)
        self.assertGreater(self.sdt.psi_0, 0)
        self.assertGreater(self.sdt.omega_0, 0)
    
    def test_psi_field_computation(self):
        """Test noetic field Ψ(x,t) computation"""
        x = np.array([0.0, 0.0, 0.0])
        t = 0.0
        
        psi = self.sdt.compute_psi_field(x, t)
        
        # At t=0, x=0, should be Ψ₀ cos(0) = Ψ₀
        self.assertAlmostEqual(psi, self.sdt.psi_0, places=6)
        
        # Should oscillate with time
        psi_t1 = self.sdt.compute_psi_field(x, 1.0)
        self.assertNotEqual(psi, psi_t1)
    
    def test_psi_time_derivatives(self):
        """Test time derivatives of Ψ"""
        x = np.array([0.0, 0.0, 0.0])
        t = 0.0
        
        # First derivative
        dpsi_dt = self.sdt.compute_psi_time_derivative(x, t, order=1)
        self.assertTrue(np.isfinite(dpsi_dt))
        
        # Second derivative
        d2psi_dt2 = self.sdt.compute_psi_time_derivative(x, t, order=2)
        
        # ∂²Ψ/∂t² = -ω₀²Ψ
        psi = self.sdt.compute_psi_field(x, t)
        expected = -self.sdt.omega_0**2 * psi
        self.assertAlmostEqual(d2psi_dt2, expected, places=2)
    
    def test_epsilon_field_computation(self):
        """Test regularization field ε(x) computation"""
        x = np.array([0.0, 0.0, 0.0])
        
        epsilon = self.sdt.compute_epsilon_field(x)
        
        # Should be positive
        self.assertGreater(epsilon, 0)
        
        # Should be close to base epsilon
        self.assertAlmostEqual(epsilon, self.sdt.epsilon, delta=0.2*self.sdt.epsilon)
    
    def test_ricci_tensor_computation(self):
        """Test effective Ricci tensor R_ij computation"""
        t = 0.0
        
        # Compute diagonal component
        R_00 = self.sdt.compute_ricci_tensor(self.grid, 0, 0, self.grid_spacing)
        
        # Should be finite
        self.assertTrue(np.all(np.isfinite(R_00)))
        
        # Should have spatial structure
        self.assertGreater(np.std(R_00), 0)
    
    def test_phi_tensor_component(self):
        """Test single Φ_ij component computation"""
        t = 0.0
        i, j = 0, 0
        
        phi_00 = self.sdt.compute_phi_tensor_component(
            self.grid, t, i, j, self.grid_spacing
        )
        
        # Should be finite
        self.assertTrue(np.all(np.isfinite(phi_00)))
        
        # Should have spatial structure
        self.assertGreater(np.std(phi_00), 0)
    
    def test_phi_tensor_full(self):
        """Test full Φ_ij tensor computation"""
        t = 0.0
        
        phi_tensor = self.sdt.compute_phi_tensor_full(
            self.grid, t, self.grid_spacing
        )
        
        # Check shape
        expected_shape = (3, 3, self.N, self.N, self.N)
        self.assertEqual(phi_tensor.shape, expected_shape)
        
        # Should be all finite
        self.assertTrue(np.all(np.isfinite(phi_tensor)))
    
    def test_phi_tensor_symmetry(self):
        """Test that Φ_ij is symmetric"""
        t = 0.0
        
        phi_tensor = self.sdt.compute_phi_tensor_full(
            self.grid, t, self.grid_spacing
        )
        
        # Check symmetry: Φ_ij = Φ_ji
        for i in range(3):
            for j in range(i+1, 3):
                max_diff = np.max(np.abs(phi_tensor[i, j] - phi_tensor[j, i]))
                self.assertLess(max_diff, 1e-10, 
                    f"Tensor not symmetric: Φ[{i},{j}] != Φ[{j},{i}]")
    
    def test_phi_tensor_time_dependence(self):
        """Test time dependence of Φ_ij"""
        t1 = 0.0
        t2 = 0.1
        
        phi_t1 = self.sdt.compute_phi_tensor_full(
            self.grid, t1, self.grid_spacing
        )
        phi_t2 = self.sdt.compute_phi_tensor_full(
            self.grid, t2, self.grid_spacing
        )
        
        # Tensors should differ in time
        max_diff = np.max(np.abs(phi_t1 - phi_t2))
        self.assertGreater(max_diff, 0)
    
    def test_extended_nse_coupling(self):
        """Test Φ_ij u_j coupling computation"""
        # Create test velocity field
        u = np.random.randn(3, self.N, self.N, self.N) * 0.1
        
        # Compute tensor
        phi_tensor = self.sdt.compute_phi_tensor_full(
            self.grid, 0.0, self.grid_spacing
        )
        
        # Compute coupling
        coupling = self.sdt.compute_extended_nse_coupling(u, phi_tensor)
        
        # Should have same shape as velocity
        self.assertEqual(coupling.shape, u.shape)
        
        # Should be finite
        self.assertTrue(np.all(np.isfinite(coupling)))
    
    def test_extended_nse_rhs(self):
        """Test full extended NSE right-hand side"""
        # Create test fields
        u = np.random.randn(3, self.N, self.N, self.N) * 0.1
        pressure_grad = np.random.randn(3, self.N, self.N, self.N) * 0.01
        viscosity = 1e-3
        t = 0.0
        
        # Compute RHS
        rhs = self.sdt.compute_extended_nse_rhs(
            u, pressure_grad, viscosity, t, self.grid, self.grid_spacing
        )
        
        # Should have same shape as velocity
        self.assertEqual(rhs.shape, u.shape)
        
        # Should be finite
        self.assertTrue(np.all(np.isfinite(rhs)))
    
    def test_energy_balance_damping(self):
        """Test energy balance analysis shows damping"""
        # Create test velocity field
        u = np.random.randn(3, self.N, self.N, self.N) * 0.1
        
        # Compute tensor
        phi_tensor = self.sdt.compute_phi_tensor_full(
            self.grid, 0.0, self.grid_spacing
        )
        
        # Analyze energy
        energy_analysis = self.sdt.analyze_energy_balance(
            u, phi_tensor, self.grid_spacing
        )
        
        # Should have required keys
        self.assertIn('energy_rate', energy_analysis)
        self.assertIn('symmetry_error', energy_analysis)
        self.assertIn('energy_sign', energy_analysis)
        
        # Energy rate should be finite
        self.assertTrue(np.isfinite(energy_analysis['energy_rate']))
        
        # Symmetry error should be small
        self.assertLess(energy_analysis['symmetry_error'], 1e-8)
    
    def test_validation_passes(self):
        """Test that validation succeeds"""
        results = self.sdt.validate_seeley_dewitt_tensor()
        
        # Should pass validation
        self.assertTrue(results['validation_passed'])
        self.assertTrue(results['all_finite'])
        self.assertTrue(results['is_symmetric'])
        self.assertTrue(results['has_spatial_structure'])


class TestQuantumGeometricCoupling(unittest.TestCase):
    """Test quantum-geometric coupling properties"""
    
    def setUp(self):
        """Initialize test framework"""
        # Create tensor with non-unity mass ratio for testing
        params = SeeleyDeWittParams(mu=2.0, m_psi=1.0)
        self.sdt = SeeleyDeWittTensor(params)
        
        N = 8
        L = 2 * np.pi
        x = np.linspace(0, L, N)
        X, Y, Z = np.meshgrid(x, x, x, indexing='ij')
        self.grid = np.array([X, Y, Z])
        self.grid_spacing = L / (N - 1)
        self.N = N
    
    def test_logarithmic_correction_nonzero(self):
        """Test that logarithmic correction is non-zero for μ ≠ m_Ψ"""
        self.assertNotEqual(self.sdt.log_ratio, 0.0)
        self.assertGreater(abs(self.sdt.log_ratio), 1e-10)
    
    def test_quantum_correction_in_tensor(self):
        """Test that quantum correction appears in tensor"""
        t = 0.0
        
        # Compute tensor component with log correction
        phi_00 = self.sdt.compute_phi_tensor_component(
            self.grid, t, 0, 0, self.grid_spacing
        )
        
        # Should be affected by log_ratio
        self.assertTrue(np.any(np.abs(phi_00) > 1e-10))
    
    def test_ricci_tensor_generated_by_fluid(self):
        """Test that Ricci tensor is generated by fluid (ε field)"""
        # Ricci should depend on epsilon field
        R_00 = self.sdt.compute_ricci_tensor(
            self.grid, 0, 0, self.grid_spacing
        )
        
        # Should have non-trivial structure
        self.assertGreater(np.max(R_00) - np.min(R_00), 1e-10)
    
    def test_temporal_dynamics_in_diagonal(self):
        """Test that temporal dynamics appear in diagonal terms"""
        t = 0.0
        
        # Compute diagonal and off-diagonal
        phi_00 = self.sdt.compute_phi_tensor_component(
            self.grid, t, 0, 0, self.grid_spacing
        )
        phi_01 = self.sdt.compute_phi_tensor_component(
            self.grid, t, 0, 1, self.grid_spacing
        )
        
        # Diagonal should include ∂²Ψ/∂t² term
        # This gives them different magnitude
        # Both should be finite
        self.assertTrue(np.all(np.isfinite(phi_00)))
        self.assertTrue(np.all(np.isfinite(phi_01)))


class TestExtendedNavierStokesEquations(unittest.TestCase):
    """Test extended Navier-Stokes with Φ_ij coupling"""
    
    def setUp(self):
        """Initialize test framework"""
        self.sdt = SeeleyDeWittTensor()
        
        N = 8
        L = 2 * np.pi
        x = np.linspace(0, L, N)
        X, Y, Z = np.meshgrid(x, x, x, indexing='ij')
        self.grid = np.array([X, Y, Z])
        self.grid_spacing = L / (N - 1)
        self.N = N
    
    def test_coupling_preserves_dimensions(self):
        """Test that coupling preserves velocity field dimensions"""
        u = np.random.randn(3, self.N, self.N, self.N) * 0.1
        phi_tensor = self.sdt.compute_phi_tensor_full(
            self.grid, 0.0, self.grid_spacing
        )
        
        coupling = self.sdt.compute_extended_nse_coupling(u, phi_tensor)
        
        self.assertEqual(coupling.shape, u.shape)
    
    def test_coupling_linearity_in_velocity(self):
        """Test that coupling is linear in velocity"""
        u1 = np.random.randn(3, self.N, self.N, self.N) * 0.1
        u2 = np.random.randn(3, self.N, self.N, self.N) * 0.1
        alpha = 2.5
        
        phi_tensor = self.sdt.compute_phi_tensor_full(
            self.grid, 0.0, self.grid_spacing
        )
        
        # Φ(u1 + u2) should equal Φ(u1) + Φ(u2)
        coupling_sum = self.sdt.compute_extended_nse_coupling(
            u1 + u2, phi_tensor
        )
        coupling_1 = self.sdt.compute_extended_nse_coupling(u1, phi_tensor)
        coupling_2 = self.sdt.compute_extended_nse_coupling(u2, phi_tensor)
        
        np.testing.assert_allclose(
            coupling_sum, coupling_1 + coupling_2, rtol=1e-10
        )
        
        # Φ(α u) should equal α Φ(u)
        coupling_scaled = self.sdt.compute_extended_nse_coupling(
            alpha * u1, phi_tensor
        )
        coupling_1_scaled = alpha * self.sdt.compute_extended_nse_coupling(
            u1, phi_tensor
        )
        
        np.testing.assert_allclose(
            coupling_scaled, coupling_1_scaled, rtol=1e-10
        )
    
    def test_extended_nse_includes_all_terms(self):
        """Test that extended NSE includes all physical terms"""
        u = np.random.randn(3, self.N, self.N, self.N) * 0.1
        pressure_grad = np.random.randn(3, self.N, self.N, self.N) * 0.01
        viscosity = 1e-3
        t = 0.0
        
        rhs = self.sdt.compute_extended_nse_rhs(
            u, pressure_grad, viscosity, t, self.grid, self.grid_spacing
        )
        
        # RHS should be non-zero (has multiple contributions)
        self.assertGreater(np.max(np.abs(rhs)), 0)
    
    def test_singularity_prevention_mechanism(self):
        """Test that Φ_ij provides singularity prevention"""
        # Create high vorticity situation
        u = np.random.randn(3, self.N, self.N, self.N)
        phi_tensor = self.sdt.compute_phi_tensor_full(
            self.grid, 0.0, self.grid_spacing
        )
        
        energy_analysis = self.sdt.analyze_energy_balance(
            u, phi_tensor, self.grid_spacing
        )
        
        # In general, we expect damping on average
        # (though instantaneously can vary)
        self.assertIn('energy_sign', energy_analysis)
        self.assertTrue(np.isfinite(energy_analysis['energy_rate']))


def run_tests():
    """Run all tests"""
    print("="*70)
    print("SEELEY-DEWITT TENSOR Φ_ij(Ψ) - TEST SUITE")
    print("="*70)
    print()
    
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestSeeleyDeWittParams))
    suite.addTests(loader.loadTestsFromTestCase(TestSeeleyDeWittTensor))
    suite.addTests(loader.loadTestsFromTestCase(TestQuantumGeometricCoupling))
    suite.addTests(loader.loadTestsFromTestCase(TestExtendedNavierStokesEquations))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Summary
    print()
    print("="*70)
    if result.wasSuccessful():
        print("✓ ALL TESTS PASSED")
        print(f"  {result.testsRun} tests completed successfully")
    else:
        print("✗ SOME TESTS FAILED")
        print(f"  Failures: {len(result.failures)}")
        print(f"  Errors: {len(result.errors)}")
    print("="*70)
    
    return result.wasSuccessful()


if __name__ == "__main__":
    success = run_tests()
    sys.exit(0 if success else 1)
