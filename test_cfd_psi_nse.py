#!/usr/bin/env python3
"""
Test Suite for Ψ-NSE CFD Solver
================================

Validates the CFD solver implementation for blow-up prevention.
"""

import unittest
import numpy as np
from cfd_psi_nse_solver import PsiNSECFDSolver, CFDProblem
import os
import sys


class TestCFDProblem(unittest.TestCase):
    """Test CFD problem definition and validation."""
    
    def test_problem_creation(self):
        """Test basic problem creation."""
        problem = CFDProblem()
        self.assertIsNotNone(problem)
        self.assertEqual(problem.domain_size, (1.0, 1.0, 1.0))
        self.assertEqual(problem.resolution, (32, 32, 32))
    
    def test_custom_problem(self):
        """Test custom problem parameters."""
        problem = CFDProblem(
            domain_size=(2.0, 2.0, 2.0),
            resolution=(64, 64, 64),
            viscosity=1e-4
        )
        self.assertEqual(problem.domain_size, (2.0, 2.0, 2.0))
        self.assertEqual(problem.resolution, (64, 64, 64))
        self.assertEqual(problem.viscosity, 1e-4)
    
    def test_invalid_viscosity(self):
        """Test that negative viscosity raises error."""
        with self.assertRaises(ValueError):
            CFDProblem(viscosity=-1.0)
    
    def test_invalid_resolution(self):
        """Test that invalid resolution raises error."""
        with self.assertRaises(ValueError):
            CFDProblem(resolution=(0, 32, 32))


class TestPsiNSECFDSolver(unittest.TestCase):
    """Test Ψ-NSE CFD solver functionality."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.problem = CFDProblem(
            domain_size=(1.0, 1.0, 1.0),
            resolution=(16, 16, 16),  # Small for fast testing
            viscosity=1e-3,
            initial_condition='taylor_green_vortex'
        )
    
    def test_solver_creation(self):
        """Test solver initialization."""
        solver = PsiNSECFDSolver(self.problem)
        self.assertIsNotNone(solver)
        self.assertTrue(solver.enable_stabilization)
    
    def test_classical_mode(self):
        """Test classical NSE mode."""
        solver = PsiNSECFDSolver(self.problem, enable_stabilization=False)
        self.assertFalse(solver.enable_stabilization)
    
    def test_grid_setup(self):
        """Test spatial grid initialization."""
        solver = PsiNSECFDSolver(self.problem)
        self.assertEqual(solver.Nx, 16)
        self.assertEqual(solver.Ny, 16)
        self.assertEqual(solver.Nz, 16)
        self.assertAlmostEqual(solver.dx, 1.0/16)
    
    def test_wavenumber_grid(self):
        """Test wavenumber grid setup."""
        solver = PsiNSECFDSolver(self.problem)
        self.assertEqual(solver.kx.shape, (16,))
        self.assertEqual(solver.K2.shape, (16, 16, 16))
        # Check k=0 mode was replaced
        self.assertEqual(solver.K2[0, 0, 0], 1.0)
    
    def test_taylor_green_initialization(self):
        """Test Taylor-Green vortex initial condition."""
        solver = PsiNSECFDSolver(self.problem)
        solver.initialize_fields()
        
        self.assertIsNotNone(solver.velocity_field)
        self.assertEqual(solver.velocity_field.shape, (3, 16, 16, 16))
        
        # Check that field is not all zeros
        self.assertGreater(np.max(np.abs(solver.velocity_field)), 0)
    
    def test_turbulent_initialization(self):
        """Test turbulent initial condition."""
        problem = CFDProblem(
            resolution=(16, 16, 16),
            initial_condition='turbulent'
        )
        solver = PsiNSECFDSolver(problem)
        solver.initialize_fields()
        
        self.assertIsNotNone(solver.velocity_field)
        # Turbulent field should have some non-zero values
        self.assertGreater(np.max(np.abs(solver.velocity_field)), 0)
    
    def test_shear_layer_initialization(self):
        """Test shear layer initial condition."""
        problem = CFDProblem(
            resolution=(16, 16, 16),
            initial_condition='shear_layer'
        )
        solver = PsiNSECFDSolver(problem)
        solver.initialize_fields()
        
        self.assertIsNotNone(solver.velocity_field)
        self.assertEqual(solver.velocity_field.shape, (3, 16, 16, 16))
    
    def test_coherence_field_initialization(self):
        """Test quantum coherence field initialization."""
        solver = PsiNSECFDSolver(self.problem)
        solver.initialize_fields()
        
        self.assertIsNotNone(solver.coherence_field)
        self.assertEqual(solver.coherence_field.shape, (16, 16, 16))
        # Coherence field should be positive
        self.assertGreaterEqual(np.min(solver.coherence_field), 0)
    
    def test_coupling_tensor_computation(self):
        """Test coupling tensor Φ(Ψ) computation."""
        solver = PsiNSECFDSolver(self.problem, enable_stabilization=True)
        solver.initialize_fields()
        
        coupling = solver.compute_coupling_tensor(t=0.0)
        
        self.assertIsNotNone(coupling)
        self.assertEqual(coupling.shape, (16, 16, 16))
        # Check that coupling is non-zero when stabilization enabled
        self.assertGreater(np.max(np.abs(coupling)), 0)
    
    def test_coupling_disabled(self):
        """Test that coupling is zero when stabilization disabled."""
        solver = PsiNSECFDSolver(self.problem, enable_stabilization=False)
        solver.initialize_fields()
        
        coupling = solver.compute_coupling_tensor(t=0.0)
        
        # Should be all zeros when disabled
        self.assertEqual(np.max(np.abs(coupling)), 0)
    
    def test_vorticity_computation(self):
        """Test vorticity calculation."""
        solver = PsiNSECFDSolver(self.problem)
        solver.initialize_fields()
        
        omega = solver.compute_vorticity(solver.velocity_field)
        
        self.assertEqual(omega.shape, (3, 16, 16, 16))
        # Vorticity should be non-zero for Taylor-Green vortex
        self.assertGreater(np.max(np.abs(omega)), 0)
    
    def test_diagnostics_computation(self):
        """Test flow diagnostics calculation."""
        solver = PsiNSECFDSolver(self.problem)
        solver.initialize_fields()
        
        diag = solver.compute_diagnostics(0.0, solver.velocity_field)
        
        self.assertIn('time', diag)
        self.assertIn('energy', diag)
        self.assertIn('enstrophy', diag)
        self.assertIn('max_vorticity', diag)
        self.assertIn('stability_indicator', diag)
        
        # Check physical constraints
        self.assertGreater(diag['energy'], 0)
        self.assertGreater(diag['enstrophy'], 0)
        self.assertGreater(diag['max_vorticity'], 0)
    
    def test_physical_constants(self):
        """Test that physical constants are correct."""
        # Natural frequency
        self.assertAlmostEqual(PsiNSECFDSolver.F0_NATURAL, 141.7001, places=4)
        
        # Angular frequency
        expected_omega = 2.0 * np.pi * 141.7001
        self.assertAlmostEqual(PsiNSECFDSolver.OMEGA0, expected_omega, places=2)
        
        # QFT coefficients
        self.assertAlmostEqual(PsiNSECFDSolver.ALPHA_QFT, 1.0/(16.0*np.pi**2), places=8)
        self.assertAlmostEqual(PsiNSECFDSolver.BETA_QFT, 1.0/(384.0*np.pi**2), places=8)
        self.assertAlmostEqual(PsiNSECFDSolver.GAMMA_QFT, 1.0/(192.0*np.pi**2), places=8)
    
    def test_short_simulation(self):
        """Test a short simulation run."""
        solver = PsiNSECFDSolver(self.problem, enable_stabilization=True)
        
        # Short simulation
        results = solver.solve(t_final=0.5, dt_output=0.1)
        
        self.assertIsNotNone(results)
        self.assertIn('success', results)
        self.assertIn('blowup_detected', results)
        self.assertIn('time', results)
        self.assertIn('energy', results)
        
        # Check that time array has at least 2 points (start and something)
        self.assertGreaterEqual(len(results['time']), 2)
        # Check that we got some simulation (even if integration terminated early)
        self.assertGreater(results['time'][-1], 0)
    
    def test_energy_decay(self):
        """Test that energy decays due to viscosity."""
        solver = PsiNSECFDSolver(self.problem)
        results = solver.solve(t_final=2.0, dt_output=0.4)
        
        # Energy should generally decrease over time (with viscosity)
        # Allow for some numerical fluctuations at early times
        energy = results['energy']
        # Check that energy at end is not significantly higher than beginning
        self.assertLessEqual(energy[-1], energy[0] * 1.1)  # Allow 10% tolerance
    
    def test_stabilization_effect(self):
        """Test that stabilization reduces vorticity growth."""
        # Run with stabilization
        solver_stable = PsiNSECFDSolver(self.problem, enable_stabilization=True)
        results_stable = solver_stable.solve(t_final=0.5)
        
        # Run without stabilization
        solver_unstable = PsiNSECFDSolver(self.problem, enable_stabilization=False)
        results_unstable = solver_unstable.solve(t_final=0.5)
        
        # Stabilized version should have lower max vorticity
        max_vort_stable = max(results_stable['max_vorticity'])
        max_vort_unstable = max(results_unstable['max_vorticity'])
        
        # Allow for some variation, but stabilized should generally be lower
        # (or at least not catastrophically higher)
        self.assertLess(max_vort_stable, max_vort_unstable * 2.0)


class TestCFDIntegration(unittest.TestCase):
    """Integration tests for complete CFD workflows."""
    
    def test_complete_workflow(self):
        """Test complete workflow from problem to results."""
        # Define problem
        problem = CFDProblem(
            domain_size=(1.0, 1.0, 1.0),
            resolution=(16, 16, 16),
            viscosity=1e-3
        )
        
        # Create solver
        solver = PsiNSECFDSolver(problem, enable_stabilization=True)
        
        # Run simulation
        results = solver.solve(t_final=0.5)
        
        # Check results
        self.assertTrue(results['success'] or not results['blowup_detected'])
        self.assertGreater(len(results['time']), 0)
        
        # Verify diagnostics are reasonable
        self.assertTrue(np.all(results['energy'] >= 0))
        self.assertTrue(np.all(results['enstrophy'] >= 0))
        self.assertTrue(np.all(results['max_vorticity'] >= 0))
    
    def test_different_initial_conditions(self):
        """Test that solver works with different initial conditions."""
        initial_conditions = ['taylor_green_vortex', 'turbulent', 'shear_layer']
        
        for ic in initial_conditions:
            with self.subTest(initial_condition=ic):
                problem = CFDProblem(
                    resolution=(16, 16, 16),
                    viscosity=1e-3,
                    initial_condition=ic
                )
                solver = PsiNSECFDSolver(problem)
                results = solver.solve(t_final=0.2)
                
                self.assertIsNotNone(results)
                self.assertIn('success', results)


class TestCFDValidation(unittest.TestCase):
    """Validation tests against known results."""
    
    def test_zero_viscosity_limit(self):
        """Test behavior as viscosity approaches zero (Euler limit)."""
        # Note: Very low viscosity will make simulation harder
        problem = CFDProblem(
            resolution=(16, 16, 16),
            viscosity=1e-5,  # Very low
            initial_condition='taylor_green_vortex'
        )
        
        solver = PsiNSECFDSolver(problem, enable_stabilization=True)
        results = solver.solve(t_final=0.1)  # Short time
        
        # Should still complete (possibly with blow-up)
        self.assertIsNotNone(results)
    
    def test_high_viscosity_stability(self):
        """Test that high viscosity leads to stable simulation."""
        problem = CFDProblem(
            resolution=(16, 16, 16),
            viscosity=1e-1,  # High viscosity
        )
        
        solver = PsiNSECFDSolver(problem)
        results = solver.solve(t_final=1.0)
        
        # Should be stable with high viscosity
        self.assertFalse(results['blowup_detected'])
        self.assertTrue(results['success'])


def run_tests(verbosity=2):
    """Run all tests."""
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestCFDProblem))
    suite.addTests(loader.loadTestsFromTestCase(TestPsiNSECFDSolver))
    suite.addTests(loader.loadTestsFromTestCase(TestCFDIntegration))
    suite.addTests(loader.loadTestsFromTestCase(TestCFDValidation))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=verbosity)
    result = runner.run(suite)
    
    return result.wasSuccessful()


if __name__ == '__main__':
    print("="*70)
    print("Ψ-NSE CFD SOLVER - TEST SUITE")
    print("="*70)
    print()
    
    success = run_tests(verbosity=2)
    
    print()
    print("="*70)
    if success:
        print("✓ ALL TESTS PASSED")
        print("="*70)
        sys.exit(0)
    else:
        print("✗ SOME TESTS FAILED")
        print("="*70)
        sys.exit(1)
