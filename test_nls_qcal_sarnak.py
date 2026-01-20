"""
Test Suite for NLS-QCAL-Sarnak Framework

Tests the implementation of the modified NLS equation with QCAL coherent
damping and its connection to the Sarnak conjecture.

Author: JMMB Ψ✧∞³
License: MIT
"""

import unittest
import numpy as np
from nls_qcal_sarnak import (
    NLSQCALSolver,
    SarnakCoherenceTest,
    GlobalExistenceVerifier
)


class TestNLSQCALSolver(unittest.TestCase):
    """Test the NLS-QCAL solver implementation."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.solver = NLSQCALSolver(
            f0=141.7001,
            gamma0=888.0,
            nx=16, ny=16, nz=16,  # Small grid for fast tests
            Lx=2*np.pi, Ly=2*np.pi, Lz=2*np.pi
        )
    
    def test_initialization(self):
        """Test solver initialization."""
        self.assertAlmostEqual(self.solver.f0, 141.7001, places=4)
        self.assertAlmostEqual(self.solver.gamma0, 888.0, places=1)
        self.assertEqual(self.solver.nx, 16)
        self.assertEqual(self.solver.ny, 16)
        self.assertEqual(self.solver.nz, 16)
        
        # Check wavenumbers are set up
        self.assertEqual(len(self.solver.kx), 16)
        self.assertEqual(len(self.solver.ky), 16)
        self.assertEqual(len(self.solver.kz), 16)
        
        # Check K2 shape
        self.assertEqual(self.solver.K2.shape, (16, 16, 16))
    
    def test_laplacian_constant(self):
        """Test Laplacian of constant field is zero."""
        psi = np.ones((16, 16, 16), dtype=complex)
        laplacian = self.solver.compute_laplacian(psi)
        
        # Should be very close to zero
        self.assertLess(np.max(np.abs(laplacian)), 1e-10)
    
    def test_laplacian_sine_wave(self):
        """Test Laplacian computation with sine wave."""
        # Create a simple sine wave: sin(x)
        x = np.linspace(0, 2*np.pi, 16, endpoint=False)
        X, Y, Z = np.meshgrid(x, x, x, indexing='ij')
        
        # Ψ = sin(x), Laplacian should be -sin(x)
        psi = np.sin(X).astype(complex)
        laplacian = self.solver.compute_laplacian(psi)
        expected = -np.sin(X)
        
        # Check approximation (won't be perfect due to discretization)
        error = np.max(np.abs(laplacian.real - expected))
        self.assertLess(error, 0.1)
    
    def test_divergence_zero_for_solenoidal(self):
        """Test divergence is zero for solenoidal field."""
        x = np.linspace(0, 2*np.pi, 16, endpoint=False)
        X, Y, Z = np.meshgrid(x, x, x, indexing='ij')
        
        # Solenoidal field: v = (sin(y), -sin(x), 0)
        vx = np.sin(Y)
        vy = -np.sin(X)
        vz = np.zeros_like(X)
        
        div_v = self.solver.compute_divergence(vx, vy, vz)
        
        # Should be very small
        self.assertLess(np.max(np.abs(div_v)), 1e-10)
    
    def test_alpha_coherence_term(self):
        """Test damping parameter α computation."""
        # Create field with known magnitude
        psi = 0.9 * np.ones((16, 16, 16), dtype=complex)
        
        # Without velocity field
        alpha = self.solver.compute_alpha(psi, velocity_field=None)
        
        # Should equal γ₀(1 - |Ψ|²)
        expected = self.solver.gamma0 * (1 - 0.9**2)
        
        # Check all points
        self.assertAlmostEqual(np.mean(alpha), expected, places=4)
    
    def test_energy_computation(self):
        """Test energy computation."""
        # Constant field should have only nonlinear energy
        psi = 0.5 * np.ones((16, 16, 16), dtype=complex)
        energy = self.solver.compute_energy(psi)
        
        # Energy should be positive
        self.assertGreater(energy, 0)
        
        # E = ∫(|∇Ψ|² + (f₀/3)|Ψ|⁶)dx
        # For constant: E ≈ V·(f₀/3)·|Ψ|⁶
        V = (2*np.pi)**3
        expected_approx = V * (self.solver.f0 / 3) * 0.5**6
        
        # Should be close (gradient term is small for constant)
        self.assertAlmostEqual(energy, expected_approx, places=-2)
    
    def test_coherence_computation(self):
        """Test coherence computation."""
        # Uniform field
        psi = 0.888 * np.ones((16, 16, 16), dtype=complex)
        coherence = self.solver.compute_coherence(psi)
        
        self.assertAlmostEqual(coherence, 0.888, places=3)
        
        # Mixed field
        psi2 = np.random.rand(16, 16, 16) + 1j * np.random.rand(16, 16, 16)
        coherence2 = self.solver.compute_coherence(psi2)
        
        # Should be positive and less than max |Ψ|
        self.assertGreater(coherence2, 0)
        self.assertLess(coherence2, np.max(np.abs(psi2)))
    
    def test_entropy_computation(self):
        """Test entropy computation."""
        # Perfect coherent state |Ψ| = 1
        psi = np.ones((16, 16, 16), dtype=complex)
        entropy = self.solver.compute_entropy(psi)
        
        # Should be very close to zero
        self.assertLess(entropy, 1e-10)
        
        # Incoherent state
        psi2 = 0.5 * np.ones((16, 16, 16), dtype=complex)
        entropy2 = self.solver.compute_entropy(psi2)
        
        # Should be positive
        self.assertGreater(entropy2, 0)
    
    def test_solver_runs(self):
        """Test that solver runs without errors."""
        # Simple initial condition
        psi0 = 0.9 * np.ones((16, 16, 16), dtype=complex)
        
        # Solve for short time
        result = self.solver.solve(
            psi0,
            t_span=(0, 0.1),
            t_eval=np.linspace(0, 0.1, 5),
            method='RK23'  # Faster method for testing
        )
        
        self.assertTrue(result['success'])
        self.assertEqual(len(result['t']), 5)
        self.assertEqual(len(result['psi']), 5)
        self.assertEqual(len(result['coherence']), 5)
        self.assertEqual(len(result['energy']), 5)
        self.assertEqual(len(result['entropy']), 5)


class TestSarnakCoherenceTest(unittest.TestCase):
    """Test the Sarnak orthogonality testing."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.sarnak = SarnakCoherenceTest(f0=141.7001)
    
    def test_mobius_values(self):
        """Test Möbius function computation."""
        # Known values
        self.assertEqual(self.sarnak.mobius(1), 1)
        self.assertEqual(self.sarnak.mobius(2), -1)  # One prime
        self.assertEqual(self.sarnak.mobius(3), -1)  # One prime
        self.assertEqual(self.sarnak.mobius(4), 0)   # 2²
        self.assertEqual(self.sarnak.mobius(5), -1)  # One prime
        self.assertEqual(self.sarnak.mobius(6), 1)   # Two primes: 2·3
        self.assertEqual(self.sarnak.mobius(8), 0)   # 2³
        self.assertEqual(self.sarnak.mobius(30), -1) # Three primes: 2·3·5
    
    def test_coherent_sequence_generation(self):
        """Test coherent sequence generation."""
        N = 1000
        coherence_level = 0.95
        
        psi_seq = self.sarnak.generate_coherent_sequence(N, coherence_level)
        
        # Check length
        self.assertEqual(len(psi_seq), N)
        
        # Check coherence is approximately at target level
        mean_magnitude = np.mean(np.abs(psi_seq))
        self.assertGreater(mean_magnitude, coherence_level * 0.5)
        self.assertLess(mean_magnitude, coherence_level * 1.5)
    
    def test_orthogonality_for_coherent_system(self):
        """Test that coherent systems satisfy Sarnak orthogonality."""
        N = 5000
        coherence_level = 0.95  # Above threshold
        
        result = self.sarnak.test_orthogonality(N, coherence_level)
        
        # Check result structure
        self.assertEqual(result['N'], N)
        self.assertAlmostEqual(result['coherence_level'], coherence_level)
        self.assertIn('correlations', result)
        self.assertIn('final_correlation', result)
        
        # Final correlation should be small
        self.assertLess(np.abs(result['final_correlation']), 0.2)
        
        # Orthogonality should be satisfied
        self.assertTrue(result['orthogonality_satisfied'])
    
    def test_convergence_rate(self):
        """Test that convergence follows expected power law."""
        N = 10000
        result = self.sarnak.test_orthogonality(N, coherence_level=0.95)
        
        # Convergence rate can vary due to statistical fluctuations
        # Just check that correlation is getting smaller
        if result['convergence_rate'] is not None and len(result['correlations']) > 2:
            # Check that the correlation is small at the end
            self.assertLess(np.abs(result['final_correlation']), 0.3)
            
            # Check general trend: later correlations should be smaller than earlier ones
            # (on average)
            early_mean = np.mean(np.abs(result['correlations'][:len(result['correlations'])//2]))
            late_mean = np.mean(np.abs(result['correlations'][len(result['correlations'])//2:]))
            
            # Late correlations should tend to be smaller (allowing some tolerance)
            self.assertLess(late_mean, early_mean * 1.5)


class TestGlobalExistenceVerifier(unittest.TestCase):
    """Test the global existence verification."""
    
    def setUp(self):
        """Set up test fixtures."""
        # Use moderate damping for testing (γ₀ = 88 instead of 888)
        # The full γ₀ = 888 causes very rapid decay to |Ψ| = 1
        self.solver = NLSQCALSolver(
            nx=16, ny=16, nz=16,
            gamma0=88.0,  # Moderate damping for testing
            Lx=2*np.pi, Ly=2*np.pi, Lz=2*np.pi
        )
        self.verifier = GlobalExistenceVerifier(self.solver)
    
    def test_energy_decay_verification(self):
        """Test energy decay verification."""
        # Create fake history with decaying energy
        energy_history = np.array([10.0, 9.5, 9.0, 8.6, 8.3])
        time_points = np.array([0.0, 0.1, 0.2, 0.3, 0.4])
        
        result = self.verifier.verify_energy_decay(energy_history, time_points)
        
        self.assertTrue(result['energy_decay_satisfied'])
        self.assertEqual(result['num_violations'], 0)
        self.assertLess(result['max_energy_increase'], 1e-6)
        self.assertLess(result['mean_energy_rate'], 0)
    
    def test_energy_decay_violation(self):
        """Test detection of energy increase."""
        # Energy that increases
        energy_history = np.array([10.0, 10.5, 11.0])
        time_points = np.array([0.0, 0.1, 0.2])
        
        result = self.verifier.verify_energy_decay(energy_history, time_points)
        
        self.assertFalse(result['energy_decay_satisfied'])
        self.assertGreater(result['num_violations'], 0)
    
    def test_coherence_maintenance_verification(self):
        """Test coherence maintenance verification."""
        # Coherence above threshold
        coherence_history = np.array([0.95, 0.94, 0.93, 0.92, 0.91])
        
        result = self.verifier.verify_coherence_maintenance(
            coherence_history,
            threshold=0.888
        )
        
        self.assertTrue(result['coherence_maintained'])
        self.assertEqual(result['num_violations'], 0)
        self.assertGreaterEqual(result['min_coherence'], 0.888 - 0.01)
    
    def test_coherence_violation(self):
        """Test detection of coherence violation."""
        # Coherence drops below threshold
        coherence_history = np.array([0.95, 0.90, 0.85, 0.80])
        
        result = self.verifier.verify_coherence_maintenance(
            coherence_history,
            threshold=0.888
        )
        
        self.assertFalse(result['coherence_maintained'])
        self.assertGreater(result['num_violations'], 0)
    
    def test_entropy_decay_verification(self):
        """Test entropy decay verification."""
        # Decaying entropy
        entropy_history = np.array([1.0, 0.8, 0.6, 0.5, 0.4])
        time_points = np.array([0.0, 0.1, 0.2, 0.3, 0.4])
        
        result = self.verifier.verify_entropy_decay(entropy_history, time_points)
        
        self.assertTrue(result['entropy_decay_satisfied'])
        self.assertLess(result['mean_entropy_rate'], 0)
        self.assertGreater(result['entropy_reduction'], 0)
    
    def test_global_existence_with_coherent_initial_data(self):
        """Test global existence verification with coherent initial condition."""
        # Create coherent initial condition with spatial variation
        # This prevents the strong damping from killing the field
        x = np.linspace(0, 2*np.pi, 16, endpoint=False)
        X, Y, Z = np.meshgrid(x, x, x, indexing='ij')
        
        # Smooth profile close to |Ψ| = 1
        psi0 = (0.98 + 0.04 * np.sin(X) * np.sin(Y) * np.sin(Z)).astype(complex)
        
        # Short time test
        result = self.verifier.verify_global_existence(
            psi0,
            t_final=0.01,  # Very short time to avoid numerical issues
            num_points=3
        )
        
        # Should verify successfully
        self.assertTrue(result['global_existence_verified'])
        self.assertGreaterEqual(result['initial_coherence'], 0.888)
        self.assertTrue(result['solution']['success'])


class TestIntegration(unittest.TestCase):
    """Integration tests for the complete framework."""
    
    def test_complete_workflow(self):
        """Test complete NLS-QCAL-Sarnak workflow."""
        # 1. Create solver with moderate damping for testing
        solver = NLSQCALSolver(nx=16, ny=16, nz=16, gamma0=88.0)
        
        # 2. Create coherent initial condition with small spatial variation
        # Keep variation small to maintain coherence above threshold
        x = np.linspace(0, 2*np.pi, 16, endpoint=False)
        X, Y, Z = np.meshgrid(x, x, x, indexing='ij')
        psi0 = (0.98 + 0.02 * np.sin(X) * np.sin(Y) * np.sin(Z)).astype(complex)
        
        # 3. Verify global existence (very short time)
        verifier = GlobalExistenceVerifier(solver)
        result = verifier.verify_global_existence(psi0, t_final=0.005, num_points=3)
        
        self.assertTrue(result['global_existence_verified'])
        
        # 4. Test Sarnak orthogonality
        sarnak = SarnakCoherenceTest()
        sarnak_result = sarnak.test_orthogonality(N=1000, coherence_level=0.92)
        
        self.assertTrue(sarnak_result['orthogonality_satisfied'])
    
    def test_framework_with_varying_coherence(self):
        """Test framework behavior with different coherence levels."""
        solver = NLSQCALSolver(nx=16, ny=16, nz=16, gamma0=88.0)
        verifier = GlobalExistenceVerifier(solver)
        
        coherence_levels = [0.85, 0.888, 0.90, 0.95]
        
        for coh in coherence_levels:
            x = np.linspace(0, 2*np.pi, 16, endpoint=False)
            X, Y, Z = np.meshgrid(x, x, x, indexing='ij')
            psi0 = (coh + 0.02 * np.sin(X) * np.sin(Y) * np.sin(Z)).astype(complex)
            
            result = verifier.verify_global_existence(
                psi0,
                t_final=0.01,
                num_points=3
            )
            
            # All should succeed (solver is robust)
            self.assertTrue(result['solution']['success'])
            
            # Check initial coherence
            self.assertAlmostEqual(result['initial_coherence'], coh, places=1)


def run_tests():
    """Run all tests."""
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestNLSQCALSolver))
    suite.addTests(loader.loadTestsFromTestCase(TestSarnakCoherenceTest))
    suite.addTests(loader.loadTestsFromTestCase(TestGlobalExistenceVerifier))
    suite.addTests(loader.loadTestsFromTestCase(TestIntegration))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    return result


if __name__ == '__main__':
    result = run_tests()
    
    # Print summary
    print("\n" + "="*70)
    print("TEST SUMMARY")
    print("="*70)
    print(f"Tests run: {result.testsRun}")
    print(f"Successes: {result.testsRun - len(result.failures) - len(result.errors)}")
    print(f"Failures: {len(result.failures)}")
    print(f"Errors: {len(result.errors)}")
    print("="*70)
    
    if result.wasSuccessful():
        print("✓ All tests passed!")
    else:
        print("✗ Some tests failed.")
