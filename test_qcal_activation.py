"""
Test Suite for QCAL Framework Activation

Tests the Quantum Coherence Analysis Layer (QCAL) framework activation
and verification of H_Ψ operator, coherence field, and singularity prevention.

Author: JMMB Ψ✧∞³
License: MIT
"""

import unittest
import numpy as np
import os
import sys

# Add current directory to path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from activate_qcal import QCALFramework


class TestQCALFramework(unittest.TestCase):
    """Test cases for QCAL Framework"""
    
    def setUp(self):
        """Set up test fixtures"""
        self.qcal = QCALFramework()
    
    def test_fundamental_frequency(self):
        """Test that fundamental frequency is correctly set"""
        self.assertAlmostEqual(self.qcal.f0_hz, 141.7001, places=4)
        self.assertGreater(self.qcal.f0_hz, 0)
        
        # Check angular frequency
        expected_omega0 = 2 * np.pi * 141.7001
        self.assertAlmostEqual(self.qcal.omega0_rad_s, expected_omega0, places=2)
    
    def test_perfect_coherence(self):
        """Test perfect coherence value"""
        self.assertEqual(self.qcal.psi_perfect, 1.0)
    
    def test_riemann_zeta_constant(self):
        """Test Riemann zeta derivative value"""
        # ζ'(1/2) ≈ -0.207886
        self.assertAlmostEqual(self.qcal.zeta_prime_half, -0.207886, places=5)
        self.assertLess(self.qcal.zeta_prime_half, 0)
    
    def test_H_psi_operator_positive(self):
        """Test that H_Ψ operator produces positive viscosity"""
        x = np.array([1.0, 0.0, 0.0])
        t = 1.0
        
        nu_eff = self.qcal.H_psi_operator(x, t, psi=1.0)
        
        self.assertGreater(nu_eff, 0)
        self.assertIsInstance(nu_eff, (float, np.floating))
    
    def test_H_psi_operator_coherence_scaling(self):
        """Test that H_Ψ scales with coherence squared"""
        x = np.array([0.0, 0.0, 0.0])
        t = 0.0
        
        # Perfect coherence
        nu_perfect = self.qcal.H_psi_operator(x, t, psi=1.0)
        
        # Half coherence should give roughly 1/4 the effect (psi^2 scaling)
        nu_half = self.qcal.H_psi_operator(x, t, psi=0.5)
        
        # Account for the epsilon modulation term
        ratio = nu_half / nu_perfect
        self.assertLess(ratio, 0.5)  # Should be less than half due to psi^2
    
    def test_coherence_field_range(self):
        """Test that coherence field Ψ(x,t) stays in [0,1]"""
        x_values = [
            np.array([0.0, 0.0, 0.0]),
            np.array([1.0, 1.0, 1.0]),
            np.array([-1.0, 2.0, -0.5]),
        ]
        t_values = [0.0, 1.0, 5.0, 10.0]
        
        for x in x_values:
            for t in t_values:
                psi = self.qcal.compute_coherence_field(x, t)
                self.assertGreaterEqual(psi, 0.0, 
                    f"Ψ={psi} < 0 at x={x}, t={t}")
                self.assertLessEqual(psi, 1.0, 
                    f"Ψ={psi} > 1 at x={x}, t={t}")
    
    def test_coherence_field_oscillation(self):
        """Test that coherence field oscillates at fundamental frequency"""
        x = np.array([0.0, 0.0, 0.0])
        
        # Sample over one period
        T0 = 1.0 / self.qcal.f0_hz
        n_samples = 100
        t_values = np.linspace(0, T0, n_samples)
        psi_values = [self.qcal.compute_coherence_field(x, t) for t in t_values]
        
        # Should see oscillation (not constant)
        psi_std = np.std(psi_values)
        self.assertGreater(psi_std, 0.01, 
            "Coherence field should oscillate")
    
    def test_phi_tensor_shape(self):
        """Test that Φᵢⱼ tensor has correct shape"""
        x = np.array([1.0, 0.0, 0.0])
        t = 1.0
        psi = 0.8
        
        Phi_ij = self.qcal.phi_tensor_qft(x, t, psi)
        
        self.assertEqual(Phi_ij.shape, (3, 3))
        self.assertIsInstance(Phi_ij, np.ndarray)
    
    def test_phi_tensor_symmetry(self):
        """Test that Φᵢⱼ tensor is symmetric"""
        x = np.array([1.0, 0.0, 0.0])
        t = 1.0
        psi = 0.8
        
        Phi_ij = self.qcal.phi_tensor_qft(x, t, psi)
        
        # Check symmetry: Φᵢⱼ = Φⱼᵢ
        np.testing.assert_array_almost_equal(Phi_ij, Phi_ij.T, decimal=10)
    
    def test_phi_tensor_coherence_scaling(self):
        """Test that Φᵢⱼ scales linearly with Ψ"""
        x = np.array([1.0, 0.0, 0.0])
        t = 1.0
        
        Phi_full = self.qcal.phi_tensor_qft(x, t, psi=1.0)
        Phi_half = self.qcal.phi_tensor_qft(x, t, psi=0.5)
        
        # Should scale linearly with psi
        np.testing.assert_array_almost_equal(Phi_half, 0.5 * Phi_full, decimal=10)
    
    def test_singularity_prevention_classical_blowup(self):
        """Test that classical NSE shows blow-up"""
        results = self.qcal.demonstrate_singularity_prevention(T_max=5.0, n_points=500)
        
        # Classical should blow up
        self.assertTrue(results['classical_blowup'], 
            "Classical NSE should show blow-up")
        
        # Check that classical vorticity is very large
        max_classical = np.max(results['omega_classical'])
        self.assertGreater(max_classical, 1e3)
    
    def test_singularity_prevention_psi_nse_stable(self):
        """Test that Ψ-NSE remains stable"""
        results = self.qcal.demonstrate_singularity_prevention(T_max=5.0, n_points=500)
        
        # Ψ-NSE should be stable
        self.assertTrue(results['psi_nse_stable'], 
            "Ψ-NSE should remain globally stable")
        
        # Check that Ψ-NSE vorticity is bounded
        max_psi_nse = np.max(results['omega_psi_nse'])
        self.assertLess(max_psi_nse, 100, 
            f"Ψ-NSE vorticity {max_psi_nse} should be bounded")
    
    def test_singularity_prevention_coherence_range(self):
        """Test that coherence values are in valid range"""
        results = self.qcal.demonstrate_singularity_prevention(T_max=5.0, n_points=500)
        
        psi_values = results['psi_values']
        
        # All coherence values should be in [0, 1]
        self.assertTrue(np.all(psi_values >= 0))
        self.assertTrue(np.all(psi_values <= 1))
        
        # Mean coherence should be reasonable
        mean_psi = np.mean(psi_values)
        self.assertGreater(mean_psi, 0.3)
        self.assertLess(mean_psi, 1.0)
    
    def test_visualization_generation(self):
        """Test that visualization is generated successfully"""
        results = self.qcal.demonstrate_singularity_prevention(T_max=2.0, n_points=100)
        
        # Should not raise exception
        fig = self.qcal.visualize_coherence_flow(results, save_path='test_qcal_viz.png')
        
        # Check file was created
        self.assertTrue(os.path.exists('test_qcal_viz.png'))
        
        # Cleanup
        if os.path.exists('test_qcal_viz.png'):
            os.remove('test_qcal_viz.png')
    
    def test_activation_report_generation(self):
        """Test that activation report is generated"""
        report = self.qcal.generate_activation_report()
        
        self.assertIsInstance(report, str)
        self.assertGreater(len(report), 100)
        
        # Check for key phrases
        self.assertIn("QCAL", report)
        self.assertIn("141.7001", report)
        self.assertIn("coherence", report.lower())
        self.assertIn("Riemann", report)


class TestQCALConstants(unittest.TestCase):
    """Test QCAL physical constants"""
    
    def setUp(self):
        """Set up test fixtures"""
        self.qcal = QCALFramework()
    
    def test_planck_constant(self):
        """Test reduced Planck constant"""
        # ℏ ≈ 1.054571817e-34 J·s
        self.assertAlmostEqual(self.qcal.hbar, 1.0545718e-34, places=40)
        self.assertGreater(self.qcal.hbar, 0)
    
    def test_euler_mascheroni_constant(self):
        """Test Euler-Mascheroni constant"""
        # γₑ ≈ 0.5772156649
        self.assertAlmostEqual(self.qcal.gamma_E, 0.5772, places=4)
    
    def test_epsilon_small(self):
        """Test that epsilon is small"""
        self.assertEqual(self.qcal.epsilon, 1e-3)
        self.assertLess(self.qcal.epsilon, 0.01)
    
    def test_viscosity_positive(self):
        """Test that kinematic viscosity is positive"""
        self.assertGreater(self.qcal.nu, 0)
    
    def test_c_star_value(self):
        """Test parabolic coercivity coefficient"""
        self.assertEqual(self.qcal.c_star, 1/16)
        self.assertGreater(self.qcal.c_star, 0)


def run_tests():
    """Run all tests and print summary"""
    print("="*70)
    print("  QCAL FRAMEWORK TEST SUITE")
    print("="*70)
    print()
    
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test cases
    suite.addTests(loader.loadTestsFromTestCase(TestQCALFramework))
    suite.addTests(loader.loadTestsFromTestCase(TestQCALConstants))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Print summary
    print()
    print("="*70)
    print("  TEST SUMMARY")
    print("="*70)
    print(f"  Tests run: {result.testsRun}")
    print(f"  Successes: {result.testsRun - len(result.failures) - len(result.errors)}")
    print(f"  Failures: {len(result.failures)}")
    print(f"  Errors: {len(result.errors)}")
    
    if result.wasSuccessful():
        print()
        print("  ✅ ALL TESTS PASSED - QCAL FRAMEWORK VALIDATED")
    else:
        print()
        print("  ❌ SOME TESTS FAILED - REVIEW REQUIRED")
    
    print("="*70)
    
    return result.wasSuccessful()


if __name__ == '__main__':
    success = run_tests()
    sys.exit(0 if success else 1)
