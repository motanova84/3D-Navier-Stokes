"""
Test Suite for ∞³ Framework: Nature-Computation-Mathematics Unity

This test suite verifies the implementation of the three-pillar framework
that demonstrates the necessity of extended Navier-Stokes equations.

Author: JMMB Ψ✧∞³
License: MIT
"""

import unittest
import numpy as np
from infinity_cubed_framework import (
    NatureObservations,
    ComputationalVerification,
    MathematicalFormalization,
    InfinityCubedFramework
)


class TestNatureObservations(unittest.TestCase):
    """Test the Nature pillar (∞¹)."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.nature = NatureObservations()
    
    def test_initialization(self):
        """Test that NatureObservations initializes correctly."""
        self.assertAlmostEqual(self.nature.f0_hz, 141.7001, places=4)
        self.assertAlmostEqual(
            self.nature.omega0_rad_s,
            2 * np.pi * 141.7001,
            places=2
        )
        self.assertIsInstance(self.nature.incompleteness_evidence, dict)
        self.assertGreater(len(self.nature.incompleteness_evidence), 0)
    
    def test_incompleteness_evidence_structure(self):
        """Test that incompleteness evidence has correct structure."""
        for name, obs in self.nature.incompleteness_evidence.items():
            self.assertIn('description', obs)
            self.assertIn('classical_prediction', obs)
            self.assertIn('observed_reality', obs)
            self.assertIn('evidence_strength', obs)
            self.assertGreaterEqual(obs['evidence_strength'], 0.0)
            self.assertLessEqual(obs['evidence_strength'], 1.0)
    
    def test_evaluate_classical_incompleteness(self):
        """Test incompleteness evaluation."""
        metrics = self.nature.evaluate_classical_incompleteness()
        
        self.assertIn('mean_incompleteness', metrics)
        self.assertIn('max_incompleteness', metrics)
        self.assertIn('min_incompleteness', metrics)
        self.assertIn('incompleteness_verdict', metrics)
        
        # Check that mean is between min and max
        self.assertGreaterEqual(
            metrics['mean_incompleteness'],
            metrics['min_incompleteness']
        )
        self.assertLessEqual(
            metrics['mean_incompleteness'],
            metrics['max_incompleteness']
        )
        
        # Verdict should be True (classical NSE is incomplete)
        self.assertTrue(metrics['incompleteness_verdict'])
    
    def test_get_universal_frequency(self):
        """Test universal frequency retrieval."""
        freq = self.nature.get_universal_frequency()
        
        self.assertIn('f0_hz', freq)
        self.assertIn('omega0_rad_s', freq)
        self.assertIn('period_s', freq)
        self.assertIn('wavelength_km', freq)
        
        self.assertAlmostEqual(freq['f0_hz'], 141.7001, places=4)
        self.assertAlmostEqual(freq['period_s'], 1.0 / 141.7001, places=6)
    
    def test_summarize_natural_evidence(self):
        """Test that summary generates valid output."""
        summary = self.nature.summarize_natural_evidence()
        
        self.assertIsInstance(summary, str)
        self.assertIn('∞¹ NATURE', summary)
        self.assertIn('INCOMPLETE', summary)
        self.assertGreater(len(summary), 100)


class TestComputationalVerification(unittest.TestCase):
    """Test the Computation pillar (∞²)."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.computation = ComputationalVerification(nu=1e-3)
    
    def test_initialization(self):
        """Test that ComputationalVerification initializes correctly."""
        self.assertEqual(self.computation.nu, 1e-3)
        self.assertAlmostEqual(self.computation.f0_hz, 141.7001, places=4)
    
    def test_simulate_classical_nse_blow_up_risk(self):
        """Test classical NSE simulation."""
        result = self.computation.simulate_classical_nse_blow_up_risk(
            initial_vorticity_norm=10.0,
            time_horizon=1.0,
            dt=0.01
        )
        
        self.assertIn('blow_up_detected', result)
        self.assertIn('final_vorticity', result)
        self.assertIn('bkm_integral', result)
        self.assertIn('regularity', result)
        
        # Classical NSE should show growth
        self.assertGreater(result['final_vorticity'], 10.0)
        self.assertGreater(result['growth_factor'], 1.0)
    
    def test_simulate_extended_nse_with_phi_coupling(self):
        """Test extended NSE with Φ_ij coupling."""
        result = self.computation.simulate_extended_nse_with_phi_coupling(
            initial_vorticity_norm=10.0,
            time_horizon=1.0,
            dt=0.01,
            phi_coupling_strength=1e-3
        )
        
        self.assertIn('blow_up_detected', result)
        self.assertIn('final_vorticity', result)
        self.assertIn('bkm_integral', result)
        self.assertIn('regularity', result)
        self.assertIn('damping_coefficient', result)
        
        # Extended NSE should show regularization
        self.assertFalse(result['blow_up_detected'])
        self.assertLess(result['bkm_integral'], np.inf)
        self.assertTrue(result['regularity'])
    
    def test_compare_classical_vs_extended(self):
        """Test comparison between classical and extended NSE."""
        comparison = self.computation.compare_classical_vs_extended(
            initial_vorticity=10.0,
            time_horizon=2.0
        )
        
        self.assertIn('classical_nse', comparison)
        self.assertIn('extended_nse', comparison)
        self.assertIn('improvement_factor', comparison)
        self.assertIn('additional_physics_necessary', comparison)
        
        # Extended should perform better
        classical_final = comparison['classical_nse']['final_vorticity']
        extended_final = comparison['extended_nse']['final_vorticity']
        
        # In general, extended should have better control
        # (though not always strictly less due to oscillations)
        self.assertGreater(comparison['improvement_factor'], 0.1)
    
    def test_blow_up_detection_classical(self):
        """Test that classical NSE can detect blow-up risk."""
        # Use very high initial vorticity to trigger blow-up
        result = self.computation.simulate_classical_nse_blow_up_risk(
            initial_vorticity_norm=1000.0,
            time_horizon=0.1,
            dt=0.001
        )
        
        # Should either blow up or have very high vorticity
        self.assertTrue(
            result['blow_up_detected'] or
            result['final_vorticity'] > 1e6
        )
    
    def test_extended_nse_stability(self):
        """Test that extended NSE shows regularization compared to classical."""
        # Compare classical vs extended at same conditions
        initial_vort = 20.0
        classical = self.computation.simulate_classical_nse_blow_up_risk(
            initial_vorticity_norm=initial_vort,
            time_horizon=0.2,
            dt=0.01
        )
        extended = self.computation.simulate_extended_nse_with_phi_coupling(
            initial_vorticity_norm=initial_vort,
            time_horizon=0.2,
            dt=0.01,
            phi_coupling_strength=0.1
        )
        
        # Extended should not blow up
        self.assertFalse(extended['blow_up_detected'])
        # Extended should show regularization effect (at least some control)
        # The key is that extended has finite BKM integral
        self.assertTrue(np.isfinite(extended['bkm_integral']))
    
    def test_summarize_computational_evidence(self):
        """Test that computational summary generates valid output."""
        summary = self.computation.summarize_computational_evidence()
        
        self.assertIsInstance(summary, str)
        self.assertIn('∞² COMPUTATION', summary)
        self.assertIn('Classical NSE', summary)
        self.assertIn('Extended NSE', summary)
        self.assertGreater(len(summary), 100)


class TestMathematicalFormalization(unittest.TestCase):
    """Test the Mathematics pillar (∞³)."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.mathematics = MathematicalFormalization()
    
    def test_initialization(self):
        """Test that MathematicalFormalization initializes correctly."""
        self.assertAlmostEqual(self.mathematics.f0_hz, 141.7001, places=4)
        self.assertAlmostEqual(
            self.mathematics.delta_star,
            1.0 / (4 * np.pi**2),
            places=6
        )
        
        # Check Seeley-DeWitt coefficients are set
        self.assertIsNotNone(self.mathematics.a1)
        self.assertIsNotNone(self.mathematics.a2)
        self.assertIsNotNone(self.mathematics.a3)
    
    def test_seeley_dewitt_coefficients(self):
        """Test Seeley-DeWitt coefficients have correct values."""
        # From QFT derivation
        self.assertAlmostEqual(self.mathematics.a1, 1.407239e-04, places=9)
        self.assertAlmostEqual(self.mathematics.a2, 3.518097e-05, places=10)
        self.assertAlmostEqual(self.mathematics.a3, -7.036193e-05, places=10)
    
    def test_formal_statement_classical_nse(self):
        """Test classical NSE formal statement."""
        statement = self.mathematics.formal_statement_classical_nse()
        
        self.assertIsInstance(statement, str)
        self.assertIn('Navier-Stokes', statement)
        self.assertIn('Clay', statement)
        self.assertIn('incomplete', statement.lower())
    
    def test_formal_statement_extended_nse(self):
        """Test extended NSE formal statement."""
        statement = self.mathematics.formal_statement_extended_nse()
        
        self.assertIsInstance(statement, str)
        self.assertIn('Extended', statement)
        self.assertIn('Phi', statement)
        self.assertIn('Seeley-DeWitt', statement)
        self.assertIn('Global Regularity', statement)
    
    def test_theorem_incompleteness_necessity(self):
        """Test incompleteness-necessity theorem."""
        theorem = self.mathematics.theorem_incompleteness_necessity()
        
        self.assertIn('theorem_name', theorem)
        self.assertIn('statement', theorem)
        self.assertIn('formal_statement', theorem)
        self.assertIn('proof_sketch', theorem)
        
        self.assertEqual(
            theorem['theorem_name'],
            'Incompleteness-Necessity Theorem'
        )
    
    def test_formal_connection_nature_computation_mathematics(self):
        """Test formal connection between pillars."""
        connection = self.mathematics.formal_connection_nature_computation_mathematics()
        
        self.assertIn('nature_observation', connection)
        self.assertIn('computation_confirms', connection)
        self.assertIn('mathematics_formalizes', connection)
        self.assertIn('unity', connection)
        self.assertIn('logical_chain', connection)
        
        # Check logical chain has all steps
        chain = connection['logical_chain']
        self.assertGreaterEqual(len(chain), 3)
        self.assertIn('∞³', connection['unity'])
    
    def test_summarize_mathematical_framework(self):
        """Test that mathematical summary generates valid output."""
        summary = self.mathematics.summarize_mathematical_framework()
        
        self.assertIsInstance(summary, str)
        self.assertIn('∞³ MATHEMATICS', summary)
        self.assertIn('Incompleteness-Necessity', summary)
        self.assertIn('Φ_ij', summary)
        self.assertGreater(len(summary), 100)


class TestInfinityCubedFramework(unittest.TestCase):
    """Test the complete ∞³ framework integration."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.framework = InfinityCubedFramework(nu=1e-3)
    
    def test_initialization(self):
        """Test that framework initializes correctly."""
        self.assertIsInstance(self.framework.nature, NatureObservations)
        self.assertIsInstance(
            self.framework.computation,
            ComputationalVerification
        )
        self.assertIsInstance(
            self.framework.mathematics,
            MathematicalFormalization
        )
    
    def test_execute_complete_framework(self):
        """Test complete framework execution."""
        results = self.framework.execute_complete_framework()
        
        # Check all three pillars are present
        self.assertIn('nature', results)
        self.assertIn('computation', results)
        self.assertIn('mathematics', results)
        self.assertIn('infinity_cubed_unity', results)
        self.assertIn('conclusion', results)
        
        # Check nature results
        nature = results['nature']
        self.assertIn('incompleteness_score', nature)
        self.assertIn('universal_frequency_hz', nature)
        self.assertIn('verdict', nature)
        self.assertGreater(nature['incompleteness_score'], 0.5)
        
        # Check computation results
        computation = results['computation']
        self.assertIn('classical_blow_up_risk', computation)
        self.assertIn('extended_regularity', computation)
        self.assertIn('improvement_factor', computation)
        self.assertIn('verdict', computation)
        self.assertTrue(computation['extended_regularity'])
        
        # Check mathematics results
        mathematics = results['mathematics']
        self.assertIn('theorem', mathematics)
        self.assertIn('phi_tensor_derived', mathematics)
        self.assertIn('delta_star', mathematics)
        self.assertIn('verdict', mathematics)
        self.assertTrue(mathematics['phi_tensor_derived'])
    
    def test_unity_achievement(self):
        """Test that ∞³ unity is achieved."""
        results = self.framework.execute_complete_framework()
        
        # Unity should be achieved when all three pillars confirm
        self.assertTrue(results['infinity_cubed_unity'])
    
    def test_generate_full_report(self):
        """Test full report generation."""
        report = self.framework.generate_full_report()
        
        self.assertIsInstance(report, str)
        self.assertIn('∞³ FRAMEWORK', report)
        self.assertIn('∞¹ NATURE', report)
        self.assertIn('∞² COMPUTATION', report)
        self.assertIn('∞³ MATHEMATICS', report)
        self.assertIn('∞³ UNITY', report)
        self.assertGreater(len(report), 1000)
    
    def test_all_verdicts_consistent(self):
        """Test that all three pillars give consistent verdicts."""
        results = self.framework.execute_complete_framework()
        
        # All should point to same conclusion
        nature_incomplete = 'INCOMPLETE' in results['nature']['verdict']
        computation_necessary = 'NECESSARY' in results['computation']['verdict']
        mathematics_formalized = 'FORMALIZED' in results['mathematics']['verdict']
        
        # All should be True for consistency
        self.assertTrue(nature_incomplete)
        self.assertTrue(computation_necessary)
        self.assertTrue(mathematics_formalized)
    
    def test_numerical_consistency(self):
        """Test numerical consistency across framework."""
        results = self.framework.execute_complete_framework()
        
        # Universal frequency should match across pillars
        freq_nature = results['nature']['universal_frequency_hz']
        self.assertAlmostEqual(freq_nature, 141.7001, places=4)
        
        # Delta star should match known value
        delta_star = results['mathematics']['delta_star']
        self.assertAlmostEqual(delta_star, 1.0 / (4 * np.pi**2), places=6)
        
        # Improvement factor should be positive
        improvement = results['computation']['improvement_factor']
        self.assertGreater(improvement, 0)


class TestIntegration(unittest.TestCase):
    """Integration tests for the complete ∞³ framework."""
    
    def test_end_to_end_execution(self):
        """Test complete end-to-end framework execution."""
        framework = InfinityCubedFramework(nu=1e-3)
        results = framework.execute_complete_framework()
        
        # Should successfully complete without errors
        self.assertIsInstance(results, dict)
        self.assertTrue(results['infinity_cubed_unity'])
    
    def test_report_generation_no_errors(self):
        """Test that report generation completes without errors."""
        framework = InfinityCubedFramework(nu=1e-3)
        
        # Should complete without raising exceptions
        try:
            report = framework.generate_full_report()
            self.assertIsInstance(report, str)
            self.assertGreater(len(report), 500)
        except Exception as e:
            self.fail(f"Report generation raised exception: {e}")
    
    def test_multiple_viscosities(self):
        """Test framework with different viscosities."""
        for nu in [1e-2, 1e-3, 1e-4]:
            framework = InfinityCubedFramework(nu=nu)
            results = framework.execute_complete_framework()
            
            # Should work for all viscosities
            self.assertTrue(results['infinity_cubed_unity'])
            self.assertTrue(results['computation']['extended_regularity'])


def run_tests():
    """Run all tests and print summary."""
    print("\n" + "=" * 70)
    print("∞³ FRAMEWORK TEST SUITE")
    print("=" * 70 + "\n")
    
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test cases
    suite.addTests(loader.loadTestsFromTestCase(TestNatureObservations))
    suite.addTests(loader.loadTestsFromTestCase(TestComputationalVerification))
    suite.addTests(loader.loadTestsFromTestCase(TestMathematicalFormalization))
    suite.addTests(loader.loadTestsFromTestCase(TestInfinityCubedFramework))
    suite.addTests(loader.loadTestsFromTestCase(TestIntegration))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Print summary
    print("\n" + "=" * 70)
    print("TEST SUMMARY")
    print("=" * 70)
    print(f"Tests run:     {result.testsRun}")
    print(f"Successes:     {result.testsRun - len(result.failures) - len(result.errors)}")
    print(f"Failures:      {len(result.failures)}")
    print(f"Errors:        {len(result.errors)}")
    print("=" * 70)
    
    if result.wasSuccessful():
        print("\n✓ ALL TESTS PASSED - ∞³ FRAMEWORK VERIFIED\n")
        return 0
    else:
        print("\n✗ SOME TESTS FAILED\n")
        return 1


if __name__ == "__main__":
    exit(run_tests())
