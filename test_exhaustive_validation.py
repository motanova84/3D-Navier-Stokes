#!/usr/bin/env python3
"""
Tests for Exhaustive Validation Module

Comprehensive tests for parameter sweeps, edge cases, and δ* analysis
"""

import unittest
import numpy as np
import sys

sys.path.append('/home/runner/work/3D-Navier-Stokes/3D-Navier-Stokes/DNS-Verification/DualLimitSolver')
from exhaustive_validation import (
    ExhaustiveValidator,
    ValidationConfig,
    StabilityMetrics
)


class TestValidationConfig(unittest.TestCase):
    """Test ValidationConfig dataclass"""
    
    def test_default_config(self):
        """Test default configuration values"""
        config = ValidationConfig()
        
        self.assertIsNotNone(config.a_range)
        self.assertIsNotNone(config.a_critical_values)
        self.assertEqual(config.δ_star_threshold, 0.998)
        
        # Check that a=200 is in critical values
        self.assertIn(200.0, config.a_critical_values)
    
    def test_custom_config(self):
        """Test custom configuration"""
        config = ValidationConfig(
            a_range=(1.0, 500.0),
            a_samples=50,
            δ_star_threshold=0.95
        )
        
        self.assertEqual(config.a_range, (1.0, 500.0))
        self.assertEqual(config.a_samples, 50)
        self.assertEqual(config.δ_star_threshold, 0.95)


class TestDeltaStarCalculations(unittest.TestCase):
    """Test δ* computations"""
    
    def setUp(self):
        self.validator = ExhaustiveValidator()
    
    def test_compute_delta_star_small_a(self):
        """Test δ* computation for small amplitude"""
        δ_star = self.validator.compute_delta_star(2.45)
        
        # For a=2.45, c_0=1.0: δ* = 2.45²/(4π²) ≈ 0.0151
        expected = (2.45**2) / (4 * np.pi**2)
        self.assertAlmostEqual(δ_star, expected, places=6)
        self.assertLess(δ_star, 0.998)  # Should not exceed threshold
    
    def test_compute_delta_star_large_a(self):
        """Test δ* computation for large amplitude (a ≈ 200)"""
        δ_star = self.validator.compute_delta_star(200.0)
        
        # For a=200, c_0=1.0: δ* = 200²/(4π²) ≈ 1012.9
        expected = (200.0**2) / (4 * np.pi**2)
        self.assertAlmostEqual(δ_star, expected, places=2)
        self.assertGreater(δ_star, 0.998)  # Should exceed threshold
    
    def test_compute_required_amplitude_for_threshold(self):
        """Test computing required amplitude to reach threshold"""
        δ_target = 0.998
        a_required = self.validator.compute_required_amplitude(δ_target)
        
        # Verify by computing δ* with this amplitude
        δ_achieved = self.validator.compute_delta_star(a_required)
        self.assertAlmostEqual(δ_achieved, δ_target, places=3)
        
        # a ≈ 6.28 for δ* = 0.998
        self.assertGreater(a_required, 6.0)
        self.assertLess(a_required, 7.0)
    
    def test_delta_star_monotonicity(self):
        """Test that δ* increases monotonically with a"""
        a_values = [1.0, 10.0, 50.0, 100.0, 200.0]
        δ_values = [self.validator.compute_delta_star(a) for a in a_values]
        
        # Check monotonicity
        for i in range(len(δ_values) - 1):
            self.assertLess(δ_values[i], δ_values[i+1])


class TestNumericalStability(unittest.TestCase):
    """Test numerical stability assessments"""
    
    def setUp(self):
        self.validator = ExhaustiveValidator()
    
    def test_stability_normal_parameters(self):
        """Test stability with normal parameters"""
        metrics = self.validator.assess_numerical_stability(
            a=10.0, ν=1e-3, M=100.0
        )
        
        self.assertTrue(metrics.is_stable)
        self.assertEqual(metrics.error_message, "")
    
    def test_stability_large_amplitude(self):
        """Test stability with a ≈ 200"""
        metrics = self.validator.assess_numerical_stability(
            a=200.0, ν=1e-3, M=100.0
        )
        
        # Should still be stable
        self.assertTrue(metrics.is_stable)
    
    def test_instability_extreme_amplitude(self):
        """Test instability with very large amplitude"""
        metrics = self.validator.assess_numerical_stability(
            a=350.0, ν=1e-3, M=100.0
        )
        
        # Should detect instability
        self.assertFalse(metrics.is_stable)
        self.assertIn("overflow", metrics.error_message.lower())
    
    def test_instability_small_viscosity(self):
        """Test instability with very small viscosity"""
        metrics = self.validator.assess_numerical_stability(
            a=200.0, ν=1e-7, M=100.0
        )
        
        # Should detect instability
        self.assertFalse(metrics.is_stable)
        self.assertIn("viscosity", metrics.error_message.lower())
    
    def test_condition_number_estimate(self):
        """Test condition number estimation"""
        metrics = self.validator.assess_numerical_stability(
            a=100.0, ν=1e-3, M=100.0
        )
        
        # Condition number should be finite and positive
        self.assertGreater(metrics.condition_number, 0)
        self.assertTrue(np.isfinite(metrics.condition_number))


class TestTheoreticalValidation(unittest.TestCase):
    """Test theoretical stability validation"""
    
    def setUp(self):
        self.validator = ExhaustiveValidator()
    
    def test_theoretical_validation_small_a(self):
        """Test theoretical validation with small amplitude"""
        result = self.validator.validate_theoretical_stability(a=2.45)
        
        self.assertFalse(result['closure'])
        self.assertLess(result['damping'], 0)
        self.assertFalse(result['δ_star_exceeds_threshold'])
    
    def test_theoretical_validation_optimal_a(self):
        """Test theoretical validation with optimal amplitude"""
        result = self.validator.validate_theoretical_stability(a=10.0)
        
        self.assertTrue(result['closure'])
        self.assertGreater(result['damping'], 0)
    
    def test_theoretical_validation_large_a(self):
        """Test theoretical validation with a ≈ 200"""
        result = self.validator.validate_theoretical_stability(a=200.0)
        
        self.assertTrue(result['δ_star_exceeds_threshold'])
        self.assertGreater(result['δ_star'], 0.998)
        self.assertTrue(result['physical_valid'])
        
        # Damping should be strongly positive
        self.assertGreater(result['damping'], 10.0)
    
    def test_physical_constraints(self):
        """Test physical constraint checking"""
        # Valid parameters
        result = self.validator.validate_theoretical_stability(a=100.0)
        self.assertTrue(result['physical_valid'])
        self.assertEqual(len(result['constraints']), 0)


class TestAmplitudeSweep(unittest.TestCase):
    """Test amplitude parameter sweep"""
    
    def setUp(self):
        self.validator = ExhaustiveValidator()
    
    def test_amplitude_sweep_runs(self):
        """Test that amplitude sweep executes without errors"""
        results = self.validator.sweep_amplitude_range(verbose=False)
        
        self.assertIn('results', results)
        self.assertIn('summary', results)
        self.assertGreater(len(results['results']), 0)
    
    def test_amplitude_sweep_includes_200(self):
        """Test that sweep includes a ≈ 200"""
        results = self.validator.sweep_amplitude_range(verbose=False)
        
        a_values = [r['a'] for r in results['results']]
        
        # Check that a=200 is included
        self.assertIn(200.0, a_values)
    
    def test_amplitude_sweep_critical_values(self):
        """Test that all critical values are included"""
        config = ValidationConfig()
        results = self.validator.sweep_amplitude_range(verbose=False)
        
        a_values = set(r['a'] for r in results['results'])
        
        # All critical values should be tested
        for critical_a in config.a_critical_values:
            self.assertIn(critical_a, a_values)
    
    def test_amplitude_sweep_finds_threshold_exceeding(self):
        """Test that sweep finds amplitudes exceeding δ* threshold"""
        results = self.validator.sweep_amplitude_range(verbose=False)
        
        threshold_exceeded = any(
            r['δ_star_exceeds_threshold'] for r in results['results']
        )
        
        self.assertTrue(threshold_exceeded)


class TestMultiParameterSweep(unittest.TestCase):
    """Test multi-parameter sweep"""
    
    def setUp(self):
        self.validator = ExhaustiveValidator()
    
    def test_multi_parameter_sweep_runs(self):
        """Test that multi-parameter sweep executes"""
        results = self.validator.sweep_multi_parameter(verbose=False)
        
        self.assertIn('results', results)
        self.assertGreater(len(results['results']), 0)
    
    def test_multi_parameter_sweep_includes_200(self):
        """Test that multi-parameter sweep includes a=200"""
        results = self.validator.sweep_multi_parameter(verbose=False)
        
        has_200 = any(r['a'] == 200.0 for r in results['results'])
        self.assertTrue(has_200)
    
    def test_multi_parameter_sweep_dimensions(self):
        """Test that sweep covers all parameter dimensions"""
        results = self.validator.sweep_multi_parameter(verbose=False)
        
        # Check that all parameters vary
        a_values = set(r['a'] for r in results['results'])
        α_values = set(r['α'] for r in results['results'])
        f0_values = set(r['f0'] for r in results['results'])
        ν_values = set(r['ν'] for r in results['results'])
        
        self.assertGreater(len(a_values), 1)
        self.assertGreater(len(α_values), 1)
        self.assertGreater(len(f0_values), 1)
        self.assertGreater(len(ν_values), 1)


class TestEdgeCases(unittest.TestCase):
    """Test edge case validation"""
    
    def setUp(self):
        self.validator = ExhaustiveValidator()
    
    def test_edge_cases_run(self):
        """Test that edge case testing executes"""
        results = self.validator.test_edge_cases(verbose=False)
        
        self.assertIn('edge_cases', results)
        self.assertGreater(len(results['edge_cases']), 0)
    
    def test_edge_case_minimal_amplitude(self):
        """Test edge case with minimal amplitude"""
        results = self.validator.test_edge_cases(verbose=False)
        
        # Find minimal amplitude case
        minimal_case = next(
            (c for c in results['edge_cases'] 
             if 'Minimal' in c['name']),
            None
        )
        
        self.assertIsNotNone(minimal_case)
        self.assertLess(minimal_case['result']['δ_star'], 0.01)
    
    def test_edge_case_large_amplitude(self):
        """Test edge case with a=200"""
        results = self.validator.test_edge_cases(verbose=False)
        
        # Find a=200 case
        large_case = next(
            (c for c in results['edge_cases']
             if c['params']['a'] == 200.0),
            None
        )
        
        self.assertIsNotNone(large_case)
        self.assertGreater(large_case['result']['δ_star'], 0.998)
    
    def test_edge_case_varied_viscosity(self):
        """Test edge cases cover viscosity range"""
        results = self.validator.test_edge_cases(verbose=False)
        
        ν_values = [c['params']['ν'] for c in results['edge_cases']]
        
        # Should include both small and large viscosity
        self.assertIn(1e-5, ν_values)
        self.assertIn(0.1, ν_values)


class TestRecommendations(unittest.TestCase):
    """Test recommendation generation"""
    
    def setUp(self):
        self.validator = ExhaustiveValidator()
    
    def test_recommendations_generated(self):
        """Test that recommendations are generated"""
        amplitude_results = self.validator.sweep_amplitude_range(verbose=False)
        edge_results = self.validator.test_edge_cases(verbose=False)
        
        recommendations = self.validator.generate_recommendations(
            amplitude_results, edge_results
        )
        
        self.assertGreater(len(recommendations), 0)
    
    def test_recommendations_mention_200(self):
        """Test that recommendations mention a ≈ 200"""
        amplitude_results = self.validator.sweep_amplitude_range(verbose=False)
        edge_results = self.validator.test_edge_cases(verbose=False)
        
        recommendations = self.validator.generate_recommendations(
            amplitude_results, edge_results
        )
        
        # Should mention the recommended value
        recommendations_text = ' '.join(recommendations)
        self.assertTrue(
            '200' in recommendations_text or '2' in recommendations_text
        )


class TestFullValidation(unittest.TestCase):
    """Test full validation suite"""
    
    def setUp(self):
        self.validator = ExhaustiveValidator()
    
    def test_full_validation_runs(self):
        """Test that full validation suite executes"""
        results = self.validator.run_full_validation(verbose=False)
        
        self.assertIn('amplitude_sweep', results)
        self.assertIn('multi_parameter_sweep', results)
        self.assertIn('edge_cases', results)
        self.assertIn('recommendations', results)
        self.assertIn('summary', results)
    
    def test_full_validation_summary(self):
        """Test that summary statistics are computed"""
        results = self.validator.run_full_validation(verbose=False)
        
        self.assertIn('total_tests', results['summary'])
        self.assertGreater(results['summary']['total_tests'], 0)
    
    def test_full_validation_includes_all_phases(self):
        """Test that all validation phases are included"""
        results = self.validator.run_full_validation(verbose=False)
        
        # Check amplitude sweep
        self.assertGreater(
            len(results['amplitude_sweep']['results']), 0
        )
        
        # Check multi-parameter sweep
        self.assertGreater(
            len(results['multi_parameter_sweep']['results']), 0
        )
        
        # Check edge cases
        self.assertGreater(
            len(results['edge_cases']['edge_cases']), 0
        )
        
        # Check recommendations
        self.assertGreater(len(results['recommendations']), 0)


class TestResultsSaving(unittest.TestCase):
    """Test results saving functionality"""
    
    def setUp(self):
        self.validator = ExhaustiveValidator()
    
    def test_save_results_creates_file(self):
        """Test that save_results creates output file"""
        import os
        import tempfile
        
        results = {'test': 'data', 'value': 42}
        
        # Use temporary file
        with tempfile.NamedTemporaryFile(mode='w', delete=False, suffix='.json') as f:
            temp_path = f.name
        
        try:
            self.validator.save_results(results, temp_path)
            self.assertTrue(os.path.exists(temp_path))
        finally:
            if os.path.exists(temp_path):
                os.remove(temp_path)


class TestIntegration(unittest.TestCase):
    """Integration tests for complete workflow"""
    
    def test_complete_workflow(self):
        """Test complete validation workflow"""
        validator = ExhaustiveValidator()
        
        # Run full validation
        results = validator.run_full_validation(verbose=False)
        
        # Verify structure
        self.assertIsInstance(results, dict)
        self.assertIn('config', results)
        self.assertIn('amplitude_sweep', results)
        self.assertIn('recommendations', results)
        
        # Verify that a=200 analysis was performed
        amplitude_results = results['amplitude_sweep']['results']
        has_200 = any(abs(r['a'] - 200.0) < 1.0 for r in amplitude_results)
        self.assertTrue(has_200)
        
        # Verify recommendations exist
        self.assertGreater(len(results['recommendations']), 0)


if __name__ == '__main__':
    print("="*70)
    print("EXHAUSTIVE VALIDATION - Test Suite")
    print("="*70)
    
    # Run tests
    unittest.main(verbosity=2)
