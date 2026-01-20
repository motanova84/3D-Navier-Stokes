"""
Tests for Ψ-NSE Visualization and Validation Tools
====================================================

Test suite for visualization and validation components

Author: QCAL ∞³ Framework
License: MIT
"""

import unittest
import numpy as np
import sys
import os

# Add PsiNSE to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from PsiNSE.visualization import (
    FlowFieldVisualizer,
    AerodynamicPerformancePlotter,
    QCALDashboard,
    ValidationSuite
)


class TestFlowFieldVisualizer(unittest.TestCase):
    """Tests for flow field visualization"""
    
    def setUp(self):
        """Initialize visualizer"""
        self.visualizer = FlowFieldVisualizer()
        
        # Mock solution
        self.mock_solution = {
            'config': type('Config', (), {
                'f0': 151.7001,
                'Nx': 32, 'Ny': 16, 'Nz': 16,
            })(),
            't_final': 1.0,
            'energy_history': np.linspace(0.1, 0.05, 50),
            'vorticity_max_history': np.exp(-np.linspace(0, 2, 50)) * 0.5,
            'coherence_history': np.sin(np.linspace(0, 4*np.pi, 50)) * 0.2 + 0.7,
            'stable': True,
            'certification_hash': '1d62f6d4',
            'frequency': 151.7001
        }
        
    def test_ascii_visualization(self):
        """Test ASCII visualization generation"""
        result = self.visualizer.visualize_solution(
            self.mock_solution,
            output_format="ascii"
        )
        
        self.assertIsInstance(result, str)
        self.assertIn("Ψ-NSE FLOW FIELD VISUALIZATION", result)
        self.assertIn("151.7001 Hz", result)
        self.assertIn("STABLE", result)
        
    def test_data_export(self):
        """Test data export format"""
        result = self.visualizer.visualize_solution(
            self.mock_solution,
            output_format="data"
        )
        
        self.assertIsInstance(result, dict)
        self.assertIn('frequency', result)
        self.assertIn('energy', result)
        self.assertIn('vorticity', result)
        self.assertIn('coherence', result)
        self.assertEqual(result['frequency'], 151.7001)
        
    def test_ascii_graph_generation(self):
        """Test ASCII graph plotting"""
        data = np.sin(np.linspace(0, 2*np.pi, 20))
        graph = self.visualizer._plot_ascii_graph(data, "Test", width=40, height=8)
        
        self.assertIsInstance(graph, str)
        self.assertIn("Test", graph)
        self.assertIn("●", graph)  # Should have data points
        
    def test_empty_data_handling(self):
        """Test handling of empty data"""
        empty_solution = {
            'config': None,
            'energy_history': [],
            'vorticity_max_history': [],
            'coherence_history': [],
            'stable': False
        }
        
        result = self.visualizer.visualize_solution(
            empty_solution,
            output_format="ascii"
        )
        
        self.assertIsInstance(result, str)
        # Should not crash with empty data


class TestAerodynamicPerformancePlotter(unittest.TestCase):
    """Tests for aerodynamic performance plotting"""
    
    def setUp(self):
        """Initialize plotter"""
        self.plotter = AerodynamicPerformancePlotter()
        
    def test_lift_curve_plot(self):
        """Test lift curve visualization"""
        angles = np.array([0, 2, 4, 6, 8])
        cl_values = 2 * np.pi * np.radians(angles)
        coherence = np.array([0.85, 0.87, 0.90, 0.92, 0.89])
        
        result = self.plotter.plot_lift_curve(angles, cl_values, coherence)
        
        self.assertIsInstance(result, str)
        self.assertIn("LIFT CURVE", result)
        self.assertIn("CL", result)
        self.assertIn("Ψ", result)
        
    def test_drag_polar_plot(self):
        """Test drag polar visualization"""
        cd_values = np.array([0.01, 0.015, 0.022, 0.030])
        cl_values = np.array([0.2, 0.4, 0.6, 0.8])
        
        result = self.plotter.plot_drag_polar(cd_values, cl_values)
        
        self.assertIsInstance(result, str)
        self.assertIn("DRAG POLAR", result)
        self.assertIn("L/D", result)
        self.assertIn("Maximum", result)
        
    def test_efficiency_comparison(self):
        """Test efficiency comparison plot"""
        result = self.plotter.plot_efficiency_comparison(
            traditional_ld=15.0,
            psi_nse_ld=18.5,
            coherence=0.92
        )
        
        self.assertIsInstance(result, str)
        self.assertIn("EFFICIENCY COMPARISON", result)
        self.assertIn("Traditional CFD", result)
        self.assertIn("Ψ-NSE", result)
        self.assertIn("Improvement", result)
        self.assertIn("151.7001 Hz", result)


class TestQCALDashboard(unittest.TestCase):
    """Tests for QCAL dashboard"""
    
    def setUp(self):
        """Initialize dashboard"""
        self.dashboard = QCALDashboard()
        
    def test_full_dashboard(self):
        """Test complete dashboard generation"""
        mining = {
            'total_value_cs': 1250.50,
            'value_per_node': 14.21,
            'coherent_work_hours': 25.5,
            'efficiency': 0.92,
            'frequency': 151.7001
        }
        
        certification = {
            'total_certifications': 15,
            'approved': 14,
            'rejected': 1,
            'approval_rate': 0.933,
            'mean_coherence': 0.905,
            'registry_hash': 'a3f9c2e1'
        }
        
        verification = {
            'psi_score': 0.912,
            'threshold': 0.888,
            'guardian_status': 'APPROVED',
            'vibration_frequency': 151.7050,
            'harmonic_alignment': 0.997
        }
        
        result = self.dashboard.generate_dashboard(
            mining, certification, verification
        )
        
        self.assertIsInstance(result, str)
        self.assertIn("QCAL ∞³ DASHBOARD", result)
        self.assertIn("COHERENCE MINING", result)
        self.assertIn("CERTIFICATION", result)
        self.assertIn("VERIFICATION", result)
        self.assertIn("151.7001 Hz", result)
        
    def test_partial_dashboard(self):
        """Test dashboard with partial data"""
        mining = {'total_value_cs': 100.0, 'frequency': 151.7001}
        
        result = self.dashboard.generate_dashboard(mining_results=mining)
        
        self.assertIsInstance(result, str)
        self.assertIn("COHERENCE MINING", result)
        
    def test_empty_dashboard(self):
        """Test dashboard with no data"""
        result = self.dashboard.generate_dashboard()
        
        self.assertIsInstance(result, str)
        self.assertIn("QCAL ∞³ DASHBOARD", result)


class TestValidationSuite(unittest.TestCase):
    """Tests for validation suite"""
    
    def setUp(self):
        """Initialize validator"""
        self.validator = ValidationSuite()
        
        # Mock valid solution
        self.valid_solution = {
            'stable': True,
            'energy_history': np.linspace(10, 5, 100),
            'coherence_history': np.ones(100) * 0.9,
            'frequency': 151.7001,
            'certification_hash': '1d62f6d4'
        }
        
        # Mock invalid solution
        self.invalid_solution = {
            'stable': False,
            'energy_history': np.array([1e10]),  # Too large
            'coherence_history': [],
            'frequency': 100.0,  # Wrong frequency
            'certification_hash': ''
        }
        
    def test_validate_valid_solution(self):
        """Test validation of valid solution"""
        result = self.validator.validate_solution(self.valid_solution)
        
        self.assertIsInstance(result, dict)
        self.assertIn('tests', result)
        self.assertIn('passed', result)
        self.assertIn('failed', result)
        self.assertTrue(result['overall_pass'])
        self.assertGreater(result['passed'], 0)
        
    def test_validate_invalid_solution(self):
        """Test validation of invalid solution"""
        result = self.validator.validate_solution(self.invalid_solution)
        
        self.assertIsInstance(result, dict)
        self.assertFalse(result['overall_pass'])
        self.assertGreater(result['failed'], 0)
        
    def test_validation_report_generation(self):
        """Test validation report generation"""
        validation = self.validator.validate_solution(self.valid_solution)
        report = self.validator.generate_validation_report(validation)
        
        self.assertIsInstance(report, str)
        self.assertIn("VALIDATION REPORT", report)
        self.assertIn("Test Results", report)
        self.assertIn("Summary", report)
        
    def test_json_export(self):
        """Test JSON export of validation results"""
        validation = self.validator.validate_solution(self.valid_solution)
        json_str = self.validator.export_validation_json(validation)
        
        self.assertIsInstance(json_str, str)
        # Should be valid JSON
        import json
        data = json.loads(json_str)
        self.assertIn('tests', data)
        self.assertIn('passed', data)
        
    def test_individual_tests(self):
        """Test individual validation tests"""
        validation = self.validator.validate_solution(self.valid_solution)
        
        test_names = [test['name'] for test in validation['tests']]
        
        self.assertIn('Stability', test_names)
        self.assertIn('Energy bounded', test_names)
        self.assertIn('Resonance frequency', test_names)
        self.assertIn('Certification hash', test_names)
        
    def test_critical_vs_warning(self):
        """Test differentiation between critical and warning tests"""
        validation = self.validator.validate_solution(self.valid_solution)
        
        critical_tests = [t for t in validation['tests'] if t.get('critical', False)]
        warning_tests = [t for t in validation['tests'] if not t.get('critical', False)]
        
        self.assertGreater(len(critical_tests), 0)
        # Should have both critical and warning level tests


def run_visualization_tests():
    """Run all visualization test suites"""
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestFlowFieldVisualizer))
    suite.addTests(loader.loadTestsFromTestCase(TestAerodynamicPerformancePlotter))
    suite.addTests(loader.loadTestsFromTestCase(TestQCALDashboard))
    suite.addTests(loader.loadTestsFromTestCase(TestValidationSuite))
    
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    return result.wasSuccessful()


if __name__ == '__main__':
    print("=" * 70)
    print("Ψ-NSE Visualization and Validation Tools - Test Suite")
    print("=" * 70)
    print()
    
    success = run_visualization_tests()
    
    print()
    print("=" * 70)
    if success:
        print("✓ ALL VISUALIZATION TESTS PASSED")
    else:
        print("✗ SOME TESTS FAILED")
    print("=" * 70)
    
    sys.exit(0 if success else 1)
