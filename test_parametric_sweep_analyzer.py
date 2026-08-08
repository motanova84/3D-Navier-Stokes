"""
Test Suite for Parametric Sweep Analyzer

Tests the parametric_sweep_analyzer module functionality with mock data.
"""

import unittest
import numpy as np
import pandas as pd
import json
import tempfile
import shutil
from pathlib import Path
import matplotlib
matplotlib.use('Agg')  # Non-interactive backend for testing

from parametric_sweep_analyzer import (
    load_all_simulation_results,
    plot_stability_map,
    plot_frequency_emergence_validation,
    plot_classical_vs_psi_comparison
)


class TestParametricSweepAnalyzer(unittest.TestCase):
    """Test cases for the parametric sweep analyzer"""
    
    def setUp(self):
        """Set up test fixtures"""
        # Create temporary directories
        self.test_dir = tempfile.mkdtemp()
        self.results_dir = Path(self.test_dir) / 'parametric_sweep_results'
        self.output_dir = Path(self.test_dir) / 'artifacts'
        self.results_dir.mkdir(parents=True)
        self.output_dir.mkdir(parents=True)
        
        # Create mock simulation results
        self._create_mock_results()
    
    def tearDown(self):
        """Clean up test fixtures"""
        shutil.rmtree(self.test_dir)
    
    def _create_mock_results(self):
        """Create mock simulation results for testing"""
        # Mock result package 1
        package_1 = {
            'package_id': 'test_package_1',
            'results': [
                {
                    'status': 'success',
                    'params': {
                        'f0': 100.0,
                        'Re': 1000.0,
                        'nu': 0.001,
                        'N': 32,
                        'T_max': 10.0,
                        'L': 2 * np.pi
                    },
                    'results': {
                        'blowup_detected': False,
                        'blowup_time': np.nan,
                        'max_vorticity': 15.3,
                        'energy_final': 0.95,
                        'energy_variation': 0.02,
                        'dominant_frequency': 101.2,
                        'frequency_error': 0.012,
                        'bkm_integral': 45.6,
                        'bkm_converged': True,
                        'simulation_time': 120.5
                    },
                    'completed_at': '2025-01-01T12:00:00'
                },
                {
                    'status': 'success',
                    'params': {
                        'f0': 141.7,
                        'Re': 2000.0,
                        'nu': 0.0005,
                        'N': 32,
                        'T_max': 10.0,
                        'L': 2 * np.pi
                    },
                    'results': {
                        'blowup_detected': False,
                        'blowup_time': np.nan,
                        'max_vorticity': 25.8,
                        'energy_final': 0.93,
                        'energy_variation': 0.03,
                        'dominant_frequency': 142.1,
                        'frequency_error': 0.003,
                        'bkm_integral': 78.2,
                        'bkm_converged': True,
                        'simulation_time': 180.3
                    },
                    'completed_at': '2025-01-01T12:05:00'
                },
                {
                    'status': 'success',
                    'params': {
                        'f0': 200.0,
                        'Re': 5000.0,
                        'nu': 0.0002,
                        'N': 64,
                        'T_max': 10.0,
                        'L': 2 * np.pi
                    },
                    'results': {
                        'blowup_detected': True,
                        'blowup_time': 5.2,
                        'max_vorticity': 150.5,
                        'energy_final': 1.2,
                        'energy_variation': 0.15,
                        'dominant_frequency': 205.3,
                        'frequency_error': 0.027,
                        'bkm_integral': 250.0,
                        'bkm_converged': False,
                        'simulation_time': 95.7
                    },
                    'completed_at': '2025-01-01T12:10:00'
                }
            ]
        }
        
        # Save mock results
        with open(self.results_dir / 'results_package_1.json', 'w') as f:
            json.dump(package_1, f)
        
        # Mock result package 2
        package_2 = {
            'package_id': 'test_package_2',
            'results': [
                {
                    'status': 'success',
                    'params': {
                        'f0': 150.0,
                        'Re': 1500.0,
                        'nu': 0.00067,
                        'N': 32,
                        'T_max': 10.0,
                        'L': 2 * np.pi
                    },
                    'results': {
                        'blowup_detected': False,
                        'blowup_time': np.nan,
                        'max_vorticity': 20.1,
                        'energy_final': 0.94,
                        'energy_variation': 0.025,
                        'dominant_frequency': 149.5,
                        'frequency_error': -0.003,
                        'bkm_integral': 55.3,
                        'bkm_converged': True,
                        'simulation_time': 145.2
                    },
                    'completed_at': '2025-01-01T12:15:00'
                },
                {
                    'status': 'failed',  # This should be skipped
                    'params': {
                        'f0': 300.0,
                        'Re': 10000.0,
                        'nu': 0.0001,
                        'N': 64,
                        'T_max': 10.0,
                        'L': 2 * np.pi
                    },
                    'results': {},
                    'completed_at': '2025-01-01T12:20:00'
                }
            ]
        }
        
        with open(self.results_dir / 'results_package_2.json', 'w') as f:
            json.dump(package_2, f)
    
    def test_load_all_simulation_results(self):
        """Test loading simulation results from JSON files"""
        df = load_all_simulation_results(str(self.results_dir))
        
        # Should load 4 successful simulations (failed one is skipped)
        self.assertEqual(len(df), 4)
        
        # Check columns exist
        expected_columns = [
            'f0', 'Re', 'nu', 'N', 'T_max', 'L',
            'blowup_detected', 'max_vorticity', 'energy_final',
            'dominant_frequency', 'frequency_error', 'bkm_integral',
            'simulation_time', 'package_id'
        ]
        for col in expected_columns:
            self.assertIn(col, df.columns)
        
        # Check data types
        self.assertTrue(df['blowup_detected'].dtype == bool)
        self.assertTrue(df['f0'].dtype in [np.float64, float])
        self.assertTrue(df['Re'].dtype in [np.float64, float])
        
        # Check specific values
        self.assertEqual(df[df['f0'] == 141.7]['Re'].values[0], 2000.0)
        self.assertEqual(df[df['f0'] == 200.0]['blowup_detected'].values[0], True)
    
    def test_load_empty_directory(self):
        """Test loading from empty directory"""
        empty_dir = Path(self.test_dir) / 'empty'
        empty_dir.mkdir()
        
        df = load_all_simulation_results(str(empty_dir))
        self.assertEqual(len(df), 0)
    
    def test_plot_stability_map(self):
        """Test stability map generation"""
        df = load_all_simulation_results(str(self.results_dir))
        output_file = self.output_dir / 'test_stability_map.png'
        
        fig = plot_stability_map(df, str(output_file))
        
        # Check file was created
        self.assertTrue(output_file.exists())
        
        # Check figure properties
        self.assertIsNotNone(fig)
        # Should have 3 main axes (number of colorbars may vary)
        self.assertGreaterEqual(len(fig.axes), 3)
    
    def test_plot_frequency_emergence_validation(self):
        """Test frequency emergence validation plot"""
        df = load_all_simulation_results(str(self.results_dir))
        output_file = self.output_dir / 'test_frequency_validation.png'
        
        fig = plot_frequency_emergence_validation(df, str(output_file))
        
        # Check file was created
        self.assertTrue(output_file.exists())
        
        # Check figure properties
        self.assertIsNotNone(fig)
        self.assertTrue(len(fig.axes) > 0)
    
    def test_plot_classical_vs_psi_comparison(self):
        """Test NSE vs Psi-NSE comparison plot"""
        df = load_all_simulation_results(str(self.results_dir))
        output_file = self.output_dir / 'test_comparison.png'
        
        fig = plot_classical_vs_psi_comparison(df, str(output_file))
        
        # Check file was created
        self.assertTrue(output_file.exists())
        
        # Check figure properties
        self.assertIsNotNone(fig)
        self.assertEqual(len(fig.axes), 4)
    
    def test_dataframe_computations(self):
        """Test DataFrame computations and derived columns"""
        df = load_all_simulation_results(str(self.results_dir))
        
        # Test blowup detection
        blowups = df[df['blowup_detected'] == True]
        stable = df[df['blowup_detected'] == False]
        
        self.assertEqual(len(blowups), 1)
        self.assertEqual(len(stable), 3)
        
        # Test frequency error calculations
        self.assertTrue(all(df['frequency_error'].notna()))
        
        # Test that blowup time is NaN for stable cases
        self.assertTrue(all(stable['blowup_time'].isna()))
        self.assertFalse(any(blowups['blowup_time'].isna()))
    
    def test_handling_missing_data(self):
        """Test handling of missing or incomplete data"""
        # Create result with missing fields
        incomplete_package = {
            'package_id': 'incomplete',
            'results': [
                {
                    'status': 'success',
                    'params': {
                        'f0': 100.0,
                        'Re': 1000.0,
                        'nu': 0.001,
                        'N': 32,
                        'T_max': 10.0,
                        'L': 2 * np.pi
                    },
                    'results': {
                        'blowup_detected': False,
                        # Missing some fields
                        'max_vorticity': 15.0
                    },
                    'completed_at': '2025-01-01T12:00:00'
                }
            ]
        }
        
        with open(self.results_dir / 'results_incomplete.json', 'w') as f:
            json.dump(incomplete_package, f)
        
        # Should handle missing data gracefully
        df = load_all_simulation_results(str(self.results_dir))
        self.assertTrue(len(df) >= 4)  # At least original 4 results
        
        # Missing fields should be NaN
        incomplete_row = df[df['package_id'] == 'incomplete']
        if len(incomplete_row) > 0:
            self.assertTrue(pd.isna(incomplete_row['dominant_frequency'].values[0]))
    
    def test_statistics_computation(self):
        """Test statistical aggregations"""
        df = load_all_simulation_results(str(self.results_dir))
        
        # Group by f0 and compute statistics
        freq_stats = df.groupby('f0')['dominant_frequency'].agg(['mean', 'std', 'count'])
        
        self.assertTrue(len(freq_stats) > 0)
        self.assertTrue(all(freq_stats['count'] > 0))
        
        # Check success rate calculation
        success_rate = (~df['blowup_detected']).mean()
        self.assertTrue(0 <= success_rate <= 1)
        self.assertAlmostEqual(success_rate, 0.75, places=2)  # 3 out of 4


class TestAnalyzerEdgeCases(unittest.TestCase):
    """Test edge cases and error handling"""
    
    def setUp(self):
        """Set up test fixtures"""
        self.test_dir = tempfile.mkdtemp()
        self.output_dir = Path(self.test_dir) / 'artifacts'
        self.output_dir.mkdir(parents=True)
    
    def tearDown(self):
        """Clean up test fixtures"""
        shutil.rmtree(self.test_dir)
    
    def test_single_simulation(self):
        """Test analysis with only one simulation"""
        df = pd.DataFrame([{
            'f0': 141.7,
            'Re': 1000.0,
            'nu': 0.001,
            'N': 32,
            'T_max': 10.0,
            'L': 2 * np.pi,
            'blowup_detected': False,
            'blowup_time': np.nan,
            'max_vorticity': 20.0,
            'energy_final': 0.95,
            'energy_variation': 0.02,
            'dominant_frequency': 142.0,
            'frequency_error': 0.002,
            'bkm_integral': 50.0,
            'bkm_converged': True,
            'simulation_time': 120.0,
            'package_id': 'single',
            'completed_at': '2025-01-01T12:00:00'
        }])
        
        # Should not crash with single data point
        output_file = self.output_dir / 'single_stability.png'
        fig = plot_stability_map(df, str(output_file))
        self.assertIsNotNone(fig)
    
    def test_all_stable_simulations(self):
        """Test with all stable simulations (no blowups)"""
        df = pd.DataFrame([
            {
                'f0': 100.0 + i*20,
                'Re': 1000.0 + i*500,
                'nu': 0.001,
                'N': 32,
                'T_max': 10.0,
                'L': 2 * np.pi,
                'blowup_detected': False,
                'blowup_time': np.nan,
                'max_vorticity': 20.0 + i*5,
                'energy_final': 0.95,
                'energy_variation': 0.02,
                'dominant_frequency': 100.0 + i*20 + i*0.5,
                'frequency_error': 0.005,
                'bkm_integral': 50.0 + i*10,
                'bkm_converged': True,
                'simulation_time': 120.0,
                'package_id': f'stable_{i}',
                'completed_at': '2025-01-01T12:00:00'
            }
            for i in range(5)
        ])
        
        # Should handle all stable case
        output_file = self.output_dir / 'all_stable.png'
        fig = plot_stability_map(df, str(output_file))
        self.assertIsNotNone(fig)


if __name__ == '__main__':
    unittest.main()
