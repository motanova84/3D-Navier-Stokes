"""
Test Suite for Universal Validation Framework

Tests the multi-system validation of f₀ = 141.7 Hz
"""

import unittest
import numpy as np
import sys
import os
from pathlib import Path

# Add parent directory to path for imports
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from universal_validation_framework import (
    UniversalFrequency,
    DESIValidator,
    IGETSValidator,
    LISAValidator,
    EEGValidator,
    HelioseismologyValidator,
    UniversalValidator
)


class TestUniversalFrequency(unittest.TestCase):
    """Test cases for UniversalFrequency class"""
    
    def setUp(self):
        """Initialize frequency object for each test"""
        self.f0_obj = UniversalFrequency()
    
    def test_fundamental_frequency(self):
        """Test that fundamental frequency is correctly set"""
        self.assertAlmostEqual(self.f0_obj.f0, 141.7001, places=4)
    
    def test_harmonics(self):
        """Test harmonic generation"""
        harmonics = self.f0_obj.harmonics(n_max=3)
        expected = np.array([141.7001, 283.4002, 425.1003])
        np.testing.assert_array_almost_equal(harmonics, expected, decimal=3)
    
    def test_subharmonics(self):
        """Test subharmonic generation"""
        subharmonics = self.f0_obj.subharmonics(n_max=2)
        expected = np.array([141.7001/2, 141.7001/3])
        np.testing.assert_array_almost_equal(subharmonics, expected, decimal=4)
    
    def test_tolerance_band(self):
        """Test tolerance band calculation"""
        f_min, f_max = self.f0_obj.tolerance_band(tolerance_pct=0.5)
        expected_min = 141.7001 * (1 - 0.005)
        expected_max = 141.7001 * (1 + 0.005)
        self.assertAlmostEqual(f_min, expected_min, places=4)
        self.assertAlmostEqual(f_max, expected_max, places=4)
    
    def test_all_resonances(self):
        """Test all resonances include subharmonics, fundamental, and harmonics"""
        resonances = self.f0_obj.all_resonances()
        # Should have 3 subharmonics + 1 fundamental + 5 harmonics = 9 total
        self.assertEqual(len(resonances), 9)
        # Fundamental should be in the middle
        self.assertIn(self.f0_obj.f0, resonances)


class TestDESIValidator(unittest.TestCase):
    """Test cases for DESI validator"""
    
    def setUp(self):
        """Initialize DESI validator"""
        self.validator = DESIValidator()
    
    def test_initialization(self):
        """Test validator initializes correctly"""
        self.assertEqual(self.validator.name, "DESI (Estructura Cósmica)")
        self.assertIsInstance(self.validator.f0, UniversalFrequency)
    
    def test_search_signal(self):
        """Test signal search returns proper result structure"""
        result = self.validator.search_signal({})
        
        # Check required keys
        self.assertIn('system', result)
        self.assertIn('frequency_detected', result)
        self.assertIn('snr', result)
        self.assertIn('significance_sigma', result)
        self.assertIn('method', result)
        self.assertIn('data_source', result)
        self.assertIn('detection_confidence', result)
        
        # Check values
        self.assertEqual(result['system'], self.validator.name)
        self.assertIsInstance(result['frequency_detected'], float)
        self.assertGreater(result['snr'], 0)


class TestIGETSValidator(unittest.TestCase):
    """Test cases for IGETS validator"""
    
    def setUp(self):
        """Initialize IGETS validator"""
        self.validator = IGETSValidator()
    
    def test_initialization(self):
        """Test validator initializes correctly"""
        self.assertEqual(self.validator.name, "IGETS (Mareas Terrestres)")
        self.assertIsInstance(self.validator.f0, UniversalFrequency)
    
    def test_generate_synthetic_data(self):
        """Test synthetic data generation"""
        duration_hours = 1.0  # Short duration for testing
        t, g = self.validator.generate_synthetic_data(duration_hours)
        
        # Check array shapes
        self.assertEqual(len(t), len(g))
        self.assertGreater(len(t), 0)
        
        # Check time array
        self.assertAlmostEqual(t[0], 0.0)
        # Check within 1% of expected duration
        self.assertAlmostEqual(t[-1], duration_hours * 3600, delta=36)
        
        # Check data is not all zeros
        self.assertGreater(np.std(g), 0)
    
    def test_search_signal(self):
        """Test signal search on synthetic data"""
        duration_hours = 1.0  # Short duration for testing
        t, g = self.validator.generate_synthetic_data(duration_hours)
        result = self.validator.search_signal(t, g)
        
        # Check required keys
        self.assertIn('system', result)
        self.assertIn('frequency_detected', result)
        self.assertIn('frequency_expected', result)
        self.assertIn('snr', result)
        self.assertIn('significance_sigma', result)
        
        # Check frequency is in reasonable range
        self.assertGreater(result['frequency_detected'], 0)
        self.assertLess(result['frequency_detected'], 1000)


class TestLISAValidator(unittest.TestCase):
    """Test cases for LISA validator"""
    
    def setUp(self):
        """Initialize LISA validator"""
        self.validator = LISAValidator()
    
    def test_initialization(self):
        """Test validator initializes correctly"""
        self.assertEqual(self.validator.name, "LISA (Ondas Gravitacionales)")
        self.assertIsInstance(self.validator.f0, UniversalFrequency)
    
    def test_search_signal(self):
        """Test signal search returns proper result structure"""
        result = self.validator.search_signal()
        
        # Check required keys
        self.assertIn('system', result)
        self.assertIn('frequency_target', result)
        self.assertIn('frequency_fundamental', result)
        self.assertIn('harmonic_number', result)
        self.assertIn('detection_confidence', result)
        
        # Check that it's looking for subharmonic
        self.assertEqual(result['harmonic_number'], -1000)
        self.assertAlmostEqual(
            result['frequency_target'],
            result['frequency_fundamental'] / 1000,
            places=4
        )


class TestEEGValidator(unittest.TestCase):
    """Test cases for EEG validator"""
    
    def setUp(self):
        """Initialize EEG validator"""
        self.validator = EEGValidator()
    
    def test_initialization(self):
        """Test validator initializes correctly"""
        self.assertEqual(self.validator.name, "EEG (Actividad Cerebral)")
        self.assertIsInstance(self.validator.f0, UniversalFrequency)
    
    def test_generate_synthetic_eeg(self):
        """Test synthetic EEG data generation"""
        duration_s = 10.0  # Short duration for testing
        t, eeg = self.validator.generate_synthetic_eeg(duration_s)
        
        # Check array shapes
        self.assertEqual(len(t), len(eeg))
        self.assertGreater(len(t), 0)
        
        # Check time array
        self.assertAlmostEqual(t[0], 0.0)
        self.assertLess(abs(t[-1] - duration_s), 0.01)
        
        # Check data is not all zeros
        self.assertGreater(np.std(eeg), 0)
    
    def test_search_signal(self):
        """Test signal search on synthetic EEG"""
        duration_s = 10.0  # Short duration for testing
        t, eeg = self.validator.generate_synthetic_eeg(duration_s)
        result = self.validator.search_signal(t, eeg)
        
        # Check required keys
        self.assertIn('system', result)
        self.assertIn('frequency_detected', result)
        self.assertIn('frequency_expected', result)
        self.assertIn('snr', result)
        self.assertIn('significance_sigma', result)
        
        # Check frequency is in reasonable range
        self.assertGreater(result['frequency_detected'], 0)
        self.assertLess(result['frequency_detected'], 500)


class TestHelioseismologyValidator(unittest.TestCase):
    """Test cases for Helioseismology validator"""
    
    def setUp(self):
        """Initialize Helioseismology validator"""
        self.validator = HelioseismologyValidator()
    
    def test_initialization(self):
        """Test validator initializes correctly"""
        self.assertEqual(self.validator.name, "Heliosismología (Sol)")
        self.assertIsInstance(self.validator.f0, UniversalFrequency)
    
    def test_search_signal(self):
        """Test signal search returns proper result structure"""
        result = self.validator.search_signal()
        
        # Check required keys
        self.assertIn('system', result)
        self.assertIn('frequency_target', result)
        self.assertIn('frequency_fundamental', result)
        self.assertIn('harmonic_number', result)
        self.assertIn('detection_confidence', result)
        
        # Check that it's looking for subharmonic
        self.assertEqual(result['harmonic_number'], -50000)


class TestUniversalValidator(unittest.TestCase):
    """Test cases for UniversalValidator orchestrator"""
    
    def setUp(self):
        """Initialize universal validator"""
        self.validator = UniversalValidator()
    
    def test_initialization(self):
        """Test validator initializes correctly"""
        self.assertIsInstance(self.validator.f0, UniversalFrequency)
        self.assertIsInstance(self.validator.validators, list)
    
    def test_run_all_validations(self):
        """Test running all validations"""
        # This will generate output but should complete
        results = self.validator.run_all_validations()
        
        # Check we got results from all systems
        self.assertGreater(len(results), 0)
        self.assertEqual(len(results), 5)  # 5 systems
        
        # Check each result has required keys
        for result in results:
            self.assertIn('system', result)
            self.assertIn('method', result)
            self.assertIn('data_source', result)
            self.assertIn('detection_confidence', result)
    
    def test_generate_report(self):
        """Test report generation"""
        results = self.validator.run_all_validations()
        report = self.validator.generate_report(results)
        
        # Check report is non-empty string
        self.assertIsInstance(report, str)
        self.assertGreater(len(report), 0)
        
        # Check key content is present
        self.assertIn('f₀ = 141.7', report)
        self.assertIn('José Manuel Mota Burruezo', report)
        self.assertIn('SISTEMAS ANALIZADOS', report)


if __name__ == '__main__':
    # Run tests
    unittest.main(verbosity=2)
