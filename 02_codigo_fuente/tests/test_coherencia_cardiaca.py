#!/usr/bin/env python3
"""
Tests for Coherencia Cardíaca Model
===================================

Tests para verificar:
1. Parámetros cardíacos
2. Escalamiento micro-macro
3. Picos espectrales en HRV
4. Estado de coherencia
5. Acoplamiento cuántico-celular
6. Simulación HRV

Author: José Manuel Mota Burruezo
Date: 31 de enero de 2026
"""

import sys
import os
import unittest
import numpy as np

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'teoria_principal'))

from coherencia_cardiaca import (
    CoherenciaCardiaca,
    CardiacParams
)


class TestCardiacParams(unittest.TestCase):
    """Test CardiacParams dataclass"""
    
    def test_default_params(self):
        """Test default parameter values"""
        params = CardiacParams()
        
        self.assertEqual(params.heart_rate_bpm, 60.0)
        self.assertEqual(params.hrv_rmssd_ms, 50.0)
        self.assertEqual(params.coherence_ratio, 0.7)
    
    def test_custom_params(self):
        """Test custom parameter values"""
        params = CardiacParams(
            heart_rate_bpm=72.0,
            hrv_rmssd_ms=60.0,
            coherence_ratio=0.8
        )
        
        self.assertEqual(params.heart_rate_bpm, 72.0)
        self.assertEqual(params.hrv_rmssd_ms, 60.0)
        self.assertEqual(params.coherence_ratio, 0.8)
    
    def test_invalid_heart_rate(self):
        """Test that negative heart rate raises error"""
        with self.assertRaises(ValueError):
            CardiacParams(heart_rate_bpm=-60.0)
    
    def test_invalid_hrv(self):
        """Test that negative HRV raises error"""
        with self.assertRaises(ValueError):
            CardiacParams(hrv_rmssd_ms=-50.0)
    
    def test_invalid_coherence_ratio(self):
        """Test that invalid coherence ratio raises error"""
        with self.assertRaises(ValueError):
            CardiacParams(coherence_ratio=1.5)
        with self.assertRaises(ValueError):
            CardiacParams(coherence_ratio=-0.1)


class TestHeartFrequency(unittest.TestCase):
    """Test heart frequency calculations"""
    
    def test_default_heart_frequency(self):
        """Test heart frequency with default params (60 bpm)"""
        model = CoherenciaCardiaca()
        freq = model.get_heart_frequency()
        
        # 60 bpm = 1 Hz
        self.assertAlmostEqual(freq, 1.0, places=4)
    
    def test_custom_heart_frequency(self):
        """Test heart frequency with custom params"""
        params = CardiacParams(heart_rate_bpm=72.0)
        model = CoherenciaCardiaca(params)
        freq = model.get_heart_frequency()
        
        # 72 bpm = 1.2 Hz
        self.assertAlmostEqual(freq, 1.2, places=4)


class TestScalingFactor(unittest.TestCase):
    """Test micro-macro scaling factor"""
    
    def test_default_scaling_factor(self):
        """Test scaling factor with default params"""
        model = CoherenciaCardiaca()
        scaling = model.get_scaling_factor()
        
        # cellular_f0 / heart_freq = 141.7001 / 1.0
        self.assertAlmostEqual(scaling, 141.7001, places=2)
    
    def test_scaling_factor_with_custom_heart_rate(self):
        """Test scaling factor with custom heart rate"""
        params = CardiacParams(heart_rate_bpm=72.0)  # 1.2 Hz
        model = CoherenciaCardiaca(params)
        scaling = model.get_scaling_factor()
        
        # 141.7001 / 1.2 ≈ 118.08
        expected = 141.7001 / 1.2
        self.assertAlmostEqual(scaling, expected, places=2)


class TestHRVSpectralPeaks(unittest.TestCase):
    """Test HRV spectral peaks"""
    
    def test_hrv_peaks_structure(self):
        """Test that HRV peaks contains expected keys"""
        model = CoherenciaCardiaca()
        peaks = model.get_hrv_spectral_peaks()
        
        required_keys = [
            "fundamental_cardiac_hz",
            "LF_center_hz",
            "HF_center_hz",
            "cellular_scaled_hz",
            "coherence_peak_hz"
        ]
        
        for key in required_keys:
            self.assertIn(key, peaks)
    
    def test_hrv_peaks_values(self):
        """Test HRV peak values"""
        model = CoherenciaCardiaca()
        peaks = model.get_hrv_spectral_peaks()
        
        self.assertAlmostEqual(peaks["fundamental_cardiac_hz"], 1.0, places=2)
        self.assertAlmostEqual(peaks["LF_center_hz"], 0.1, places=2)
        self.assertAlmostEqual(peaks["HF_center_hz"], 0.25, places=2)
        self.assertAlmostEqual(peaks["coherence_peak_hz"], 0.1, places=2)


class TestCoherenceState(unittest.TestCase):
    """Test coherence state detection"""
    
    def test_coherent_state_default(self):
        """Test that default params give coherent state"""
        model = CoherenciaCardiaca()
        
        # Default coherence_ratio is 0.7, which is >= 0.5
        self.assertTrue(model.is_coherent_state())
    
    def test_coherent_state_high(self):
        """Test high coherence state"""
        params = CardiacParams(coherence_ratio=0.9)
        model = CoherenciaCardiaca(params)
        
        self.assertTrue(model.is_coherent_state())
    
    def test_incoherent_state(self):
        """Test incoherent state"""
        params = CardiacParams(coherence_ratio=0.3)
        model = CoherenciaCardiaca(params)
        
        self.assertFalse(model.is_coherent_state())
    
    def test_custom_threshold(self):
        """Test coherence with custom threshold"""
        params = CardiacParams(coherence_ratio=0.6)
        model = CoherenciaCardiaca(params)
        
        # Should be coherent with threshold 0.5
        self.assertTrue(model.is_coherent_state(threshold=0.5))
        
        # Should not be coherent with threshold 0.7
        self.assertFalse(model.is_coherent_state(threshold=0.7))


class TestCoherenceScore(unittest.TestCase):
    """Test coherence score calculation"""
    
    def test_coherence_score_without_spectrum(self):
        """Test coherence score without spectrum (uses params)"""
        params = CardiacParams(coherence_ratio=0.7)
        model = CoherenciaCardiaca(params)
        
        score = model.calculate_coherence_score()
        self.assertAlmostEqual(score, 0.7, places=4)
    
    def test_coherence_score_with_spectrum(self):
        """Test coherence score with spectrum"""
        model = CoherenciaCardiaca()
        
        # Create a simple spectrum with a peak
        spectrum = np.array([1, 2, 5, 2, 1, 1, 1, 1, 1, 1])
        score = model.calculate_coherence_score(spectrum)
        
        # Peak power (5) / total power (16)
        expected = 5.0 / 16.0
        self.assertAlmostEqual(score, expected, places=4)
    
    def test_coherence_score_bounds(self):
        """Test that coherence score is always between 0 and 1"""
        model = CoherenciaCardiaca()
        
        # Test with various spectra
        spectra = [
            np.array([1, 1, 1, 1, 1]),
            np.array([10, 1, 1, 1, 1]),
            np.array([100, 1, 1, 1, 1]),
            np.ones(100),
        ]
        
        for spectrum in spectra:
            score = model.calculate_coherence_score(spectrum)
            self.assertGreaterEqual(score, 0.0)
            self.assertLessEqual(score, 1.0)


class TestQuantumCellularCoupling(unittest.TestCase):
    """Test quantum-cellular coupling"""
    
    def test_coupling_structure(self):
        """Test that coupling dict contains expected keys"""
        model = CoherenciaCardiaca()
        coupling = model.get_quantum_cellular_coupling()
        
        required_keys = [
            "cellular_frequency_hz",
            "cardiac_frequency_hz",
            "scaling_factor",
            "coherence_ratio",
            "is_coherent",
            "coupling_strength"
        ]
        
        for key in required_keys:
            self.assertIn(key, coupling)
    
    def test_coupling_values(self):
        """Test coupling values"""
        model = CoherenciaCardiaca()
        coupling = model.get_quantum_cellular_coupling()
        
        self.assertAlmostEqual(coupling["cellular_frequency_hz"], 141.7001, places=2)
        self.assertAlmostEqual(coupling["cardiac_frequency_hz"], 1.0, places=2)
        self.assertAlmostEqual(coupling["coherence_ratio"], 0.7, places=2)
        self.assertTrue(coupling["is_coherent"])


class TestHRVSimulation(unittest.TestCase):
    """Test HRV simulation"""
    
    def test_hrv_simulation_output(self):
        """Test that HRV simulation returns correct output"""
        model = CoherenciaCardiaca()
        t, hrv = model.simulate_hrv_response(duration_seconds=10)
        
        # Check time array
        self.assertGreater(len(t), 0)
        self.assertAlmostEqual(t[-1], 10.0, delta=0.5)
        
        # Check HRV signal
        self.assertEqual(len(t), len(hrv))
        self.assertIsInstance(hrv, np.ndarray)
    
    def test_hrv_simulation_duration(self):
        """Test HRV simulation with different durations"""
        model = CoherenciaCardiaca()
        
        for duration in [10, 30, 60, 120]:
            t, hrv = model.simulate_hrv_response(duration_seconds=duration)
            self.assertAlmostEqual(t[-1], duration, delta=1.0)
    
    def test_hrv_simulation_statistics(self):
        """Test HRV simulation statistics"""
        model = CoherenciaCardiaca()
        t, hrv = model.simulate_hrv_response(duration_seconds=60)
        
        # Mean should be close to zero (balanced signal)
        self.assertAlmostEqual(np.mean(hrv), 0.0, delta=0.2)
        
        # Standard deviation should be reasonable
        self.assertGreater(np.std(hrv), 0.1)
        self.assertLess(np.std(hrv), 2.0)


class TestTestablePredictions(unittest.TestCase):
    """Test testable predictions"""
    
    def test_predictions_structure(self):
        """Test that predictions dict contains expected keys"""
        model = CoherenciaCardiaca()
        predictions = model.get_testable_predictions()
        
        required_keys = [
            "hrv_spectral_peaks",
            "expected_coherence_frequency_hz",
            "cellular_to_cardiac_scaling",
            "minimum_coherence_for_health",
            "optimal_coherence",
            "test_organism",
            "measurement_method",
            "validation_criterion"
        ]
        
        for key in required_keys:
            self.assertIn(key, predictions)
    
    def test_predictions_values(self):
        """Test prediction values"""
        model = CoherenciaCardiaca()
        predictions = model.get_testable_predictions()
        
        self.assertAlmostEqual(predictions["expected_coherence_frequency_hz"], 0.1, places=2)
        self.assertEqual(predictions["minimum_coherence_for_health"], 0.5)
        self.assertEqual(predictions["optimal_coherence"], 0.7)
        self.assertIn("C. elegans", predictions["test_organism"])


class TestSummary(unittest.TestCase):
    """Test summary generation"""
    
    def test_summary_contains_all_sections(self):
        """Test that summary contains all sections"""
        model = CoherenciaCardiaca()
        summary = model.get_summary()
        
        required_keys = [
            "heart_rate_bpm",
            "heart_rate_hz",
            "hrv_rmssd_ms",
            "coherence_ratio",
            "cellular_fundamental_hz",
            "micro_macro_scaling",
            "is_coherent_state",
            "hrv_spectral_peaks",
            "quantum_cellular_coupling",
            "testable_predictions"
        ]
        
        for key in required_keys:
            self.assertIn(key, summary)
    
    def test_summary_values(self):
        """Test summary values for default params"""
        model = CoherenciaCardiaca()
        summary = model.get_summary()
        
        self.assertEqual(summary["heart_rate_bpm"], 60.0)
        self.assertAlmostEqual(summary["heart_rate_hz"], 1.0)
        self.assertEqual(summary["coherence_ratio"], 0.7)
        self.assertTrue(summary["is_coherent_state"])


class TestDemonstration(unittest.TestCase):
    """Test demonstration output"""
    
    def test_print_demonstration_runs(self):
        """Test that print_demonstration runs without error"""
        import io
        from contextlib import redirect_stdout
        
        model = CoherenciaCardiaca()
        
        # Capture output
        f = io.StringIO()
        with redirect_stdout(f):
            model.print_demonstration()
        
        output = f.getvalue()
        
        # Check that output contains key phrases
        self.assertIn("COHERENCIA CARDÍACA", output)
        self.assertIn("141.7", output)
        self.assertIn("COHERENTE", output)
        self.assertIn("HRV", output)


def run_tests():
    """Run all tests"""
    unittest.main(argv=[''], verbosity=2, exit=False)


if __name__ == "__main__":
    run_tests()
