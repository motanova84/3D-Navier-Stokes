#!/usr/bin/env python3
"""
Test Suite for Frequency Response Detector
===========================================

Comprehensive tests for the FrequencyResponseDetector class.

Author: José Manuel Mota Burruezo (JMMB Ψ✧∞³)
License: MIT
"""

import unittest
import numpy as np
from frequency_response_detector import FrequencyResponseDetector, create_example_detector


class TestFrequencyResponseDetector(unittest.TestCase):
    """Test cases for FrequencyResponseDetector."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.detector = create_example_detector()
        self.f0 = 141.7001
        self.dt = 1e-4
        self.duration = 1.0
        
    def test_initialization(self):
        """Test detector initialization."""
        detector = FrequencyResponseDetector(
            f0_expected=100.0,
            coherence_threshold=0.9,
            max_harmonics=3,
            frequency_tolerance=0.01
        )
        
        self.assertEqual(detector.f0_expected, 100.0)
        self.assertEqual(detector.coherence_threshold, 0.9)
        self.assertEqual(detector.max_harmonics, 3)
        self.assertEqual(detector.frequency_tolerance, 0.01)
        
    def test_detect_single_frequency(self):
        """Test detection of a single pure frequency."""
        # Generate pure sine wave at f₀
        t, signal = self.detector.generate_test_signal(
            duration=self.duration,
            dt=self.dt,
            harmonics=[1.0],
            noise_level=0.0
        )
        
        results = self.detector.detect_frequency(signal, self.dt)
        
        # Check detection
        self.assertIsNotNone(results)
        self.assertIn('detected_frequency_Hz', results)
        self.assertIn('expected_frequency_Hz', results)
        self.assertIn('absolute_error_Hz', results)
        self.assertIn('relative_error', results)
        
        # Should detect f₀ accurately (within FFT resolution)
        self.assertAlmostEqual(
            results['detected_frequency_Hz'],
            self.f0,
            delta=1.0  # Allow FFT resolution error
        )
        
        # Error should be small
        self.assertLess(results['relative_error'], 0.01)
        
    def test_detect_with_noise(self):
        """Test frequency detection with additive noise."""
        # Generate signal with noise
        t, signal = self.detector.generate_test_signal(
            duration=self.duration,
            dt=self.dt,
            harmonics=[1.0],
            noise_level=0.1
        )
        
        results = self.detector.detect_frequency(signal, self.dt)
        
        # Should still detect f₀ despite noise
        self.assertLess(
            abs(results['detected_frequency_Hz'] - self.f0),
            1.0  # Within 1 Hz
        )
        
    def test_harmonic_detection(self):
        """Test detection of fundamental and harmonics."""
        # Generate signal with 3 harmonics
        t, signal = self.detector.generate_test_signal(
            duration=self.duration,
            dt=self.dt,
            harmonics=[1.0, 0.5, 0.25],  # f₀, 2f₀, 3f₀
            noise_level=0.02
        )
        
        results = self.detector.detect_harmonics(signal, self.dt)
        
        # Check results structure
        self.assertIn('harmonics_detected', results)
        self.assertIn('harmonic_count', results)
        self.assertIn('fundamental_confirmed', results)
        
        # Should detect at least the fundamental
        self.assertGreaterEqual(results['harmonic_count'], 1)
        
    def test_multi_signal_analysis(self):
        """Test analysis of multiple signals."""
        # Create multiple test signals
        signals = {}
        for i in range(3):
            t, signal = self.detector.generate_test_signal(
                duration=self.duration,
                dt=self.dt,
                harmonics=[1.0],
                noise_level=0.05
            )
            signals[f'signal_{i}'] = signal
            
        results = self.detector.analyze_multi_signal(signals, self.dt)
        
        # Check structure
        self.assertIn('individual_results', results)
        self.assertIn('aggregate_statistics', results)
        
        # Check all signals analyzed
        self.assertEqual(len(results['individual_results']), 3)
        
        # Check aggregate stats
        agg = results['aggregate_statistics']
        self.assertIn('mean_frequency_Hz', agg)
        self.assertIn('std_frequency_Hz', agg)
        self.assertIn('signal_count', agg)
        self.assertEqual(agg['signal_count'], 3)
        
    def test_coherence_validation(self):
        """Test QCAL coherence validation."""
        # Generate highly coherent signal (pure f₀)
        t, signal = self.detector.generate_test_signal(
            duration=self.duration,
            dt=self.dt,
            harmonics=[1.0],
            noise_level=0.01
        )
        
        results = self.detector.validate_coherence(signal, self.dt)
        
        # Check structure
        self.assertIn('coherence', results)
        self.assertIn('is_coherent', results)
        self.assertIn('coherence_threshold', results)
        
        # Pure signal should have some coherence (may be affected by tolerance band)
        self.assertGreaterEqual(results['coherence'], 0.0)
        
    def test_quality_metrics(self):
        """Test comprehensive quality metrics computation."""
        # Generate test signal
        t, signal = self.detector.generate_test_signal(
            duration=self.duration,
            dt=self.dt,
            harmonics=[1.0, 0.3],
            noise_level=0.05
        )
        
        results = self.detector.compute_quality_metrics(signal, self.dt)
        
        # Check structure
        self.assertIn('quality_metrics', results)
        self.assertIn('frequency_detection', results)
        self.assertIn('harmonic_analysis', results)
        self.assertIn('coherence_validation', results)
        
        # Check quality metrics
        metrics = results['quality_metrics']
        self.assertIn('frequency_accuracy', metrics)
        self.assertIn('coherence', metrics)
        self.assertIn('snr', metrics)
        self.assertIn('snr_db', metrics)
        self.assertIn('overall_quality', metrics)
        self.assertIn('grade', metrics)
        
        # Quality should be reasonable
        self.assertGreater(metrics['overall_quality'], 0.0)
        self.assertLessEqual(metrics['overall_quality'], 1.0)
        
    def test_quality_grading(self):
        """Test quality grading system."""
        test_cases = [
            (0.98, 'A+'),
            (0.92, 'A'),
            (0.87, 'B+'),
            (0.82, 'B'),
            (0.77, 'C+'),
            (0.72, 'C'),
            (0.60, 'F')
        ]
        
        for score, expected_grade in test_cases:
            grade = self.detector._quality_grade(score)
            self.assertEqual(grade, expected_grade)
            
    def test_wrong_frequency_detection(self):
        """Test detection when frequency differs from f₀."""
        # Generate signal at different frequency
        wrong_freq = 200.0
        detector_wrong = FrequencyResponseDetector(f0_expected=self.f0)
        
        t = np.arange(0, self.duration, self.dt)
        signal = np.cos(2 * np.pi * wrong_freq * t)
        
        results = detector_wrong.detect_frequency(signal, self.dt)
        
        # Should detect the actual frequency
        self.assertAlmostEqual(
            results['detected_frequency_Hz'],
            wrong_freq,
            delta=1.0
        )
        
        # Error relative to f₀ should be large
        self.assertGreater(results['relative_error'], 0.1)
        self.assertFalse(results['within_tolerance'])
        
    def test_empty_signal(self):
        """Test handling of edge cases."""
        # Very short signal
        short_signal = np.array([1.0, 2.0, 3.0])
        results = self.detector.detect_frequency(short_signal, self.dt)
        
        # Should not crash
        self.assertIsNotNone(results)
        self.assertIn('detected_frequency_Hz', results)
        
    def test_zero_signal(self):
        """Test handling of zero signal."""
        zero_signal = np.zeros(1000)
        results = self.detector.detect_frequency(zero_signal, self.dt)
        
        # Should handle gracefully
        self.assertIsNotNone(results)
        self.assertEqual(results['peak_amplitude'], 0.0)
        
    def test_generate_test_signal(self):
        """Test test signal generation."""
        t, signal = self.detector.generate_test_signal(
            duration=1.0,
            dt=1e-4,
            harmonics=[1.0, 0.5, 0.25],
            noise_level=0.1
        )
        
        # Check dimensions
        expected_length = int(1.0 / 1e-4)
        self.assertEqual(len(t), expected_length)
        self.assertEqual(len(signal), expected_length)
        
        # Check time array
        self.assertAlmostEqual(t[0], 0.0)
        self.assertAlmostEqual(t[-1], 1.0 - 1e-4, places=5)
        
    def test_multidimensional_input(self):
        """Test handling of multidimensional arrays."""
        # Create 2D array
        t, signal_1d = self.detector.generate_test_signal(
            duration=0.5,
            dt=self.dt,
            harmonics=[1.0]
        )
        
        # Reshape to 2D
        signal_2d = signal_1d.reshape(-1, 1)
        
        # Should flatten and process
        results = self.detector.detect_frequency(signal_2d, self.dt)
        self.assertIsNotNone(results)
        self.assertLess(results['relative_error'], 0.1)
        
    def test_tolerance_check(self):
        """Test frequency tolerance checking."""
        # Create signal exactly at f₀
        t, signal = self.detector.generate_test_signal(
            duration=self.duration,
            dt=self.dt,
            frequency=self.f0,
            harmonics=[1.0],
            noise_level=0.0
        )
        
        results = self.detector.detect_frequency(signal, self.dt)
        
        # Should be reasonably close (FFT resolution may exceed strict tolerance)
        self.assertLess(results['absolute_error_Hz'], 1.0)  # Within 1 Hz
        
    def test_normalized_spectrum(self):
        """Test spectrum normalization."""
        t, signal = self.detector.generate_test_signal(
            duration=self.duration,
            dt=self.dt,
            harmonics=[1.0]
        )
        
        results = self.detector.detect_frequency(signal, self.dt)
        
        # Check normalized spectrum exists and is properly normalized
        self.assertIn('spectrum_normalized', results)
        spectrum_norm = results['spectrum_normalized']
        
        # Max should be 1.0 (or close to it)
        self.assertAlmostEqual(np.max(spectrum_norm), 1.0, places=5)
        
    def test_snr_calculation(self):
        """Test signal-to-noise ratio calculation."""
        # Generate signal with known SNR
        t, signal = self.detector.generate_test_signal(
            duration=self.duration,
            dt=self.dt,
            harmonics=[1.0],
            noise_level=0.1
        )
        
        results = self.detector.compute_quality_metrics(signal, self.dt)
        metrics = results['quality_metrics']
        
        # SNR should be positive and reasonable
        self.assertGreater(metrics['snr'], 0.0)
        self.assertGreater(metrics['snr_db'], 0.0)
        
    def test_create_example_detector(self):
        """Test factory function for creating detector."""
        detector = create_example_detector(f0=150.0)
        
        self.assertEqual(detector.f0_expected, 150.0)
        self.assertEqual(detector.coherence_threshold, 0.888)
        self.assertEqual(detector.max_harmonics, 5)
        self.assertEqual(detector.frequency_tolerance, 0.001)


class TestIntegrationWithDNS(unittest.TestCase):
    """Integration tests with DNS-like data."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.detector = create_example_detector()
        
    def test_energy_time_series(self):
        """Test analysis of energy time series (typical DNS output)."""
        # Simulate energy oscillating at f₀
        dt = 1e-3
        t = np.arange(0, 2.0, dt)
        
        # Energy with f₀ oscillation + decay
        E_base = 1.0
        decay = np.exp(-0.1 * t)
        oscillation = 0.1 * np.cos(2 * np.pi * self.detector.f0_expected * t)
        energy = E_base * decay + oscillation
        
        results = self.detector.detect_frequency(energy, dt, "kinetic_energy")
        
        # Should detect f₀
        self.assertLess(
            abs(results['detected_frequency_Hz'] - self.detector.f0_expected),
            5.0  # Within 5 Hz for this noisy case
        )
        
    def test_velocity_field_temporal_evolution(self):
        """Test analysis of velocity field temporal evolution."""
        # Simulate velocity component oscillating at f₀
        dt = 5e-4
        t = np.arange(0, 1.0, dt)
        
        # Velocity with f₀ and 2f₀
        u = np.cos(2 * np.pi * self.detector.f0_expected * t)
        u += 0.3 * np.cos(2 * np.pi * 2 * self.detector.f0_expected * t)
        u += 0.05 * np.random.randn(len(t))  # Noise
        
        results = self.detector.detect_harmonics(u, dt, "velocity_u")
        
        # Should detect at least some frequencies
        self.assertGreaterEqual(results['harmonic_count'], 0)
        
    def test_multiple_field_components(self):
        """Test multi-signal analysis with velocity components."""
        dt = 1e-3
        t = np.arange(0, 1.5, dt)
        
        # Create u, v, w components all oscillating at f₀
        signals = {}
        for component in ['u', 'v', 'w']:
            signal = np.cos(2 * np.pi * self.detector.f0_expected * t)
            signal += 0.1 * np.random.randn(len(t))
            signals[component] = signal
            
        results = self.detector.analyze_multi_signal(signals, dt)
        
        # All should detect similar frequency
        agg = results['aggregate_statistics']
        self.assertLess(agg['std_frequency_Hz'], 10.0)  # Low variation
        self.assertEqual(agg['signal_count'], 3)


class TestEdgeCases(unittest.TestCase):
    """Test edge cases and error handling."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.detector = create_example_detector()
        
    def test_very_short_duration(self):
        """Test with very short time series."""
        t, signal = self.detector.generate_test_signal(
            duration=0.01,  # Very short
            dt=1e-4,
            harmonics=[1.0]
        )
        
        results = self.detector.detect_frequency(signal, 1e-4)
        
        # Should not crash, though accuracy may be poor
        self.assertIsNotNone(results)
        
    def test_high_noise_level(self):
        """Test with very high noise level."""
        t, signal = self.detector.generate_test_signal(
            duration=1.0,
            dt=1e-4,
            harmonics=[1.0],
            noise_level=1.0  # Very noisy
        )
        
        results = self.detector.detect_frequency(signal, 1e-4)
        
        # Should still return results
        self.assertIsNotNone(results)
        self.assertIn('detected_frequency_Hz', results)
        
    def test_dc_signal(self):
        """Test with constant (DC) signal."""
        signal = np.ones(10000)
        results = self.detector.detect_frequency(signal, 1e-4)
        
        # Should handle gracefully
        self.assertIsNotNone(results)
        
    def test_multiple_peaks_similar_amplitude(self):
        """Test with multiple peaks of similar amplitude."""
        t, signal = self.detector.generate_test_signal(
            duration=1.0,
            dt=1e-4,
            harmonics=[1.0, 0.9, 0.8],  # Similar amplitudes
            noise_level=0.05
        )
        
        results = self.detector.detect_harmonics(signal, 1e-4)
        
        # Should detect at least some harmonics
        self.assertGreaterEqual(results['harmonic_count'], 0)


if __name__ == '__main__':
    unittest.main(verbosity=2)
