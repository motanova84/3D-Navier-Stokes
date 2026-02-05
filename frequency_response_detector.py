#!/usr/bin/env python3
"""
Frequency Response Detector for Ψ-NSE Simulations
==================================================

Comprehensive frequency response detection and analysis module for detecting
the fundamental frequency f₀ = 141.7001 Hz and its harmonics in fluid dynamics
simulations using the Ψ-Navier-Stokes Equations.

Features:
- FFT-based spectral analysis
- Multi-signal frequency detection
- Harmonic analysis (f₀, 2f₀, 3f₀, ...)
- Coherence validation against QCAL threshold (0.888)
- Quality metrics and error bounds

Author: José Manuel Mota Burruezo (JMMB Ψ✧∞³)
License: MIT
"""

import numpy as np
from scipy.fft import fft, fftfreq
from scipy.signal import find_peaks, welch
from typing import Dict, List, Optional, Tuple, Union
import warnings


class FrequencyResponseDetector:
    """
    Advanced frequency response detector for Ψ-NSE simulations.
    
    Detects and analyzes frequency responses in time-series data from
    fluid dynamics simulations, with focus on detecting the fundamental
    frequency f₀ = 141.7001 Hz derived from Riemann zeta zeros.
    """
    
    def __init__(self, 
                 f0_expected: float = 141.7001,
                 coherence_threshold: float = 0.888,
                 max_harmonics: int = 5,
                 frequency_tolerance: float = 0.001):
        """
        Initialize the frequency response detector.
        
        Args:
            f0_expected: Expected fundamental frequency (Hz)
            coherence_threshold: QCAL coherence threshold
            max_harmonics: Maximum number of harmonics to detect
            frequency_tolerance: Tolerance for frequency detection (Hz)
        """
        self.f0_expected = f0_expected
        self.coherence_threshold = coherence_threshold
        self.max_harmonics = max_harmonics
        self.frequency_tolerance = frequency_tolerance
        
    def detect_frequency(self,
                        time_series: np.ndarray,
                        dt: float,
                        signal_name: str = "signal") -> Dict:
        """
        Detect dominant frequency in a time series using FFT.
        
        Args:
            time_series: Input time series data
            dt: Time step between samples
            signal_name: Name of the signal for reporting
            
        Returns:
            Dictionary containing detection results
        """
        # Ensure time series is 1D
        if time_series.ndim > 1:
            time_series = time_series.flatten()
            
        N = len(time_series)
        
        # Apply FFT
        fft_vals = fft(time_series)
        freqs = fftfreq(N, dt)
        
        # Take only positive frequencies
        positive_mask = freqs > 0
        freqs_pos = freqs[positive_mask]
        fft_mag = np.abs(fft_vals[positive_mask])
        
        # Normalize spectrum
        fft_mag_norm = fft_mag / np.max(fft_mag) if np.max(fft_mag) > 0 else fft_mag
        
        # Find dominant frequency
        if len(fft_mag) > 0:
            idx_peak = np.argmax(fft_mag)
            f_detected = freqs_pos[idx_peak]
            amplitude = fft_mag[idx_peak]
            normalized_amplitude = fft_mag_norm[idx_peak]
        else:
            f_detected = 0.0
            amplitude = 0.0
            normalized_amplitude = 0.0
            
        # Calculate error metrics
        abs_error = abs(f_detected - self.f0_expected)
        rel_error = abs_error / self.f0_expected if self.f0_expected > 0 else np.inf
        
        # Quality assessment
        within_tolerance = abs_error <= self.frequency_tolerance
        
        results = {
            'signal_name': signal_name,
            'detected_frequency_Hz': float(f_detected),
            'expected_frequency_Hz': float(self.f0_expected),
            'absolute_error_Hz': float(abs_error),
            'relative_error': float(rel_error),
            'peak_amplitude': float(amplitude),
            'normalized_amplitude': float(normalized_amplitude),
            'within_tolerance': bool(within_tolerance),
            'frequencies': freqs_pos,
            'spectrum': fft_mag,
            'spectrum_normalized': fft_mag_norm
        }
        
        return results
    
    def detect_harmonics(self,
                        time_series: np.ndarray,
                        dt: float,
                        signal_name: str = "signal") -> Dict:
        """
        Detect fundamental frequency and its harmonics.
        
        Args:
            time_series: Input time series data
            dt: Time step between samples
            signal_name: Name of the signal for reporting
            
        Returns:
            Dictionary containing harmonic analysis results
        """
        # Get base frequency detection
        base_results = self.detect_frequency(time_series, dt, signal_name)
        
        # Extract spectrum
        freqs = base_results['frequencies']
        spectrum = base_results['spectrum']
        
        # Find peaks in spectrum
        peaks, properties = find_peaks(spectrum, height=0.1*np.max(spectrum))
        
        if len(peaks) == 0:
            return {
                **base_results,
                'harmonics_detected': [],
                'harmonic_count': 0,
                'fundamental_confirmed': False
            }
        
        peak_freqs = freqs[peaks]
        peak_amps = spectrum[peaks]
        
        # Sort peaks by amplitude
        sorted_indices = np.argsort(peak_amps)[::-1]
        peak_freqs_sorted = peak_freqs[sorted_indices]
        peak_amps_sorted = peak_amps[sorted_indices]
        
        # Try to identify harmonics
        harmonics = []
        fundamental = peak_freqs_sorted[0]  # Assume strongest peak is fundamental
        
        # Check for harmonics of f0_expected
        # Use adaptive tolerance based on harmonic number and FFT resolution
        freq_resolution = 1.0 / (len(time_series) * dt)
        for n in range(1, self.max_harmonics + 1):
            expected_harmonic = n * self.f0_expected
            # Adaptive tolerance: either specified tolerance or FFT resolution, whichever is larger
            adaptive_tolerance = max(self.frequency_tolerance * n, freq_resolution * 2)
            
            # Look for peaks near expected harmonic
            for i, f in enumerate(peak_freqs_sorted):
                if abs(f - expected_harmonic) <= adaptive_tolerance:
                    harmonics.append({
                        'harmonic_number': n,
                        'frequency_Hz': float(f),
                        'expected_frequency_Hz': float(expected_harmonic),
                        'amplitude': float(peak_amps_sorted[i]),
                        'error_Hz': float(abs(f - expected_harmonic))
                    })
                    break
        
        # Check if fundamental is confirmed by harmonics
        fundamental_confirmed = len(harmonics) >= 2 and harmonics[0]['harmonic_number'] == 1
        
        return {
            **base_results,
            'harmonics_detected': harmonics,
            'harmonic_count': len(harmonics),
            'fundamental_confirmed': fundamental_confirmed,
            'fundamental_frequency_Hz': float(fundamental)
        }
    
    def analyze_multi_signal(self,
                            signals: Dict[str, np.ndarray],
                            dt: float,
                            detect_harmonics: bool = False) -> Dict:
        """
        Analyze frequency responses from multiple signals.
        
        Args:
            signals: Dictionary of signal_name -> time_series
            dt: Time step between samples
            detect_harmonics: Whether to perform harmonic analysis
            
        Returns:
            Dictionary containing multi-signal analysis results
        """
        results = {}
        
        for name, signal in signals.items():
            if detect_harmonics:
                results[name] = self.detect_harmonics(signal, dt, name)
            else:
                results[name] = self.detect_frequency(signal, dt, name)
                
        # Aggregate statistics
        detected_freqs = [r['detected_frequency_Hz'] for r in results.values()]
        errors = [r['relative_error'] for r in results.values()]
        
        aggregate = {
            'mean_frequency_Hz': float(np.mean(detected_freqs)),
            'std_frequency_Hz': float(np.std(detected_freqs)),
            'mean_relative_error': float(np.mean(errors)),
            'max_relative_error': float(np.max(errors)),
            'all_within_tolerance': all(r['within_tolerance'] for r in results.values()),
            'signal_count': len(signals)
        }
        
        return {
            'individual_results': results,
            'aggregate_statistics': aggregate
        }
    
    def validate_coherence(self,
                          time_series: np.ndarray,
                          dt: float) -> Dict:
        """
        Validate QCAL coherence in the frequency response.
        
        Coherence is measured as the ratio of energy at f₀ to total energy.
        Should exceed coherence_threshold (0.888) for QCAL systems.
        
        Args:
            time_series: Input time series data
            dt: Time step between samples
            
        Returns:
            Dictionary containing coherence validation results
        """
        # Get frequency detection
        freq_results = self.detect_frequency(time_series, dt)
        
        freqs = freq_results['frequencies']
        spectrum = freq_results['spectrum']
        f_detected = freq_results['detected_frequency_Hz']
        
        # Calculate total spectral energy
        total_energy = np.sum(spectrum**2)
        
        # Find energy near f₀
        tolerance_band = self.frequency_tolerance * 5  # Wider band for coherence
        near_f0 = np.abs(freqs - self.f0_expected) <= tolerance_band
        f0_energy = np.sum(spectrum[near_f0]**2)
        
        # Calculate coherence
        coherence = f0_energy / total_energy if total_energy > 0 else 0.0
        
        # Validation
        is_coherent = coherence >= self.coherence_threshold
        
        results = {
            'coherence': float(coherence),
            'coherence_threshold': float(self.coherence_threshold),
            'is_coherent': bool(is_coherent),
            'total_energy': float(total_energy),
            'f0_energy': float(f0_energy),
            'energy_concentration': float(f0_energy / total_energy) if total_energy > 0 else 0.0,
            **freq_results
        }
        
        return results
    
    def compute_quality_metrics(self,
                                time_series: np.ndarray,
                                dt: float) -> Dict:
        """
        Compute comprehensive quality metrics for frequency detection.
        
        Args:
            time_series: Input time series data
            dt: Time step between samples
            
        Returns:
            Dictionary containing quality metrics
        """
        # Get base detection
        freq_results = self.detect_frequency(time_series, dt)
        
        # Get harmonic analysis
        harmonic_results = self.detect_harmonics(time_series, dt)
        
        # Get coherence validation
        coherence_results = self.validate_coherence(time_series, dt)
        
        # Compute signal-to-noise ratio
        spectrum = freq_results['spectrum']
        peak_amplitude = freq_results['peak_amplitude']
        noise_floor = np.median(spectrum)
        snr = peak_amplitude / noise_floor if noise_floor > 0 else np.inf
        snr_db = 10 * np.log10(snr) if snr > 0 else -np.inf
        
        # Overall quality score (0-1)
        quality_components = [
            1.0 - min(freq_results['relative_error'], 1.0),  # Frequency accuracy
            coherence_results['coherence'],  # Coherence
            min(snr / 100.0, 1.0),  # SNR contribution
            1.0 if harmonic_results['fundamental_confirmed'] else 0.5  # Harmonic confirmation
        ]
        overall_quality = np.mean(quality_components)
        
        metrics = {
            'frequency_accuracy': float(1.0 - freq_results['relative_error']),
            'coherence': float(coherence_results['coherence']),
            'snr': float(snr),
            'snr_db': float(snr_db),
            'noise_floor': float(noise_floor),
            'harmonic_confirmation': bool(harmonic_results['fundamental_confirmed']),
            'overall_quality': float(overall_quality),
            'grade': self._quality_grade(overall_quality)
        }
        
        return {
            'quality_metrics': metrics,
            'frequency_detection': freq_results,
            'harmonic_analysis': harmonic_results,
            'coherence_validation': coherence_results
        }
    
    def _quality_grade(self, quality_score: float) -> str:
        """Assign letter grade to quality score."""
        if quality_score >= 0.95:
            return 'A+'
        elif quality_score >= 0.90:
            return 'A'
        elif quality_score >= 0.85:
            return 'B+'
        elif quality_score >= 0.80:
            return 'B'
        elif quality_score >= 0.75:
            return 'C+'
        elif quality_score >= 0.70:
            return 'C'
        else:
            return 'F'
    
    def generate_test_signal(self,
                            duration: float = 1.0,
                            dt: float = 1e-4,
                            frequency: Optional[float] = None,
                            harmonics: List[float] = None,
                            noise_level: float = 0.01) -> Tuple[np.ndarray, np.ndarray]:
        """
        Generate synthetic test signal with known frequency.
        
        Args:
            duration: Signal duration (seconds)
            dt: Time step (seconds)
            frequency: Fundamental frequency (defaults to f0_expected)
            harmonics: List of harmonic amplitudes [A1, A2, A3, ...]
            noise_level: Amplitude of additive Gaussian noise
            
        Returns:
            Tuple of (time_array, signal_array)
        """
        if frequency is None:
            frequency = self.f0_expected
            
        if harmonics is None:
            harmonics = [1.0]  # Only fundamental
            
        # Time array
        t = np.arange(0, duration, dt)
        
        # Generate signal with harmonics
        signal = np.zeros_like(t)
        for n, amplitude in enumerate(harmonics, start=1):
            signal += amplitude * np.cos(2 * np.pi * n * frequency * t)
            
        # Add noise
        if noise_level > 0:
            signal += noise_level * np.random.randn(len(t))
            
        return t, signal


def create_example_detector(f0: float = 141.7001) -> FrequencyResponseDetector:
    """
    Create a frequency detector with standard QCAL parameters.
    
    Args:
        f0: Fundamental frequency (Hz)
        
    Returns:
        Configured FrequencyResponseDetector instance
    """
    return FrequencyResponseDetector(
        f0_expected=f0,
        coherence_threshold=0.888,
        max_harmonics=5,
        frequency_tolerance=0.001
    )


if __name__ == "__main__":
    # Quick demonstration
    print("="*70)
    print("Frequency Response Detector - Quick Test")
    print("="*70)
    
    # Create detector
    detector = create_example_detector()
    
    # Generate test signal with f₀ and harmonics
    t, signal = detector.generate_test_signal(
        duration=1.0,
        dt=1e-4,
        harmonics=[1.0, 0.5, 0.25],  # f₀, 2f₀, 3f₀
        noise_level=0.05
    )
    
    # Perform comprehensive analysis
    print("\n🔍 Performing comprehensive frequency analysis...")
    results = detector.compute_quality_metrics(signal, dt=1e-4)
    
    # Display results
    print("\n📊 Results:")
    print(f"  Detected frequency: {results['frequency_detection']['detected_frequency_Hz']:.4f} Hz")
    print(f"  Expected frequency: {results['frequency_detection']['expected_frequency_Hz']:.4f} Hz")
    print(f"  Absolute error: {results['frequency_detection']['absolute_error_Hz']:.6f} Hz")
    print(f"  Relative error: {results['frequency_detection']['relative_error']:.6f}")
    print(f"  Within tolerance: {results['frequency_detection']['within_tolerance']}")
    
    print("\n🎵 Harmonic Analysis:")
    print(f"  Harmonics detected: {results['harmonic_analysis']['harmonic_count']}")
    print(f"  Fundamental confirmed: {results['harmonic_analysis']['fundamental_confirmed']}")
    
    print("\n✨ Coherence Validation:")
    print(f"  Coherence: {results['coherence_validation']['coherence']:.4f}")
    print(f"  Threshold: {results['coherence_validation']['coherence_threshold']:.4f}")
    print(f"  Is coherent: {results['coherence_validation']['is_coherent']}")
    
    print("\n⭐ Quality Metrics:")
    metrics = results['quality_metrics']
    print(f"  Frequency accuracy: {metrics['frequency_accuracy']:.4f}")
    print(f"  SNR: {metrics['snr_db']:.2f} dB")
    print(f"  Overall quality: {metrics['overall_quality']:.4f}")
    print(f"  Grade: {metrics['grade']}")
    
    print("\n✅ Test completed successfully!")
    print("="*70)
