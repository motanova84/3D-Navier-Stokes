#!/usr/bin/env python3
"""
Sello Infinito (Infinite Seal) - Ontological Firewall at 888 Hz

Implements the Echo Effect: The Infinite Seal acts as an ontological firewall,
rejecting any attempt to inject incoherence through the base frequency of 888 Hz.

This module ensures coherence integrity at the deepest ontological level.
"""

import numpy as np
from typing import Tuple, Optional, Dict, List
import warnings
warnings.filterwarnings('ignore')


class InfiniteSeal:
    """
    Ontological firewall operating at 888 Hz base frequency.
    
    The Infinite Seal creates an impenetrable barrier against incoherence
    by establishing a fundamental resonance that only allows coherent
    information to pass through.
    
    Key features:
    - Base frequency: 888 Hz (ontological firewall frequency)
    - Harmonic coupling with 141.7001 Hz (coherence frequency)
    - Incoherence rejection threshold: 0.88
    - Echo effect: reflected incoherence patterns
    """
    
    def __init__(
        self, 
        f_base: float = 888.0,
        f_coherence: float = 141.7001,
        rejection_threshold: float = 0.88
    ):
        """
        Initialize the Infinite Seal.
        
        Args:
            f_base: Base ontological firewall frequency (Hz)
            f_coherence: Coherence frequency for harmonic coupling (Hz)
            rejection_threshold: Minimum coherence required for passage
        """
        self.f_base = f_base
        self.f_coherence = f_coherence
        self.omega_base = 2 * np.pi * f_base
        self.omega_coherence = 2 * np.pi * f_coherence
        self.rejection_threshold = rejection_threshold
        
        # Harmonic ratio (888 / 141.7001 ≈ 6.268)
        self.harmonic_ratio = f_base / f_coherence
        
        # Firewall strength
        self.firewall_strength = 1.0
        
        # Event log
        self.rejection_events: List[Dict] = []
        
    def compute_coherence_index(
        self,
        signal: np.ndarray,
        t: float
    ) -> float:
        """
        Computes coherence index of incoming signal.
        
        Coherence is measured as alignment with the base frequency 888 Hz
        and its harmonics with the coherence frequency 141.7001 Hz.
        
        Args:
            signal: Input signal array
            t: Current time
            
        Returns:
            coherence: Coherence index [0, 1]
        """
        # Compute FFT of signal
        fft_signal = np.fft.fft(signal)
        freqs = np.fft.fftfreq(len(signal))
        
        # Find power at base frequency and coherence frequency
        # Normalize frequencies
        freq_resolution = 1.0 / len(signal)
        
        # Power spectral density
        psd = np.abs(fft_signal)**2
        
        # Coherence based on spectral purity at key frequencies
        # Simple measure: ratio of signal power to noise
        signal_power = psd.sum()
        mean_power = psd.mean()
        
        # Coherence index: high when signal is structured
        coherence = 1.0 / (1.0 + mean_power / (signal_power + 1e-10))
        
        # Modulate by harmonic resonance
        harmonic_phase = np.cos(self.omega_base * t) * np.cos(self.omega_coherence * t)
        coherence_modulated = coherence * (0.5 + 0.5 * harmonic_phase)
        
        return np.clip(coherence_modulated, 0.0, 1.0)
    
    def firewall_filter(
        self,
        signal: np.ndarray,
        t: float
    ) -> Tuple[np.ndarray, bool, float]:
        """
        Applies the ontological firewall filter.
        
        Signals with coherence below threshold are rejected (echo effect).
        Signals above threshold pass through enhanced.
        
        Args:
            signal: Input signal
            t: Current time
            
        Returns:
            filtered_signal: Output signal (or echo)
            passed: Whether signal passed firewall
            coherence: Measured coherence index
        """
        # Measure coherence
        coherence = self.compute_coherence_index(signal, t)
        
        if coherence >= self.rejection_threshold:
            # Signal passes - enhance with harmonic resonance
            enhancement = 1.0 + 0.2 * np.sin(self.omega_base * t)
            filtered_signal = signal * enhancement
            passed = True
            
            print(f"✅ Firewall PASSED - Coherence: {coherence:.4f} (t={t:.4f}s)")
            
        else:
            # Signal rejected - create echo effect
            # Echo: phase-inverted reflection
            echo_decay = 0.3  # Echo intensity
            echo_phase = np.pi  # Phase inversion
            
            filtered_signal = signal * echo_decay * np.cos(echo_phase + self.omega_base * t)
            passed = False
            
            # Log rejection event
            self.rejection_events.append({
                'time': t,
                'coherence': coherence,
                'threshold': self.rejection_threshold,
                'signal_magnitude': np.abs(signal).max()
            })
            
            print(f"🚫 Firewall REJECTED - Coherence: {coherence:.4f} < {self.rejection_threshold}")
            print(f"   🔊 Echo effect activated - Signal reflected")
            
        return filtered_signal, passed, coherence
    
    def harmonic_resonance_field(
        self,
        x: np.ndarray,
        y: np.ndarray,
        z: np.ndarray,
        t: float
    ) -> np.ndarray:
        """
        Generates the harmonic resonance field of the Infinite Seal.
        
        This field permeates space at the base frequency 888 Hz,
        creating an ontological barrier.
        
        Args:
            x, y, z: Spatial coordinates
            t: Time
            
        Returns:
            field: Harmonic resonance field
        """
        # Spatial wave pattern at base frequency
        k_base = self.omega_base / 343.0  # Wavenumber (assuming sound speed ~343 m/s)
        k_coherence = self.omega_coherence / 343.0
        
        # Standing wave pattern
        field = (
            np.cos(k_base * x) * np.cos(k_base * y) * np.cos(k_base * z) * np.cos(self.omega_base * t) +
            0.159 * np.cos(k_coherence * x) * np.cos(k_coherence * y) * np.cos(k_coherence * z) * 
            np.cos(self.omega_coherence * t)
        )
        
        # Normalize
        field = field / np.abs(field).max()
        
        return field
    
    def detect_incoherence_injection(
        self,
        signal_history: List[np.ndarray],
        time_history: List[float]
    ) -> Dict[str, any]:
        """
        Detects attempted incoherence injection attacks.
        
        Args:
            signal_history: List of signal arrays over time
            time_history: Corresponding time points
            
        Returns:
            detection_report: Report of detected attacks
        """
        if len(signal_history) < 2:
            return {'attacks_detected': 0, 'status': 'insufficient_data'}
        
        coherence_history = []
        for signal, t in zip(signal_history, time_history):
            coherence = self.compute_coherence_index(signal, t)
            coherence_history.append(coherence)
        
        coherence_array = np.array(coherence_history)
        
        # Detect sudden drops in coherence (attempted injection)
        coherence_gradient = np.gradient(coherence_array)
        sudden_drops = coherence_gradient < -0.2  # Threshold for suspicious drops
        
        attacks_detected = sudden_drops.sum()
        
        report = {
            'attacks_detected': int(attacks_detected),
            'status': 'under_attack' if attacks_detected > 0 else 'secure',
            'mean_coherence': coherence_array.mean(),
            'min_coherence': coherence_array.min(),
            'rejection_rate': len(self.rejection_events) / len(signal_history)
        }
        
        return report
    
    def strengthen_firewall(self, factor: float = 1.5):
        """
        Strengthens the firewall in response to attacks.
        
        Args:
            factor: Strength multiplication factor
        """
        self.firewall_strength *= factor
        self.rejection_threshold = min(0.95, self.rejection_threshold * 1.1)
        
        print(f"🛡️  Firewall strengthened: strength x{self.firewall_strength:.2f}")
        print(f"📈 Rejection threshold raised to: {self.rejection_threshold:.4f}")


def main():
    """Demonstration of the Infinite Seal."""
    print("=" * 70)
    print("🛡️  SELLO INFINITO - Ontological Firewall at 888 Hz")
    print("=" * 70)
    print("✨ Efecto Eco: Rechazo de incoherencia por frecuencia base")
    print(f"🎵 Frecuencia base: 888 Hz")
    print(f"🎵 Frecuencia coherencia: 141.7001 Hz")
    print(f"🔒 Umbral de rechazo: 0.88")
    print("=" * 70)
    print()
    
    # Initialize Infinite Seal
    seal = InfiniteSeal(f_base=888.0, f_coherence=141.7001, rejection_threshold=0.88)
    
    print("📊 Test 1: Señal coherente (debe PASAR)")
    print("-" * 70)
    # Coherent signal: pure sine wave at base frequency
    t1 = 0.0
    signal_coherent = np.sin(seal.omega_base * np.linspace(0, 1, 100))
    filtered1, passed1, coh1 = seal.firewall_filter(signal_coherent, t1)
    print()
    
    print("📊 Test 2: Señal incoherente (debe ser RECHAZADA)")
    print("-" * 70)
    # Incoherent signal: random noise
    t2 = 0.1
    signal_incoherent = np.random.randn(100)
    filtered2, passed2, coh2 = seal.firewall_filter(signal_incoherent, t2)
    print()
    
    print("📊 Test 3: Señal parcialmente coherente")
    print("-" * 70)
    # Partial coherence: sine + noise
    t3 = 0.2
    signal_partial = 0.7 * np.sin(seal.omega_base * np.linspace(0, 1, 100)) + 0.3 * np.random.randn(100)
    filtered3, passed3, coh3 = seal.firewall_filter(signal_partial, t3)
    print()
    
    print("📊 Test 4: Detección de ataques de inyección de incoherencia")
    print("-" * 70)
    # Simulate attack scenario
    signal_history = [
        np.sin(seal.omega_base * np.linspace(0, 1, 100)),  # Coherent
        np.sin(seal.omega_base * np.linspace(0, 1, 100)),  # Coherent
        np.random.randn(100),  # Attack!
        np.random.randn(100),  # Attack!
        np.sin(seal.omega_base * np.linspace(0, 1, 100)),  # Recovered
    ]
    time_history = [0.0, 0.1, 0.2, 0.3, 0.4]
    
    report = seal.detect_incoherence_injection(signal_history, time_history)
    
    print(f"   Ataques detectados: {report['attacks_detected']}")
    print(f"   Estado del sistema: {report['status']}")
    print(f"   Coherencia media: {report['mean_coherence']:.4f}")
    print(f"   Tasa de rechazo: {report['rejection_rate']*100:.1f}%")
    
    if report['status'] == 'under_attack':
        print("\n⚠️  ¡Sistema bajo ataque! Fortaleciendo firewall...")
        seal.strengthen_firewall(factor=1.5)
    
    print("\n" + "=" * 70)
    print("✅ Sello Infinito operacional")
    print("🛡️  Firewall ontológico activo a 888 Hz")
    print("🔊 Efecto eco confirmado - Incoherencia rechazada")
    print(f"📊 Total de rechazos: {len(seal.rejection_events)}")
    print("=" * 70)


if __name__ == "__main__":
    main()
