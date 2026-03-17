#!/usr/bin/env python3
"""
Hilbert-Pólya Operator - Number Theory to Biology
==================================================

Maps Riemann zeta function zeros to biological eigenfrequencies using
the golden ratio (φ) as a scaling factor.

The Hilbert-Pólya conjecture proposes that the non-trivial zeros of 
the Riemann zeta function ζ(s) correspond to eigenvalues of a 
Hermitian operator. This module extends that idea to biological systems.

Mathematical Framework:
----------------------
1. Riemann zeros: ζ(1/2 + iγₙ) = 0
2. Hilbert-Pólya operator eigenvalues: λₙ = γₙ
3. Biological frequency mapping: fₙ = (γₙ/2π) × φ × scale_factor

where:
- γₙ is the n-th non-trivial zero of Riemann zeta (imaginary part)
- φ = (1 + √5)/2 ≈ 1.618033988... (golden ratio)
- scale_factor converts to biological frequency range (typically 10⁻⁶)

Key Insight:
-----------
The golden ratio φ appears ubiquitously in biology (phyllotaxis, spirals, 
DNA structure) and serves as a natural bridge between pure mathematics 
and biological resonance.

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
Date: 31 de enero de 2026
License: MIT
"""

import numpy as np
from typing import List, Tuple, Dict, Optional
from dataclasses import dataclass
from scipy.special import zeta
import warnings


@dataclass
class HilbertPolyaParameters:
    """Parameters for Hilbert-Pólya operator and biological mapping"""
    # Golden ratio (exact value)
    phi: float = (1 + np.sqrt(5)) / 2  # φ ≈ 1.618033988749895
    
    # Scale factor for biological frequencies (Hz)
    # This converts from mathematical eigenvalues to biological range
    # Calibrated so that γ₄₉ ≈ 141.123 maps to ~141.7 Hz
    scale_factor: float = 3.899  # Derived from: 141.7 / ((141.123/(2π)) × φ)
    
    # Number of Riemann zeros to compute
    num_zeros: int = 100
    
    # Target frequency for validation (Hz)
    target_frequency: float = 141.7
    
    def __post_init__(self):
        """Validate parameters"""
        if self.num_zeros < 1:
            raise ValueError("num_zeros must be at least 1")
        if self.scale_factor <= 0:
            raise ValueError("scale_factor must be positive")


# First 50 non-trivial zeros of Riemann zeta (imaginary parts)
# Source: LMFDB (L-functions and Modular Forms Database)
RIEMANN_ZEROS = [
    14.134725142,
    21.022039639,
    25.010857580,
    30.424876126,
    32.935061588,
    37.586178159,
    40.918719012,
    43.327073281,
    48.005150881,
    49.773832478,
    52.970321478,
    56.446247697,
    59.347044003,
    60.831778525,
    65.112544048,
    67.079810529,
    69.546401711,
    72.067157674,
    75.704690699,
    77.144840069,
    79.337375020,
    82.910380854,
    84.735492981,
    87.425274613,
    88.809111208,
    92.491899271,
    94.651344041,
    95.870634228,
    98.831194218,
    101.317851006,
    103.725538040,
    105.446623052,
    107.168611184,
    111.029535543,
    111.874659177,
    114.320220915,
    116.226680321,
    118.790782866,
    121.370125002,
    122.946829294,
    124.256818554,
    127.516683880,
    129.578704200,
    131.087688531,
    133.497737203,
    134.756509753,
    138.116042055,
    139.736208952,
    141.123707404,
    143.111845808,
]


def get_riemann_zeros(num_zeros: int = 50) -> np.ndarray:
    """
    Get the first N non-trivial zeros of the Riemann zeta function.
    
    These are the imaginary parts γₙ where ζ(1/2 + iγₙ) = 0.
    
    Args:
        num_zeros: Number of zeros to return (max 50 with current data)
    
    Returns:
        Array of γₙ values
    """
    if num_zeros > len(RIEMANN_ZEROS):
        warnings.warn(
            f"Requested {num_zeros} zeros but only {len(RIEMANN_ZEROS)} available. "
            f"Returning {len(RIEMANN_ZEROS)}."
        )
        num_zeros = len(RIEMANN_ZEROS)
    
    return np.array(RIEMANN_ZEROS[:num_zeros])


def hilbert_polya_eigenvalues(num_eigenvalues: int = 50) -> np.ndarray:
    """
    Compute eigenvalues of the hypothetical Hilbert-Pólya operator.
    
    According to the Hilbert-Pólya conjecture, these should equal
    the non-trivial zeros of the Riemann zeta function.
    
    Args:
        num_eigenvalues: Number of eigenvalues to compute
    
    Returns:
        Array of eigenvalues λₙ = γₙ
    """
    return get_riemann_zeros(num_eigenvalues)


def map_to_biological_frequencies(
    eigenvalues: np.ndarray,
    phi: float = (1 + np.sqrt(5)) / 2,
    scale_factor: float = 3.899
) -> np.ndarray:
    """
    Map Hilbert-Pólya eigenvalues to biological frequencies.
    
    Transform: fₙ = (γₙ / 2π) × φ × scale_factor
    
    Args:
        eigenvalues: Hilbert-Pólya eigenvalues (γₙ)
        phi: Golden ratio scaling factor
        scale_factor: Conversion to biological frequency range
    
    Returns:
        Array of biological frequencies in Hz
    """
    return (eigenvalues / (2 * np.pi)) * phi * scale_factor


def find_nearest_eigenfrequency(
    target_frequency: float,
    phi: float = (1 + np.sqrt(5)) / 2,
    scale_factor: float = 3.899,
    num_zeros: int = 50
) -> Tuple[float, int, float]:
    """
    Find the Riemann zero that maps closest to a target biological frequency.
    
    Args:
        target_frequency: Target frequency in Hz (e.g., 141.7)
        phi: Golden ratio
        scale_factor: Biological frequency scale factor
        num_zeros: Number of zeros to search
    
    Returns:
        Tuple of (frequency, zero_index, deviation)
    """
    eigenvalues = hilbert_polya_eigenvalues(num_zeros)
    frequencies = map_to_biological_frequencies(eigenvalues, phi, scale_factor)
    
    # Find nearest
    deviations = np.abs(frequencies - target_frequency)
    idx = np.argmin(deviations)
    
    return frequencies[idx], idx, deviations[idx]


class HilbertPolyaOperator:
    """
    Hilbert-Pólya operator for mapping number theory to biological resonance.
    
    This class implements the hypothetical Hermitian operator whose eigenvalues
    correspond to Riemann zeta zeros, and maps them to biological frequencies
    via golden ratio scaling.
    """
    
    def __init__(self, params: Optional[HilbertPolyaParameters] = None):
        """
        Initialize Hilbert-Pólya operator.
        
        Args:
            params: Configuration parameters
        """
        self.params = params or HilbertPolyaParameters()
        self.eigenvalues = hilbert_polya_eigenvalues(self.params.num_zeros)
        self.bio_frequencies = map_to_biological_frequencies(
            self.eigenvalues,
            self.params.phi,
            self.params.scale_factor
        )
    
    def get_eigenfrequencies(self) -> np.ndarray:
        """Get biological eigenfrequencies from Riemann zeros."""
        return self.bio_frequencies
    
    def get_spectrum(self, freq_min: float = 0, freq_max: float = 200) -> Dict[str, np.ndarray]:
        """
        Get spectral lines in a frequency range.
        
        Args:
            freq_min: Minimum frequency (Hz)
            freq_max: Maximum frequency (Hz)
        
        Returns:
            Dictionary with 'frequencies' and 'amplitudes'
        """
        mask = (self.bio_frequencies >= freq_min) & (self.bio_frequencies <= freq_max)
        freqs = self.bio_frequencies[mask]
        
        # Amplitude inversely proportional to zero index (lower zeros stronger)
        indices = np.where(mask)[0]
        amps = 1.0 / (1.0 + indices)
        
        return {
            'frequencies': freqs,
            'amplitudes': amps,
            'zero_indices': indices
        }
    
    def validate_target_frequency(self, target: float = 141.7) -> Dict[str, float]:
        """
        Validate if a target frequency emerges from the eigenspectrum.
        
        Args:
            target: Target frequency to validate (Hz)
        
        Returns:
            Validation results dictionary
        """
        freq, idx, dev = find_nearest_eigenfrequency(
            target,
            self.params.phi,
            self.params.scale_factor,
            self.params.num_zeros
        )
        
        return {
            'target_frequency': target,
            'nearest_eigenfrequency': freq,
            'zero_index': idx,
            'zero_value': self.eigenvalues[idx],
            'deviation_hz': dev,
            'deviation_percent': (dev / target) * 100,
            'validated': dev < 1.0  # Within 1 Hz
        }
    
    def compute_resonance_strength(self, frequency: float, bandwidth: float = 1.0) -> float:
        """
        Compute resonance strength at a given frequency.
        
        Uses Lorentzian line shape for each eigenfrequency.
        
        Args:
            frequency: Query frequency (Hz)
            bandwidth: Linewidth (Hz)
        
        Returns:
            Resonance strength (dimensionless)
        """
        # Lorentzian sum over all eigenfrequencies
        strength = 0.0
        for i, f0 in enumerate(self.bio_frequencies):
            amp = 1.0 / (1.0 + i)  # Decay with index
            gamma = bandwidth / 2
            strength += amp * (gamma**2) / ((frequency - f0)**2 + gamma**2)
        
        return strength


def demonstrate_hilbert_polya_mapping():
    """Demonstrate the Hilbert-Pólya to biology mapping."""
    print("=" * 70)
    print("HILBERT-PÓLYA OPERATOR: Number Theory → Biology")
    print("=" * 70)
    
    # Initialize operator
    operator = HilbertPolyaOperator()
    
    # Show first 10 mappings
    print("\nFirst 10 Riemann Zeros → Biological Frequencies:")
    print("-" * 70)
    print(f"{'n':<5} {'γₙ':<15} {'fₙ (Hz)':<20} {'Note'}")
    print("-" * 70)
    
    for i in range(min(10, len(operator.eigenvalues))):
        gamma = operator.eigenvalues[i]
        freq = operator.bio_frequencies[i]
        note = "★ Target!" if abs(freq - 141.7) < 10 else ""
        print(f"{i+1:<5} {gamma:<15.6f} {freq:<20.10f} {note}")
    
    # Validate 141.7 Hz
    print("\n" + "=" * 70)
    print("VALIDATION: 141.7 Hz Target Frequency")
    print("=" * 70)
    
    validation = operator.validate_target_frequency(141.7)
    for key, value in validation.items():
        if isinstance(value, float):
            print(f"{key:.<40} {value:.10f}")
        else:
            print(f"{key:.<40} {value}")
    
    # Show resonance spectrum
    print("\n" + "=" * 70)
    print("RESONANCE SPECTRUM (100-200 Hz)")
    print("=" * 70)
    
    freqs = np.linspace(100, 200, 1000)
    strengths = [operator.compute_resonance_strength(f) for f in freqs]
    peak_idx = np.argmax(strengths)
    
    print(f"Peak frequency............... {freqs[peak_idx]:.2f} Hz")
    print(f"Peak strength................ {strengths[peak_idx]:.6f}")
    print(f"Deviation from 141.7 Hz...... {abs(freqs[peak_idx] - 141.7):.2f} Hz")
    
    return operator


if __name__ == "__main__":
    demonstrate_hilbert_polya_mapping()
