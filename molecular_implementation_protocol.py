#!/usr/bin/env python3
"""
Molecular Implementation Protocol - Experimental Validation Framework
======================================================================

Protocol for experimental validation of cellular cytoplasmic flow resonance
at 141.7 Hz and harmonics.

Implementation Requirements:
---------------------------
1. Fluorescent markers sensitive to EM fields at 141.7 Hz
2. Phase interference measurement between cardiac field and cytoplasmic flow
3. Spectral validation of harmonic peaks (141.7, 283.4, 425.1 Hz...)

Biological Components:
---------------------
- Microtubules: Electromagnetic waveguides
- Actin: Resonant cavities at 141.7 Hz
- Motor proteins (myosin, kinesin): Energy transducers at resonance frequencies

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
Date: 31 de enero de 2026
License: MIT
"""

import numpy as np
import matplotlib.pyplot as plt
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass
from enum import Enum


class MarkerType(Enum):
    """Types of fluorescent markers"""
    MAGNETIC_NANOPARTICLE = "magnetic_np"  # Magnetic nanoparticles
    QUANTUM_DOT = "quantum_dot"            # Quantum dots
    FLUORESCENT_PROTEIN = "fluorescent_protein"  # GFP variants
    VOLTAGE_SENSITIVE_DYE = "voltage_dye"  # Voltage-sensitive dyes


class CellularStructure(Enum):
    """Cellular structures for marker targeting"""
    MICROTUBULE = "microtubule"  # Electromagnetic waveguides
    ACTIN = "actin"              # Resonant cavities
    MYOSIN = "myosin"            # Motor protein
    KINESIN = "kinesin"          # Motor protein
    MEMBRANE = "membrane"         # Cell membrane
    CYTOPLASM = "cytoplasm"      # General cytoplasm


@dataclass
class FluorescentMarker:
    """
    Fluorescent marker for cytoplasmic flow visualization
    
    Must be sensitive to electromagnetic fields at cardiac frequency
    """
    name: str
    marker_type: MarkerType
    target_structure: CellularStructure
    
    # Spectral properties
    excitation_wavelength_nm: float
    emission_wavelength_nm: float
    
    # EM sensitivity
    em_sensitive: bool
    resonance_frequency_hz: float  # Frequency of maximum sensitivity
    sensitivity_bandwidth_hz: float  # Bandwidth around resonance
    
    def is_sensitive_at_frequency(self, frequency_hz: float) -> bool:
        """
        Check if marker is sensitive at given frequency
        
        Args:
            frequency_hz: Test frequency [Hz]
            
        Returns:
            True if within sensitivity bandwidth
        """
        if not self.em_sensitive:
            return False
        
        freq_diff = abs(frequency_hz - self.resonance_frequency_hz)
        return freq_diff <= self.sensitivity_bandwidth_hz / 2


@dataclass
class PhaseInterferenceMeasurement:
    """
    Phase interference measurement between cardiac field and cytoplasmic flow
    
    Measures phase difference Δφ between:
    - Cardiac electrical field oscillations (ECG)
    - Cytoplasmic flow oscillations (fluorescence imaging)
    """
    cell_id: str
    cardiac_phase_rad: float  # Phase of cardiac field
    cytoplasm_phase_rad: float  # Phase of cytoplasmic flow
    
    @property
    def phase_difference_rad(self) -> float:
        """Phase difference Δφ = φ_cytoplasm - φ_cardiac"""
        return self.cytoplasm_phase_rad - self.cardiac_phase_rad
    
    @property
    def phase_difference_deg(self) -> float:
        """Phase difference in degrees"""
        return np.degrees(self.phase_difference_rad)
    
    @property
    def phase_coherence(self) -> float:
        """
        Phase coherence measure (0-1)
        
        1.0 = perfect phase lock
        0.0 = random phase
        """
        # Coherence based on phase stability
        # For now, simple cos² measure
        return np.cos(self.phase_difference_rad)**2
    
    def is_phase_locked(self, tolerance_deg: float = 30.0) -> bool:
        """
        Check if cytoplasm is phase-locked to cardiac field
        
        Args:
            tolerance_deg: Phase tolerance in degrees
            
        Returns:
            True if within tolerance
        """
        phase_diff_deg = abs(self.phase_difference_deg)
        # Wrap to [-180, 180]
        while phase_diff_deg > 180:
            phase_diff_deg -= 360
        return abs(phase_diff_deg) <= tolerance_deg


class SpectralValidator:
    """
    Spectral validation framework
    
    Validates presence of harmonic peaks at fₙ = n × 141.7 Hz
    """
    
    def __init__(self, fundamental_hz: float = 141.7001):
        """
        Initialize spectral validator
        
        Args:
            fundamental_hz: Fundamental cardiac frequency
        """
        self.f0_hz = fundamental_hz
        
    def generate_expected_spectrum(self, max_harmonic: int = 10) -> np.ndarray:
        """
        Generate expected harmonic frequencies
        
        Args:
            max_harmonic: Maximum harmonic number
            
        Returns:
            Array of expected frequencies [Hz]
        """
        n = np.arange(1, max_harmonic + 1)
        return n * self.f0_hz
    
    def validate_spectrum(self, measured_frequencies_hz: np.ndarray,
                         measured_powers: np.ndarray,
                         max_harmonic: int = 5,
                         frequency_tolerance_hz: float = 5.0,
                         power_threshold: float = 0.1) -> Dict:
        """
        Validate measured spectrum against expected harmonics
        
        Args:
            measured_frequencies_hz: Measured frequency array [Hz]
            measured_powers: Measured power spectrum
            max_harmonic: Number of harmonics to check
            frequency_tolerance_hz: Tolerance for frequency matching
            power_threshold: Minimum relative power for peak detection
            
        Returns:
            Validation results dictionary
        """
        expected_freqs = self.generate_expected_spectrum(max_harmonic)
        
        # Normalize power spectrum
        power_normalized = measured_powers / np.max(measured_powers)
        
        peaks_found = []
        for n, f_expected in enumerate(expected_freqs, 1):
            # Find peaks near expected frequency
            mask = np.abs(measured_frequencies_hz - f_expected) < frequency_tolerance_hz
            
            if np.any(mask):
                local_powers = power_normalized[mask]
                local_freqs = measured_frequencies_hz[mask]
                
                # Find strongest peak in window
                peak_idx = np.argmax(local_powers)
                peak_power = local_powers[peak_idx]
                peak_freq = local_freqs[peak_idx]
                
                if peak_power >= power_threshold:
                    peaks_found.append({
                        'harmonic': n,
                        'expected_hz': f_expected,
                        'measured_hz': peak_freq,
                        'power': peak_power,
                        'found': True
                    })
                else:
                    peaks_found.append({
                        'harmonic': n,
                        'expected_hz': f_expected,
                        'measured_hz': None,
                        'power': 0.0,
                        'found': False
                    })
            else:
                peaks_found.append({
                    'harmonic': n,
                    'expected_hz': f_expected,
                    'measured_hz': None,
                    'power': 0.0,
                    'found': False
                })
        
        # Calculate validation metrics
        n_found = sum(1 for p in peaks_found if p['found'])
        validation_score = n_found / max_harmonic
        
        return {
            'peaks': peaks_found,
            'harmonics_found': n_found,
            'harmonics_expected': max_harmonic,
            'validation_score': validation_score,
            'validated': validation_score >= 0.6,  # At least 60% of harmonics
            'fundamental_hz': self.f0_hz
        }


class ExperimentalProtocol:
    """
    Complete experimental protocol for cellular resonance validation
    """
    
    def __init__(self):
        """Initialize experimental protocol"""
        self.markers: List[FluorescentMarker] = []
        self.measurements: List[PhaseInterferenceMeasurement] = []
        self.validator = SpectralValidator()
        
    def add_marker(self, marker: FluorescentMarker):
        """Add fluorescent marker to protocol"""
        self.markers.append(marker)
    
    def design_marker_panel(self) -> List[FluorescentMarker]:
        """
        Design complete panel of fluorescent markers
        
        Returns:
            List of recommended markers
        """
        markers = [
            # Magnetic nanoparticles for EM-sensitive imaging
            FluorescentMarker(
                name="MagNP-141",
                marker_type=MarkerType.MAGNETIC_NANOPARTICLE,
                target_structure=CellularStructure.CYTOPLASM,
                excitation_wavelength_nm=488,
                emission_wavelength_nm=520,
                em_sensitive=True,
                resonance_frequency_hz=141.7,
                sensitivity_bandwidth_hz=20.0
            ),
            
            # Microtubule marker (waveguide)
            FluorescentMarker(
                name="Tubulin-GFP",
                marker_type=MarkerType.FLUORESCENT_PROTEIN,
                target_structure=CellularStructure.MICROTUBULE,
                excitation_wavelength_nm=488,
                emission_wavelength_nm=509,
                em_sensitive=False,
                resonance_frequency_hz=0.0,
                sensitivity_bandwidth_hz=0.0
            ),
            
            # Actin marker (resonant cavity)
            FluorescentMarker(
                name="Actin-RFP",
                marker_type=MarkerType.FLUORESCENT_PROTEIN,
                target_structure=CellularStructure.ACTIN,
                excitation_wavelength_nm=558,
                emission_wavelength_nm=583,
                em_sensitive=False,
                resonance_frequency_hz=0.0,
                sensitivity_bandwidth_hz=0.0
            ),
            
            # Voltage-sensitive dye for membrane potential
            FluorescentMarker(
                name="VSD-Fast",
                marker_type=MarkerType.VOLTAGE_SENSITIVE_DYE,
                target_structure=CellularStructure.MEMBRANE,
                excitation_wavelength_nm=520,
                emission_wavelength_nm=600,
                em_sensitive=True,
                resonance_frequency_hz=141.7,
                sensitivity_bandwidth_hz=50.0
            ),
        ]
        
        self.markers = markers
        return markers
    
    def simulate_measurement(self, n_cells: int = 100,
                           phase_noise_std_rad: float = 0.3) -> List[PhaseInterferenceMeasurement]:
        """
        Simulate phase interference measurements
        
        Args:
            n_cells: Number of cells to measure
            phase_noise_std_rad: Standard deviation of phase noise
            
        Returns:
            List of measurements
        """
        measurements = []
        
        for i in range(n_cells):
            # Cardiac phase (reference, set to 0)
            cardiac_phase = 0.0
            
            # Cytoplasm phase with noise (healthy cells should be near 0)
            # Add some biological variation
            cytoplasm_phase = np.random.normal(0.0, phase_noise_std_rad)
            
            measurement = PhaseInterferenceMeasurement(
                cell_id=f"Cell-{i:03d}",
                cardiac_phase_rad=cardiac_phase,
                cytoplasm_phase_rad=cytoplasm_phase
            )
            
            measurements.append(measurement)
        
        self.measurements = measurements
        return measurements
    
    def analyze_population_coherence(self, 
                                    measurements: Optional[List[PhaseInterferenceMeasurement]] = None) -> Dict:
        """
        Analyze phase coherence across cell population
        
        Args:
            measurements: List of measurements (default: use stored)
            
        Returns:
            Population coherence analysis
        """
        if measurements is None:
            measurements = self.measurements
        
        if not measurements:
            return {
                'mean_coherence': 0.0,
                'std_coherence': 0.0,
                'fraction_phase_locked': 0.0,
                'n_cells': 0
            }
        
        coherences = [m.phase_coherence for m in measurements]
        phase_locked = [m.is_phase_locked() for m in measurements]
        
        return {
            'mean_coherence': np.mean(coherences),
            'std_coherence': np.std(coherences),
            'fraction_phase_locked': np.sum(phase_locked) / len(measurements),
            'n_cells': len(measurements),
            'coherences': coherences,
            'phase_differences_deg': [m.phase_difference_deg for m in measurements]
        }
    
    def generate_test_signal(self, duration_s: float = 1.0,
                           sampling_rate_hz: float = 10000,
                           harmonics: List[int] = [1, 2, 3, 4, 5],
                           noise_level: float = 0.1) -> Tuple[np.ndarray, np.ndarray]:
        """
        Generate synthetic test signal with harmonics
        
        Args:
            duration_s: Signal duration [s]
            sampling_rate_hz: Sampling rate [Hz]
            harmonics: List of harmonic numbers to include
            noise_level: Relative noise level (0-1)
            
        Returns:
            (time, signal) arrays
        """
        t = np.linspace(0, duration_s, int(duration_s * sampling_rate_hz))
        signal = np.zeros_like(t)
        
        # Add harmonics
        for n in harmonics:
            f_n = n * self.validator.f0_hz
            amplitude = 1.0 / n  # Decreasing amplitude with harmonic number
            signal += amplitude * np.sin(2 * np.pi * f_n * t)
        
        # Add noise
        if noise_level > 0:
            noise = noise_level * np.random.randn(len(t))
            signal += noise
        
        return t, signal


def create_standard_protocol() -> ExperimentalProtocol:
    """
    Create standard experimental protocol
    
    Returns:
        Configured ExperimentalProtocol instance
    """
    protocol = ExperimentalProtocol()
    protocol.design_marker_panel()
    return protocol


def visualize_phase_coherence(measurements: List[PhaseInterferenceMeasurement]):
    """
    Visualize phase coherence across cell population
    
    Args:
        measurements: List of phase measurements
    """
    if not measurements:
        print("No measurements to visualize")
        return
    
    phase_diffs = [m.phase_difference_deg for m in measurements]
    coherences = [m.phase_coherence for m in measurements]
    
    fig, axes = plt.subplots(2, 1, figsize=(10, 8))
    
    # Phase difference histogram
    axes[0].hist(phase_diffs, bins=30, alpha=0.7, color='blue', edgecolor='black')
    axes[0].axvline(0, color='red', linestyle='--', linewidth=2, label='Perfect phase lock')
    axes[0].set_xlabel('Phase Difference [degrees]')
    axes[0].set_ylabel('Number of Cells')
    axes[0].set_title('Phase Difference Distribution (Cardiac vs Cytoplasm)')
    axes[0].legend()
    axes[0].grid(True, alpha=0.3)
    
    # Coherence scatter
    cell_indices = range(len(measurements))
    axes[1].scatter(cell_indices, coherences, alpha=0.6, s=50)
    axes[1].axhline(0.9, color='green', linestyle='--', label='High coherence threshold')
    axes[1].set_xlabel('Cell Index')
    axes[1].set_ylabel('Phase Coherence')
    axes[1].set_title('Per-Cell Phase Coherence')
    axes[1].set_ylim([0, 1])
    axes[1].legend()
    axes[1].grid(True, alpha=0.3)
    
    plt.tight_layout()
    return fig


def visualize_spectral_validation(frequencies_hz: np.ndarray,
                                  power: np.ndarray,
                                  validation_results: Dict):
    """
    Visualize spectral validation results
    
    Args:
        frequencies_hz: Frequency array
        power: Power spectrum
        validation_results: Results from SpectralValidator
    """
    fig, ax = plt.subplots(figsize=(12, 6))
    
    # Plot power spectrum
    ax.plot(frequencies_hz, power, 'b-', alpha=0.7, linewidth=1, label='Measured spectrum')
    
    # Mark expected harmonics
    for peak in validation_results['peaks']:
        f_expected = peak['expected_hz']
        if peak['found']:
            ax.axvline(f_expected, color='green', linestyle='--', alpha=0.5)
            ax.text(f_expected, ax.get_ylim()[1] * 0.9, 
                   f"n={peak['harmonic']}", 
                   rotation=90, va='top', fontsize=8, color='green')
        else:
            ax.axvline(f_expected, color='red', linestyle=':', alpha=0.3)
    
    ax.set_xlabel('Frequency [Hz]')
    ax.set_ylabel('Power')
    ax.set_title(f"Spectral Validation (Score: {validation_results['validation_score']:.1%})")
    ax.grid(True, alpha=0.3)
    ax.set_xlim([0, validation_results['peaks'][-1]['expected_hz'] * 1.2])
    
    # Add legend
    from matplotlib.patches import Patch
    legend_elements = [
        Patch(facecolor='blue', alpha=0.7, label='Measured spectrum'),
        Patch(facecolor='green', alpha=0.5, label='Harmonic found'),
        Patch(facecolor='red', alpha=0.3, label='Harmonic missing')
    ]
    ax.legend(handles=legend_elements)
    
    plt.tight_layout()
    return fig


if __name__ == "__main__":
    print("="*80)
    print("Molecular Implementation Protocol")
    print("Experimental Validation Framework")
    print("="*80)
    print()
    
    # Create protocol
    protocol = create_standard_protocol()
    
    print("Fluorescent Marker Panel:")
    print("-" * 80)
    for marker in protocol.markers:
        print(f"  {marker.name}")
        print(f"    Type: {marker.marker_type.value}")
        print(f"    Target: {marker.target_structure.value}")
        print(f"    EM-sensitive: {marker.em_sensitive}")
        if marker.em_sensitive:
            print(f"    Resonance: {marker.resonance_frequency_hz:.1f} Hz")
        print()
    
    # Simulate measurements
    print("Phase Interference Measurements:")
    print("-" * 80)
    measurements = protocol.simulate_measurement(n_cells=100, phase_noise_std_rad=0.3)
    
    analysis = protocol.analyze_population_coherence()
    print(f"  Cells measured: {analysis['n_cells']}")
    print(f"  Mean coherence: {analysis['mean_coherence']:.3f}")
    print(f"  Std coherence: {analysis['std_coherence']:.3f}")
    print(f"  Phase-locked fraction: {analysis['fraction_phase_locked']:.1%}")
    print()
    
    # Spectral validation
    print("Spectral Validation:")
    print("-" * 80)
    t, signal = protocol.generate_test_signal(duration_s=1.0, harmonics=[1, 2, 3, 4, 5])
    
    # Compute FFT
    fft = np.fft.rfft(signal)
    freqs = np.fft.rfftfreq(len(signal), t[1] - t[0])
    power = np.abs(fft)**2
    
    validation = protocol.validator.validate_spectrum(freqs, power, max_harmonic=5)
    
    print(f"  Fundamental: {validation['fundamental_hz']:.4f} Hz")
    print(f"  Harmonics found: {validation['harmonics_found']}/{validation['harmonics_expected']}")
    print(f"  Validation score: {validation['validation_score']:.1%}")
    print(f"  Validated: {validation['validated']}")
    print()
    
    for peak in validation['peaks']:
        if peak['found']:
            print(f"    ✓ Harmonic {peak['harmonic']}: " + 
                  f"{peak['expected_hz']:.1f} Hz → {peak['measured_hz']:.1f} Hz " +
                  f"(power: {peak['power']:.3f})")
        else:
            print(f"    ✗ Harmonic {peak['harmonic']}: " +
                  f"{peak['expected_hz']:.1f} Hz (not found)")
    
    print()
    print("="*80)
    print("Instituto Consciencia Cuántica QCAL ∞³")
    print("∴𓂀Ω∞³")
    print("="*80)
