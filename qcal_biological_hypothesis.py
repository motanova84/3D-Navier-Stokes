#!/usr/bin/env python3
"""
QCAL Biological Hypothesis - Spectral Field Theory for Biological Clocks
=========================================================================

Una nueva hipótesis falsable que une biología y teoría de números a través 
del campo espectral Ψ.

This module implements the QCAL (Quantum-Cycle Arithmetic Logic) hypothesis
that biological clocks respond not to simple accumulative signals but to 
structured spectral content. The environmental signal is not just "temperature" 
or raw energy, but integrated vibrational information.

Mathematical Framework:
----------------------
1. Environmental Spectral Field: Ψₑ(t) = Σᵢ Aᵢ exp(i(ωᵢt + φᵢ))
2. Biological Filter: H(ω) = ∫ G(τ)exp(-iωτ)dτ
3. Phase Accumulation: Φ(t) = ∫₀ᵗ |H(ω)*Ψₑ(ω)|² dω
4. Activation Condition: Φ(t) ≥ Φ_crítico AND dΦ/dt > 0
5. Phase Memory: Φ_acum = αΦ(t) + (1-α)Φ(t-Δt), α ≈ 0.1

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
Date: 27 de enero de 2026
License: MIT
"""

import numpy as np
import matplotlib.pyplot as plt
from typing import Dict, Tuple, List, Optional, Callable
from dataclasses import dataclass
from enum import Enum
import warnings


class FrequencyBand(Enum):
    """Biological frequency bands classification"""
    LOW = "low"          # 10⁻⁶ - 10⁻³ Hz: Macro life cycles (seasonal, diurnal, lunar)
    MEDIUM = "medium"    # 0.1 - 100 Hz: Tissue and cellular vibrations
    HIGH = "high"        # >1 kHz: Thermal noise (typically filtered)


@dataclass
class SpectralComponent:
    """Individual spectral component with amplitude, frequency, and phase"""
    amplitude: float      # Aᵢ
    frequency_hz: float   # ωᵢ/2π
    phase_rad: float      # φᵢ
    band: FrequencyBand
    description: str
    
    @property
    def omega_rad_s(self) -> float:
        """Angular frequency in rad/s"""
        return 2 * np.pi * self.frequency_hz


@dataclass
class BiologicalConstants:
    """Constants for QCAL biological model"""
    # Fundamental frequency (derived from Navier-Stokes biofluid solutions)
    F0_HZ: float = 141.7  # Characteristic frequency for biological resonance
    
    # Cycle frequencies
    F_ANNUAL_HZ: float = 1.0 / (365.25 * 24 * 3600)  # ≈ 3.17×10⁻⁸ Hz
    F_DIURNAL_HZ: float = 1.0 / (24 * 3600)          # ≈ 1.16×10⁻⁵ Hz
    F_LUNAR_HZ: float = 1.0 / (29.5 * 24 * 3600)     # ≈ 3.93×10⁻⁷ Hz
    
    # Phase memory parameter (retains 90% of previous phase)
    ALPHA_MEMORY: float = 0.1
    
    # Filter response parameters
    TAU_RESPONSE_S: float = 3600.0  # 1 hour characteristic response time


class SpectralField:
    """
    Represents the environmental spectral field Ψₑ(t)
    
    The field is a superposition of periodic signals from the environment:
    temperature, light, humidity, pressure, etc., expressed as spectral 
    components.
    """
    
    def __init__(self):
        """Initialize empty spectral field"""
        self.components: List[SpectralComponent] = []
        
    def add_component(self, amplitude: float, frequency_hz: float, 
                     phase_rad: float = 0.0, description: str = ""):
        """
        Add a spectral component to the field
        
        Args:
            amplitude: Signal amplitude Aᵢ
            frequency_hz: Frequency in Hz
            phase_rad: Phase in radians (default: 0)
            description: Component description
        """
        # Classify frequency band
        if frequency_hz < 1e-3:
            band = FrequencyBand.LOW
        elif frequency_hz < 100:
            band = FrequencyBand.MEDIUM
        else:
            band = FrequencyBand.HIGH
            
        component = SpectralComponent(
            amplitude=amplitude,
            frequency_hz=frequency_hz,
            phase_rad=phase_rad,
            band=band,
            description=description
        )
        self.components.append(component)
        
    def evaluate(self, t: np.ndarray) -> np.ndarray:
        """
        Evaluate spectral field at time(s) t
        
        Ψₑ(t) = Σᵢ Aᵢ exp(i(ωᵢt + φᵢ))
        
        Args:
            t: Time array [s]
            
        Returns:
            Complex field values
        """
        psi = np.zeros_like(t, dtype=complex)
        for comp in self.components:
            omega = comp.omega_rad_s
            psi += comp.amplitude * np.exp(1j * (omega * t + comp.phase_rad))
        return psi
    
    def get_spectrum(self, t_max: float = None) -> Tuple[np.ndarray, np.ndarray]:
        """
        Get discrete spectrum representation
        
        Returns:
            frequencies: Array of component frequencies [Hz]
            amplitudes: Array of component amplitudes
        """
        if not self.components:
            return np.array([]), np.array([])
            
        frequencies = np.array([c.frequency_hz for c in self.components])
        amplitudes = np.array([c.amplitude for c in self.components])
        return frequencies, amplitudes


class BiologicalFilter:
    """
    Represents the biological filter H(ω) that selects which frequencies
    the organism responds to
    
    H(ω) = ∫ G(τ)exp(-iωτ)dτ
    
    Different organisms have evolved to be sensitive to different spectral
    bands. Not all signals are equally relevant.
    """
    
    def __init__(self, tau_response: float = 3600.0):
        """
        Initialize biological filter
        
        Args:
            tau_response: Characteristic response time [s]
        """
        self.tau = tau_response
        
    def response(self, omega: np.ndarray) -> np.ndarray:
        """
        Filter response function H(ω)
        
        Uses exponential decay model:
        G(τ) = exp(-τ/tau_response)
        H(ω) = 1 / (1 + iω·tau)
        
        Args:
            omega: Angular frequencies [rad/s]
            
        Returns:
            Complex filter response
        """
        return 1.0 / (1.0 + 1j * omega * self.tau)
    
    def apply_band_selectivity(self, frequencies_hz: np.ndarray) -> np.ndarray:
        """
        Apply band-selective filtering based on biological relevance
        
        H(ω) ≈ 1.0 for medium band (1-100 Hz): protein resonances, membranes
        H(ω) ≈ 0.5 for low band: slow integration of environmental cycles
        H(ω) ≈ 0.0 for high band (>1 kHz): thermal noise filtering
        
        Args:
            frequencies_hz: Frequency array [Hz]
            
        Returns:
            Band selectivity weights
        """
        weights = np.zeros_like(frequencies_hz)
        
        for i, f_hz in enumerate(frequencies_hz):
            if f_hz < 1e-3:
                # Low band: slow environmental cycles
                weights[i] = 0.5
            elif f_hz < 100:
                # Medium band: cellular and tissue vibrations
                weights[i] = 1.0
            else:
                # High band: thermal noise
                weights[i] = 0.0
                
        return weights


class PhaseAccumulator:
    """
    Accumulates phase from filtered spectral field
    
    Φ(t) = ∫₀ᵗ |H(ω)*Ψₑ(ω)|² dω
    
    This is the "biological capacitor" that stores information from past cycles.
    """
    
    def __init__(self, alpha: float = 0.1):
        """
        Initialize phase accumulator
        
        Args:
            alpha: Memory parameter (retains 1-α of previous phase)
        """
        self.alpha = alpha
        self.phase_history: List[float] = []
        self.time_history: List[float] = []
        
    def accumulate(self, spectral_field: SpectralField, 
                  bio_filter: BiologicalFilter,
                  t_current: float, dt: float) -> float:
        """
        Accumulate phase at current time
        
        Φ_acum = αΦ(t) + (1-α)Φ(t-Δt)
        
        Args:
            spectral_field: Environmental spectral field
            bio_filter: Biological filter
            t_current: Current time [s]
            dt: Time step [s]
            
        Returns:
            Accumulated phase
        """
        # Get spectrum
        frequencies, amplitudes = spectral_field.get_spectrum()
        
        if len(frequencies) == 0:
            return 0.0
        
        # Apply biological filter
        omega = 2 * np.pi * frequencies
        H = bio_filter.response(omega)
        band_weights = bio_filter.apply_band_selectivity(frequencies)
        
        # Compute spectral energy density
        filtered_amplitude = amplitudes * np.abs(H) * band_weights
        energy_density = np.sum(filtered_amplitude**2) * dt
        
        # Apply memory (exponential weighted average)
        if len(self.phase_history) > 0:
            phase_new = self.alpha * energy_density + \
                       (1 - self.alpha) * self.phase_history[-1]
        else:
            phase_new = energy_density
            
        # Store in history
        self.phase_history.append(phase_new)
        self.time_history.append(t_current)
        
        return phase_new
    
    def get_phase_derivative(self) -> float:
        """
        Get current phase derivative dΦ/dt
        
        Returns:
            Phase derivative (positive if accumulating)
        """
        if len(self.phase_history) < 2:
            return 0.0
            
        dt = self.time_history[-1] - self.time_history[-2]
        if dt == 0:
            return 0.0
            
        dphi = self.phase_history[-1] - self.phase_history[-2]
        return dphi / dt


class BiologicalClock:
    """
    Main biological clock implementing QCAL hypothesis
    
    The clock integrates environmental spectral information and triggers
    biological action when critical phase threshold is reached.
    """
    
    def __init__(self, critical_phase: float, name: str = "Generic Clock"):
        """
        Initialize biological clock
        
        Args:
            critical_phase: Φ_crítico threshold for activation
            name: Clock name/description
        """
        self.name = name
        self.critical_phase = critical_phase
        self.spectral_field = SpectralField()
        self.bio_filter = BiologicalFilter()
        self.phase_accumulator = PhaseAccumulator()
        self.activated = False
        self.activation_time = None
        
        # Constants
        self.constants = BiologicalConstants()
        
    def check_activation_condition(self) -> bool:
        """
        Check activation condition:
        Φ(t) ≥ Φ_crítico AND dΦ/dt > 0
        
        Returns:
            True if activation condition is met
        """
        if len(self.phase_accumulator.phase_history) == 0:
            return False
            
        current_phase = self.phase_accumulator.phase_history[-1]
        phase_derivative = self.phase_accumulator.get_phase_derivative()
        
        threshold_met = current_phase >= self.critical_phase
        flux_positive = phase_derivative > 0
        
        return threshold_met and flux_positive
    
    def simulate(self, t_array: np.ndarray) -> Dict:
        """
        Simulate biological clock over time
        
        Args:
            t_array: Time points [s]
            
        Returns:
            Dictionary with simulation results
        """
        results = {
            'time': t_array,
            'phase': [],
            'phase_derivative': [],
            'activated': False,
            'activation_time': None
        }
        
        # Reset state
        self.phase_accumulator.phase_history = []
        self.phase_accumulator.time_history = []
        self.activated = False
        
        # Simulate
        for i, t in enumerate(t_array):
            dt = t_array[1] - t_array[0] if i == 0 else t_array[i] - t_array[i-1]
            
            # Accumulate phase
            phase = self.phase_accumulator.accumulate(
                self.spectral_field, self.bio_filter, t, dt
            )
            results['phase'].append(phase)
            
            # Check derivative
            dphi_dt = self.phase_accumulator.get_phase_derivative()
            results['phase_derivative'].append(dphi_dt)
            
            # Check activation
            if not self.activated and self.check_activation_condition():
                self.activated = True
                self.activation_time = t
                results['activated'] = True
                results['activation_time'] = t
                
        results['phase'] = np.array(results['phase'])
        results['phase_derivative'] = np.array(results['phase_derivative'])
        
        return results
    
    def add_environmental_cycle(self, amplitude: float, period_days: float,
                               phase_rad: float = 0.0, description: str = ""):
        """
        Add environmental cycle to spectral field
        
        Args:
            amplitude: Cycle amplitude
            period_days: Period in days
            phase_rad: Initial phase
            description: Cycle description
        """
        frequency_hz = 1.0 / (period_days * 24 * 3600)
        self.spectral_field.add_component(
            amplitude, frequency_hz, phase_rad, description
        )


def create_example_annual_cycle() -> SpectralField:
    """
    Create example spectral field with typical annual cycles
    
    Returns:
        SpectralField with seasonal, diurnal, and lunar components
    """
    field = SpectralField()
    
    # Annual cycle (fundamental)
    field.add_component(
        amplitude=1.0,
        frequency_hz=BiologicalConstants.F_ANNUAL_HZ,
        description="Seasonal cycle"
    )
    
    # Diurnal cycle
    field.add_component(
        amplitude=0.3,
        frequency_hz=BiologicalConstants.F_DIURNAL_HZ,
        description="Day-night cycle"
    )
    
    # Lunar cycle
    field.add_component(
        amplitude=0.1,
        frequency_hz=BiologicalConstants.F_LUNAR_HZ,
        description="Lunar cycle"
    )
    
    return field


def visualize_spectral_field(field: SpectralField, t_days: float = 730):
    """
    Visualize spectral field in time and frequency domains
    
    Args:
        field: SpectralField to visualize
        t_days: Time span in days
    """
    # Time domain
    t = np.linspace(0, t_days * 24 * 3600, 10000)
    psi_t = field.evaluate(t)
    
    fig, axes = plt.subplots(2, 1, figsize=(12, 8))
    
    # Plot time domain
    axes[0].plot(t / (24 * 3600), np.real(psi_t), 'b-', alpha=0.7, label='Real part')
    axes[0].plot(t / (24 * 3600), np.imag(psi_t), 'r-', alpha=0.7, label='Imag part')
    axes[0].plot(t / (24 * 3600), np.abs(psi_t), 'k-', linewidth=2, label='|Ψ|')
    axes[0].set_xlabel('Time [days]')
    axes[0].set_ylabel('Ψₑ(t)')
    axes[0].set_title('Environmental Spectral Field - Time Domain')
    axes[0].legend()
    axes[0].grid(True, alpha=0.3)
    
    # Plot frequency domain
    freqs, amps = field.get_spectrum()
    if len(freqs) > 0:
        axes[1].stem(freqs * (24 * 3600), amps, basefmt=' ')
        axes[1].set_xlabel('Frequency [cycles/day]')
        axes[1].set_ylabel('Amplitude')
        axes[1].set_title('Spectral Content')
        axes[1].set_xscale('log')
        axes[1].grid(True, alpha=0.3)
        
        # Add component labels
        for i, comp in enumerate(field.components):
            f_per_day = comp.frequency_hz * (24 * 3600)
            axes[1].text(f_per_day, amps[i], f' {comp.description}',
                        rotation=45, va='bottom', fontsize=8)
    
    plt.tight_layout()
    return fig


if __name__ == "__main__":
    print("="*80)
    print("QCAL Biological Hypothesis - Core Module")
    print("="*80)
    print()
    print("Mathematical Framework:")
    print("  Ψₑ(t) = Σᵢ Aᵢ exp(i(ωᵢt + φᵢ))  - Environmental spectral field")
    print("  H(ω) = ∫ G(τ)exp(-iωτ)dτ         - Biological filter")
    print("  Φ(t) = ∫₀ᵗ |H(ω)*Ψₑ(ω)|² dω      - Phase accumulation")
    print("  Φ ≥ Φ_crítico AND dΦ/dt > 0      - Activation condition")
    print("  Φ_acum = αΦ(t) + (1-α)Φ(t-Δt)    - Phase memory")
    print()
    print("Biological frequency bands:")
    print(f"  Low band (10⁻⁶-10⁻³ Hz): Macro cycles (seasonal, lunar)")
    print(f"  Medium band (0.1-100 Hz): Cellular vibrations")
    print(f"  High band (>1 kHz): Thermal noise (filtered)")
    print()
    print("Fundamental frequency: f₀ = 141.7 Hz")
    print("  (Derived from Navier-Stokes biofluid solutions)")
    print()
    print("Instituto Consciencia Cuántica QCAL ∞³")
    print("="*80)
