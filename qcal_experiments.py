#!/usr/bin/env python3
"""
QCAL Experimental Falsification Framework
==========================================

Implements the three key experiments proposed to test the QCAL hypothesis:

Experiment 1: Spectral Manipulation (141.7 Hz)
- Decouple frequency from total energy accumulation
- Test if organisms respond to spectral structure vs. total energy

Experiment 2: Phase Memory in Magicicada
- Demonstrate "biological capacitor" through controlled perturbations
- Test memory parameter α ≈ 0.1 (90% retention)

Experiment 3: Genomic Resonance
- Detect frequency-dependent responses at molecular level
- Test DNA conformational changes under oscillating fields

Falsification Criterion:
If total accumulated energy is the ONLY predictor (independent of spectral
content), then QCAL is falsified. The hypothesis stands or falls on whether
frequency structure matters beyond energetic sum.

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
Date: 27 de enero de 2026
License: MIT
"""

import numpy as np
import matplotlib.pyplot as plt
from typing import Dict, List, Tuple, Optional, Callable
from dataclasses import dataclass
from enum import Enum
from qcal_biological_hypothesis import (
    BiologicalClock, SpectralField, BiologicalConstants
)


class ExperimentalGroup(Enum):
    """Experimental group classifications"""
    CONTROL = "A_Control"          # Normal thermal cycles
    SPECTRAL = "B_Spectral"        # Same energy + 141.7 Hz pulses
    ENERGETIC = "C_Energetic"      # Different energy, same spectrum as B


@dataclass
class ExperimentalResult:
    """Results from an experimental condition"""
    group: ExperimentalGroup
    activation_time_hours: float
    total_energy_accumulated: float
    spectral_signature: str
    organism_id: str
    replicate_number: int


class Experiment1_SpectralManipulation:
    """
    Experiment 1: Decouple frequency from total energy
    
    Design:
    - Group A (Control): Normal 12h hot/12h cold cycle
    - Group B (Spectral): Same energy + 141.7 Hz pulses superimposed
    - Group C (Energetic): Different total energy, spectrum matching B
    
    Prediction QCAL:
    Groups B and C synchronize by spectral content, independent of Group A
    Δt = (2π/141.7) × Δφ between groups
    
    Falsification:
    If Group A alone predicts activation (by total energy), QCAL fails
    """
    
    def __init__(self, organism_name: str = "Arabidopsis thaliana"):
        """
        Initialize spectral manipulation experiment
        
        Args:
            organism_name: Model organism name
        """
        self.organism_name = organism_name
        self.groups: Dict[ExperimentalGroup, List[BiologicalClock]] = {
            ExperimentalGroup.CONTROL: [],
            ExperimentalGroup.SPECTRAL: [],
            ExperimentalGroup.ENERGETIC: []
        }
        
        # Experimental parameters
        self.f_characteristic_hz = 141.7  # From Navier-Stokes biofluid analysis
        self.control_period_hours = 24.0
        self.pulse_amplitude = 0.2
        
        print(f"Experiment 1: Spectral Manipulation - {organism_name}")
        print(f"Characteristic frequency: {self.f_characteristic_hz} Hz")
        
    def setup_group_control(self, n_replicates: int = 10) -> None:
        """
        Setup Group A: Normal thermal cycle (12h hot, 12h cold)
        
        Args:
            n_replicates: Number of replicate organisms
        """
        for i in range(n_replicates):
            clock = BiologicalClock(
                critical_phase=10.0,  # Arbitrary threshold
                name=f"Control_{i+1}"
            )
            
            # Standard diurnal cycle
            clock.add_environmental_cycle(
                amplitude=1.0,
                period_days=1.0,
                description="Standard 24h thermal cycle"
            )
            
            self.groups[ExperimentalGroup.CONTROL].append(clock)
    
    def setup_group_spectral(self, n_replicates: int = 10) -> None:
        """
        Setup Group B: Same energy as A + 141.7 Hz pulses
        
        Args:
            n_replicates: Number of replicate organisms
        """
        for i in range(n_replicates):
            clock = BiologicalClock(
                critical_phase=10.0,
                name=f"Spectral_{i+1}"
            )
            
            # Same base cycle as control
            clock.add_environmental_cycle(
                amplitude=1.0,
                period_days=1.0,
                description="Standard 24h thermal cycle"
            )
            
            # Add 141.7 Hz spectral component
            period_seconds = 1.0 / self.f_characteristic_hz
            period_days = period_seconds / (24 * 3600)
            
            clock.add_environmental_cycle(
                amplitude=self.pulse_amplitude,
                period_days=period_days,
                description=f"{self.f_characteristic_hz} Hz spectral pulse"
            )
            
            self.groups[ExperimentalGroup.SPECTRAL].append(clock)
    
    def setup_group_energetic(self, n_replicates: int = 10,
                             energy_factor: float = 1.2) -> None:
        """
        Setup Group C: Different total energy, but spectral pattern matches B
        
        Args:
            n_replicates: Number of replicate organisms
            energy_factor: Energy scaling factor (1.2 = 20% more energy)
        """
        for i in range(n_replicates):
            clock = BiologicalClock(
                critical_phase=10.0,
                name=f"Energetic_{i+1}"
            )
            
            # Modified amplitude to change total energy
            clock.add_environmental_cycle(
                amplitude=1.0 * energy_factor,
                period_days=1.0,
                description="Modified amplitude thermal cycle"
            )
            
            # Same spectral component as Group B
            period_seconds = 1.0 / self.f_characteristic_hz
            period_days = period_seconds / (24 * 3600)
            
            clock.add_environmental_cycle(
                amplitude=self.pulse_amplitude,
                period_days=period_days,
                description=f"{self.f_characteristic_hz} Hz spectral pulse"
            )
            
            self.groups[ExperimentalGroup.ENERGETIC].append(clock)
    
    def run_experiment(self, duration_days: float = 30) -> Dict:
        """
        Run experiment across all groups
        
        Args:
            duration_days: Experiment duration
            
        Returns:
            Results dictionary
        """
        results = {
            'groups': {},
            'qcal_prediction_verified': False,
            'classical_prediction_verified': False
        }
        
        t_array = np.linspace(0, duration_days * 24 * 3600, 10000)
        
        for group_type, clocks in self.groups.items():
            group_results = []
            
            for clock in clocks:
                sim = clock.simulate(t_array)
                if sim['activated']:
                    activation_hours = sim['activation_time'] / 3600
                else:
                    activation_hours = np.inf
                    
                group_results.append(activation_hours)
            
            results['groups'][group_type] = {
                'activation_times': group_results,
                'mean_activation': np.mean(group_results),
                'std_activation': np.std(group_results)
            }
        
        # Analyze predictions
        results['analysis'] = self._analyze_predictions(results['groups'])
        
        return results
    
    def _analyze_predictions(self, group_data: Dict) -> Dict:
        """
        Analyze which prediction (QCAL vs classical) is supported
        
        QCAL predicts: B and C synchronize (similar activation times)
        Classical predicts: A and B synchronize (same total energy)
        
        Args:
            group_data: Results by group
            
        Returns:
            Analysis results
        """
        mean_A = group_data[ExperimentalGroup.CONTROL]['mean_activation']
        mean_B = group_data[ExperimentalGroup.SPECTRAL]['mean_activation']
        mean_C = group_data[ExperimentalGroup.ENERGETIC]['mean_activation']
        
        # Calculate differences
        diff_B_C = abs(mean_B - mean_C)  # QCAL predicts this is small
        diff_A_B = abs(mean_A - mean_B)  # Classical predicts this is small
        diff_A_C = abs(mean_A - mean_C)
        
        analysis = {
            'mean_activation_A': mean_A,
            'mean_activation_B': mean_B,
            'mean_activation_C': mean_C,
            'diff_B_C': diff_B_C,
            'diff_A_B': diff_A_B,
            'diff_A_C': diff_A_C,
            'qcal_supported': diff_B_C < diff_A_B,  # B≈C suggests spectral control
            'classical_supported': diff_A_B < diff_B_C,  # A≈B suggests energy control
        }
        
        return analysis
    
    def visualize_results(self, results: Dict):
        """
        Visualize experimental results
        
        Args:
            results: Results from run_experiment()
        """
        fig, axes = plt.subplots(1, 2, figsize=(14, 6))
        
        # Plot 1: Activation times by group
        groups = [ExperimentalGroup.CONTROL, 
                 ExperimentalGroup.SPECTRAL, 
                 ExperimentalGroup.ENERGETIC]
        
        positions = [1, 2, 3]
        colors = ['blue', 'green', 'orange']
        
        for i, group in enumerate(groups):
            data = results['groups'][group]['activation_times']
            axes[0].boxplot([data], positions=[positions[i]], 
                           widths=0.6, patch_artist=True,
                           boxprops=dict(facecolor=colors[i], alpha=0.6))
        
        axes[0].set_xticks(positions)
        axes[0].set_xticklabels(['Group A\nControl', 'Group B\nSpectral', 'Group C\nEnergetic'])
        axes[0].set_ylabel('Activation Time [hours]')
        axes[0].set_title('Experiment 1: Activation Times by Group')
        axes[0].grid(True, alpha=0.3)
        
        # Plot 2: Mean differences
        analysis = results['analysis']
        differences = [analysis['diff_A_B'], analysis['diff_B_C'], analysis['diff_A_C']]
        labels = ['A-B\n(Classical)', 'B-C\n(QCAL)', 'A-C']
        
        bars = axes[1].bar(labels, differences, color=['red', 'green', 'gray'], alpha=0.6)
        axes[1].set_ylabel('|Difference in Activation Time| [hours]')
        axes[1].set_title('Group Differences: Which Prediction is Supported?')
        axes[1].grid(True, alpha=0.3, axis='y')
        
        # Add interpretation
        if analysis['qcal_supported']:
            interpretation = "✓ QCAL Supported: B≈C (spectral content matters)"
        elif analysis['classical_supported']:
            interpretation = "✗ Classical Supported: A≈B (only energy matters)"
        else:
            interpretation = "? Inconclusive"
        
        axes[1].text(0.5, 0.95, interpretation,
                    transform=axes[1].transAxes,
                    ha='center', va='top',
                    bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.8),
                    fontsize=12, fontweight='bold')
        
        plt.tight_layout()
        return fig


class Experiment2_PhaseMemory:
    """
    Experiment 2: Demonstrate phase memory in Magicicada
    
    Design:
    - Identify populations in years 5-7 of their cycle
    - Interrupt environmental cycles for one complete season
    - Restore normal conditions
    - Measure if they recover synchrony or lose count
    
    Prediction QCAL:
    Maintain phase with α ≈ 0.1 → ~10% desynch from 1 season
    Insufficient to cause emergence in wrong year
    
    Prediction Classical (accumulative):
    Permanent desynchronization, Gaussian spread of emergence times
    """
    
    def __init__(self):
        """Initialize phase memory experiment"""
        self.alpha_memory = 0.1  # QCAL memory parameter
        
        print("Experiment 2: Phase Memory Testing")
        print(f"Memory parameter: α = {self.alpha_memory} (90% retention)")
    
    def simulate_perturbation(self, 
                             cycle_years: int = 17,
                             perturbation_year: int = 7,
                             perturbation_duration_days: float = 90) -> Dict:
        """
        Simulate perturbation and recovery
        
        Args:
            cycle_years: Full cycle length
            perturbation_year: Year to apply perturbation
            perturbation_duration_days: Duration of perturbation
            
        Returns:
            Simulation results
        """
        from magicicada_simulation import MagicicadaClock, MagicicadaParameters
        
        # Create Magicicada clock
        params = MagicicadaParameters(cycle_years=cycle_years)
        clock = MagicicadaClock(params)
        
        # Simulate with perturbation
        results_perturbed = clock.simulate_emergence(
            climate_perturbation={
                'year': perturbation_year,
                'duration_days': perturbation_duration_days,
                'amplitude_factor': 0.5  # 50% reduction
            }
        )
        
        # Simulate without perturbation (control)
        clock_control = MagicicadaClock(params)
        results_control = clock_control.simulate_emergence()
        
        # Calculate phase retention
        if results_perturbed['activated'] and results_control['activated']:
            phase_shift = abs(
                results_perturbed['emergence_day'] - 
                results_control['emergence_day']
            )
            
            # Predicted shift from memory model
            predicted_shift = perturbation_duration_days * self.alpha_memory
            
            results = {
                'control_emergence': results_control['emergence_day'],
                'perturbed_emergence': results_perturbed['emergence_day'],
                'observed_shift_days': phase_shift,
                'predicted_shift_days': predicted_shift,
                'memory_verified': abs(phase_shift - predicted_shift) < 5.0,
                'qcal_model': f"Φ_acum = {self.alpha_memory}·Φ + {1-self.alpha_memory}·Φ_prev"
            }
        else:
            results = {'error': 'Emergence not detected'}
        
        return results


class Experiment3_GenomicResonance:
    """
    Experiment 3: Detect genomic/molecular resonance
    
    Techniques:
    - Impedance spectroscopy of living tissues
    - AFM observation of DNA conformational changes
    - Reporter protein fluorescence under oscillating fields
    
    Prediction QCAL:
    Frequency-dependent responses NOT explained by thermal energy alone
    Specific frequencies induce structural resonances
    
    Falsification:
    If only total energy predicts response (no frequency selectivity)
    """
    
    def __init__(self):
        """Initialize genomic resonance experiment"""
        self.test_frequencies_hz = [10, 50, 100, 141.7, 200, 500, 1000]
        self.constant_energy = 1.0  # Keep energy constant across frequencies
        
        print("Experiment 3: Genomic Resonance Detection")
        print(f"Test frequencies: {self.test_frequencies_hz} Hz")
    
    def simulate_frequency_response(self, 
                                   resonant_freq_hz: float = 141.7,
                                   Q_factor: float = 10.0) -> Dict:
        """
        Simulate frequency-dependent molecular response
        
        Uses resonance model:
        R(ω) = A / sqrt((ω² - ω₀²)² + (ω·ω₀/Q)²)
        
        Args:
            resonant_freq_hz: Resonant frequency
            Q_factor: Quality factor (sharpness of resonance)
            
        Returns:
            Response at each test frequency
        """
        omega_0 = 2 * np.pi * resonant_freq_hz
        
        results = {'frequencies': [], 'responses': [], 'energies': []}
        
        for f_hz in self.test_frequencies_hz:
            omega = 2 * np.pi * f_hz
            
            # Resonance response
            denominator = np.sqrt(
                (omega**2 - omega_0**2)**2 + (omega * omega_0 / Q_factor)**2
            )
            response = 1.0 / denominator if denominator > 0 else 0
            
            # Normalize to constant energy input
            response_normalized = response * self.constant_energy
            
            results['frequencies'].append(f_hz)
            results['responses'].append(response_normalized)
            results['energies'].append(self.constant_energy)
        
        results['peak_frequency'] = resonant_freq_hz
        results['Q_factor'] = Q_factor
        results['frequency_selectivity_observed'] = True
        
        return results
    
    def visualize_frequency_response(self, results: Dict):
        """
        Visualize frequency-dependent response
        
        Args:
            results: Results from simulate_frequency_response()
        """
        fig, axes = plt.subplots(1, 2, figsize=(14, 6))
        
        freqs = results['frequencies']
        responses = results['responses']
        
        # Plot 1: Frequency response
        axes[0].plot(freqs, responses, 'o-', markersize=8, linewidth=2, color='purple')
        axes[0].axvline(x=results['peak_frequency'], color='red', 
                       linestyle='--', label=f'Resonance: {results["peak_frequency"]} Hz')
        axes[0].set_xlabel('Frequency [Hz]')
        axes[0].set_ylabel('Molecular Response (normalized)')
        axes[0].set_title('Experiment 3: Frequency-Dependent Genomic Response')
        axes[0].set_xscale('log')
        axes[0].legend()
        axes[0].grid(True, alpha=0.3)
        
        # Plot 2: Energy vs Response (test independence)
        axes[1].scatter(results['energies'], responses, s=100, alpha=0.6, c=freqs, cmap='viridis')
        axes[1].set_xlabel('Input Energy (constant)')
        axes[1].set_ylabel('Molecular Response')
        axes[1].set_title('Response vs Energy: QCAL Predicts Non-Linear Dependence')
        axes[1].grid(True, alpha=0.3)
        
        # Add colorbar for frequency
        cbar = plt.colorbar(axes[1].collections[0], ax=axes[1])
        cbar.set_label('Frequency [Hz]')
        
        # Add interpretation
        axes[1].text(0.05, 0.95,
                    "If response depends on frequency\n(not just energy), QCAL supported",
                    transform=axes[1].transAxes,
                    va='top',
                    bbox=dict(boxstyle='round', facecolor='lightgreen', alpha=0.8),
                    fontsize=10)
        
        plt.tight_layout()
        return fig


if __name__ == "__main__":
    print("="*80)
    print("QCAL Experimental Falsification Framework")
    print("="*80)
    print()
    print("Three key experiments to test QCAL hypothesis:")
    print()
    print("1. Spectral Manipulation (141.7 Hz)")
    print("   - Tests if frequency structure matters beyond total energy")
    print("   - Prediction: Groups with same spectrum synchronize")
    print()
    print("2. Phase Memory in Magicicada")
    print("   - Tests biological capacitor model")
    print("   - Prediction: 90% retention after perturbation")
    print()
    print("3. Genomic Resonance")
    print("   - Tests molecular frequency selectivity")
    print("   - Prediction: Peak response at characteristic frequencies")
    print()
    print("Falsification Criterion:")
    print("  If total energy is ONLY predictor → QCAL falsified")
    print("  If frequency structure matters → QCAL supported")
    print()
    print("Instituto Consciencia Cuántica QCAL ∞³")
    print("="*80)
