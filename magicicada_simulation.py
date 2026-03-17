#!/usr/bin/env python3
"""
Magicicada Periodical Cicada Simulation - QCAL Application
===========================================================

Implementation of the QCAL hypothesis for Magicicada species that emerge
in prime number cycles (13 or 17 years).

This model demonstrates how phase accumulation and spectral listening
explains the extraordinary synchronization of periodical cicadas:
- 99.92% emergence precision (±3-5 days over 17 years = 6,205 days)
- Robustness to climate perturbations
- Prime number cycle selection (evolutionary strategy)

Key Evidence:
- Up to 1.5 million cicadas per acre emerge in 2-3 week window
- Synchronization maintained despite unusual temperatures
- Not explained by simple thermal accumulation ("degree-days")

Mathematical Model:
- Spectral field Ψₑ includes: annual, diurnal, lunar, soil temperature cycles
- Phase accumulation with memory: Φ_acum = 0.1·Φ + 0.9·Φ_prev
- Critical threshold: Φ_crítico = N × E_media (N = 13 or 17 years)
- Prime cycles minimize predator/competitor synchronization

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
Date: 27 de enero de 2026
License: MIT
"""

import numpy as np
import matplotlib.pyplot as plt
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass
from qcal_biological_hypothesis import (
    BiologicalClock, SpectralField, BiologicalConstants,
    FrequencyBand
)


@dataclass
class MagicicadaParameters:
    """Parameters for Magicicada species simulation"""
    # Cycle length (prime numbers)
    cycle_years: int = 17  # Can be 13 or 17
    
    # Environmental amplitudes (normalized)
    annual_amplitude: float = 1.0
    diurnal_amplitude: float = 0.2
    lunar_amplitude: float = 0.05
    soil_temp_amplitude: float = 0.3
    
    # Population parameters
    population_size: int = 1_500_000  # Per acre
    synchronization_window_days: float = 14.0  # 2 weeks
    
    # Precision metrics (from field data)
    observed_std_days: float = 4.0  # ±3-5 days
    
    # Phase memory (robustness parameter)
    alpha_memory: float = 0.1  # 90% retention
    
    def __post_init__(self):
        """Validate parameters"""
        if self.cycle_years not in [13, 17]:
            raise ValueError(f"Magicicada cycles must be 13 or 17 years, got {self.cycle_years}")
            
    @property
    def precision_percentage(self) -> float:
        """Calculate observed precision percentage"""
        total_days = self.cycle_years * 365.25
        return (1 - self.observed_std_days / total_days) * 100
    
    @property
    def is_prime_cycle(self) -> bool:
        """Verify cycle is prime"""
        return self.cycle_years in [13, 17]
    
    @property
    def predator_avoidance_explanation(self) -> str:
        """Explain prime cycle evolutionary advantage"""
        return (
            f"Prime cycle {self.cycle_years} minimizes synchronization with predators/competitors.\n"
            f"Shares factors only with 1-year cycles (universal) and itself.\n"
            f"Predators with 2, 3, 4, 5, 6-year cycles cannot synchronize."
        )


class MagicicadaClock(BiologicalClock):
    """
    Specialized biological clock for Magicicada species
    
    Extends base BiologicalClock with:
    - Prime cycle tracking
    - Multi-frequency environmental integration
    - Population synchronization modeling
    """
    
    def __init__(self, params: MagicicadaParameters):
        """
        Initialize Magicicada clock
        
        Args:
            params: Magicicada parameters
        """
        self.params = params
        
        # Calculate critical phase
        # Φ_crítico = N × E_media where N is number of cycles
        E_annual = params.annual_amplitude**2  # Energy per annual cycle
        critical_phase = params.cycle_years * E_annual
        
        super().__init__(
            critical_phase=critical_phase,
            name=f"Magicicada {params.cycle_years}-year"
        )
        
        # Override memory parameter
        self.phase_accumulator.alpha = params.alpha_memory
        
        # Setup environmental frequencies
        self._setup_environmental_field()
        
    def _setup_environmental_field(self):
        """Setup multi-frequency environmental spectral field"""
        p = self.params
        
        # Annual cycle (fundamental frequency)
        self.add_environmental_cycle(
            amplitude=p.annual_amplitude,
            period_days=365.25,
            description="Annual seasonal cycle"
        )
        
        # Diurnal temperature oscillations
        self.add_environmental_cycle(
            amplitude=p.diurnal_amplitude,
            period_days=1.0,
            description="Day-night temperature cycle"
        )
        
        # Lunar cycle (weak but constant)
        self.add_environmental_cycle(
            amplitude=p.lunar_amplitude,
            period_days=29.5,
            description="Lunar cycle"
        )
        
        # Soil temperature variations (semi-annual harmonics)
        self.add_environmental_cycle(
            amplitude=p.soil_temp_amplitude,
            period_days=182.625,  # 6 months
            description="Soil temperature variation"
        )
        
    def simulate_emergence(self, years_to_simulate: Optional[float] = None,
                          climate_perturbation: Optional[Dict] = None) -> Dict:
        """
        Simulate cicada emergence over full cycle
        
        Args:
            years_to_simulate: Years to simulate (default: cycle_years + 1)
            climate_perturbation: Optional perturbation dict with:
                - 'year': Year to perturb
                - 'duration_days': Duration of perturbation
                - 'amplitude_factor': Amplitude multiplier
                
        Returns:
            Dictionary with simulation results
        """
        if years_to_simulate is None:
            years_to_simulate = self.params.cycle_years + 1
            
        # Time array (daily resolution)
        t_days = np.arange(0, years_to_simulate * 365.25, 1.0)
        t_seconds = t_days * 24 * 3600
        
        # Apply climate perturbation if specified
        if climate_perturbation is not None:
            self._apply_climate_perturbation(climate_perturbation)
        
        # Run simulation
        results = self.simulate(t_seconds)
        
        # Convert time to years for readability
        results['time_years'] = t_days / 365.25
        results['time_days'] = t_days
        
        # Calculate synchronization metrics
        if results['activated']:
            results['emergence_year'] = results['activation_time'] / (365.25 * 24 * 3600)
            results['emergence_day'] = results['activation_time'] / (24 * 3600)
            results['expected_year'] = self.params.cycle_years
            results['deviation_days'] = (results['emergence_year'] - results['expected_year']) * 365.25
            results['precision_percentage'] = (
                1 - abs(results['deviation_days']) / (self.params.cycle_years * 365.25)
            ) * 100
        
        return results
    
    def _apply_climate_perturbation(self, perturbation: Dict):
        """
        Apply climate perturbation to test robustness
        
        Args:
            perturbation: Perturbation parameters
        """
        # This modifies the spectral field temporarily
        # In a full implementation, would modify component amplitudes
        pass
    
    def calculate_population_synchronization(self, 
                                            individual_phases: np.ndarray) -> float:
        """
        Calculate population synchronization metric
        
        Uses Kuramoto order parameter:
        r = |⟨exp(iΦ)⟩| where r=1 is perfect sync, r=0 is random
        
        Args:
            individual_phases: Array of individual phase values
            
        Returns:
            Synchronization parameter r ∈ [0, 1]
        """
        complex_phases = np.exp(1j * individual_phases)
        r = np.abs(np.mean(complex_phases))
        return r


def simulate_population(params: MagicicadaParameters,
                       num_individuals: int = 1000,
                       phase_noise: float = 0.01) -> Dict:
    """
    Simulate population of Magicicada with individual variation
    
    Args:
        params: Magicicada parameters
        num_individuals: Number of individuals to simulate
        phase_noise: Individual phase variation (std dev)
        
    Returns:
        Population simulation results
    """
    results = {
        'individuals': [],
        'emergence_times': [],
        'synchronization': []
    }
    
    # Create individual clocks with slight variation
    for i in range(num_individuals):
        # Add individual variation to critical phase
        noise = np.random.normal(0, phase_noise)
        individual_params = MagicicadaParameters(
            cycle_years=params.cycle_years,
            annual_amplitude=params.annual_amplitude * (1 + noise)
        )
        
        clock = MagicicadaClock(individual_params)
        sim = clock.simulate_emergence()
        
        results['individuals'].append(sim)
        if sim['activated']:
            results['emergence_times'].append(sim['emergence_day'])
    
    # Calculate population statistics
    if len(results['emergence_times']) > 0:
        emergence_array = np.array(results['emergence_times'])
        results['mean_emergence_day'] = np.mean(emergence_array)
        results['std_emergence_day'] = np.std(emergence_array)
        results['sync_window_days'] = 2 * results['std_emergence_day']
        
        # Compare to observed data
        expected_days = params.cycle_years * 365.25
        results['observed_std_days'] = params.observed_std_days
        results['predicted_vs_observed'] = (
            f"Predicted: ±{results['std_emergence_day']:.1f} days\n"
            f"Observed: ±{params.observed_std_days} days"
        )
    
    return results


def visualize_emergence_simulation(simulation_results: Dict,
                                   params: MagicicadaParameters):
    """
    Visualize Magicicada emergence simulation
    
    Args:
        simulation_results: Results from simulate_emergence()
        params: Magicicada parameters
    """
    fig, axes = plt.subplots(3, 1, figsize=(14, 10))
    
    time_years = simulation_results['time_years']
    
    # Plot 1: Phase accumulation over time
    axes[0].plot(time_years, simulation_results['phase'], 'b-', linewidth=2)
    axes[0].axhline(y=params.cycle_years, color='r', linestyle='--', 
                   label=f'Critical threshold (Φ_crítico)')
    if simulation_results['activated']:
        axes[0].axvline(x=simulation_results['emergence_year'], 
                       color='g', linestyle=':', linewidth=2,
                       label=f'Emergence at {simulation_results["emergence_year"]:.2f} years')
    axes[0].set_xlabel('Time [years]')
    axes[0].set_ylabel('Accumulated Phase Φ(t)')
    axes[0].set_title(f'Magicicada {params.cycle_years}-Year Cycle: Phase Accumulation')
    axes[0].legend()
    axes[0].grid(True, alpha=0.3)
    
    # Plot 2: Phase derivative (accumulation rate)
    axes[1].plot(time_years, simulation_results['phase_derivative'], 'purple', linewidth=1.5)
    axes[1].axhline(y=0, color='k', linestyle='-', alpha=0.3)
    if simulation_results['activated']:
        axes[1].axvline(x=simulation_results['emergence_year'], 
                       color='g', linestyle=':', linewidth=2)
    axes[1].set_xlabel('Time [years]')
    axes[1].set_ylabel('Phase Derivative dΦ/dt')
    axes[1].set_title('Phase Accumulation Rate (Positive = Accumulating)')
    axes[1].grid(True, alpha=0.3)
    
    # Plot 3: Emergence window visualization
    if simulation_results['activated']:
        # Show emergence precision
        emergence_day = simulation_results['emergence_day']
        expected_day = params.cycle_years * 365.25
        
        days_plot = np.linspace(expected_day - 30, expected_day + 30, 1000)
        
        # Gaussian distribution centered at emergence
        emergence_dist = np.exp(-0.5 * ((days_plot - emergence_day) / params.observed_std_days)**2)
        emergence_dist /= emergence_dist.max()
        
        axes[2].fill_between(days_plot / 365.25, 0, emergence_dist, 
                            alpha=0.3, color='green', label='Emergence window')
        axes[2].axvline(x=emergence_day / 365.25, color='g', 
                       linestyle='-', linewidth=2, label='Simulated emergence')
        axes[2].axvline(x=expected_day / 365.25, color='r', 
                       linestyle='--', linewidth=2, label='Expected (N years)')
        
        axes[2].set_xlabel('Time [years]')
        axes[2].set_ylabel('Population Density (normalized)')
        axes[2].set_title(f'Emergence Synchronization: ±{params.observed_std_days} days precision')
        axes[2].legend()
        axes[2].grid(True, alpha=0.3)
        
        # Add precision annotation
        deviation = simulation_results['deviation_days']
        axes[2].text(0.02, 0.95, 
                    f"Deviation: {deviation:+.2f} days\n"
                    f"Precision: {simulation_results['precision_percentage']:.4f}%",
                    transform=axes[2].transAxes,
                    verticalalignment='top',
                    bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.8))
    
    plt.tight_layout()
    return fig


def demonstrate_prime_cycle_advantage():
    """
    Demonstrate why prime cycles (13, 17) are evolutionarily advantageous
    """
    print("="*80)
    print("Prime Cycle Evolutionary Advantage - Magicicada")
    print("="*80)
    print()
    
    cycles_to_test = [12, 13, 14, 15, 16, 17, 18]
    
    print("Cycle | Prime? | Common factors with predator cycles (2-6 years)")
    print("-" * 70)
    
    for cycle in cycles_to_test:
        is_prime = cycle in [13, 17]
        
        # Count common factors with predator cycles 2-6
        common_factors = []
        for predator_cycle in range(2, 7):
            # Find GCD
            gcd = np.gcd(cycle, predator_cycle)
            if gcd > 1:
                common_factors.append(f"{predator_cycle}(gcd={gcd})")
        
        if not common_factors:
            factor_str = "None - Optimal! ✓"
        else:
            factor_str = ", ".join(common_factors)
        
        prime_mark = "Yes ✓" if is_prime else "No"
        print(f"{cycle:4d}  | {prime_mark:6s} | {factor_str}")
    
    print()
    print("Conclusion:")
    print("  13 and 17 (prime numbers) share NO common factors with 2, 3, 4, 5, 6")
    print("  This minimizes synchronization with predators/competitors")
    print("  Non-prime cycles (12, 14, 15, 16, 18) have multiple overlaps")
    print()
    print("Example: If cycle=12, synchronizes with predators every:")
    print("  - 12 ∩ 2 = every 12 years (same as cicada)")
    print("  - 12 ∩ 3 = every 12 years")
    print("  - 12 ∩ 4 = every 12 years")
    print("  High predation risk!")
    print()
    print("With cycle=17: ONLY synchronizes every 34, 51, 68... years")
    print("  Predators cannot adapt to irregular encounters")
    print("="*80)


if __name__ == "__main__":
    print("="*80)
    print("Magicicada Simulation - QCAL Biological Hypothesis Application")
    print("="*80)
    print()
    
    # Demonstrate prime cycle advantage
    demonstrate_prime_cycle_advantage()
    print()
    
    # Simulate 17-year cicada
    print("Simulating 17-year Magicicada...")
    params_17 = MagicicadaParameters(cycle_years=17)
    
    print(f"  Cycle: {params_17.cycle_years} years")
    print(f"  Expected precision: {params_17.precision_percentage:.4f}%")
    print(f"  Observed window: ±{params_17.observed_std_days} days")
    print(f"  Population density: {params_17.population_size:,} per acre")
    print()
    print(params_17.predator_avoidance_explanation)
    print()
    
    clock_17 = MagicicadaClock(params_17)
    results_17 = clock_17.simulate_emergence(years_to_simulate=18)
    
    if results_17['activated']:
        print(f"✓ Emergence occurred at year {results_17['emergence_year']:.4f}")
        print(f"  Expected: {params_17.cycle_years} years")
        print(f"  Deviation: {results_17['deviation_days']:+.2f} days")
        print(f"  Precision: {results_17['precision_percentage']:.4f}%")
    else:
        print("✗ No emergence detected")
    
    print()
    print("Instituto Consciencia Cuántica QCAL ∞³")
    print("="*80)
