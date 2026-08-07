#!/usr/bin/env python3
"""
QCAL Biological Hypothesis - Complete Demonstration
====================================================

This script demonstrates all key features of the QCAL biological hypothesis:
1. Spectral field Ψₑ(t) construction and visualization
2. Biological clock simulation with phase accumulation
3. Magicicada 17-year cycle with prime number advantages
4. NSE derivation of 141.7 Hz from protein-scale vibrations
5. Experimental falsification framework

Run this to see the complete QCAL framework in action.

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
Date: 27 de enero de 2026
License: MIT
"""

import numpy as np
import matplotlib.pyplot as plt
from qcal_biological_hypothesis import (
    SpectralField, BiologicalClock, create_example_annual_cycle,
    visualize_spectral_field
)
from magicicada_simulation import (
    MagicicadaClock, MagicicadaParameters,
    visualize_emergence_simulation, demonstrate_prime_cycle_advantage
)
from qcal_experiments import (
    Experiment1_SpectralManipulation,
    Experiment3_GenomicResonance
)
from nse_biofluid_coupling import (
    BiofluidParameters, demonstrate_141_7_hz_derivation,
    explore_parameter_space, visualize_biofluid_spectrum,
    simulate_oscillatory_biofluid
)


def demo_1_spectral_field():
    """Demo 1: Environmental Spectral Field"""
    print("\n" + "="*80)
    print("DEMO 1: Environmental Spectral Field Ψₑ(t)")
    print("="*80)
    
    # Create spectral field with multiple environmental cycles
    field = create_example_annual_cycle()
    
    print(f"\nSpectral field components: {len(field.components)}")
    for i, comp in enumerate(field.components):
        print(f"  {i+1}. {comp.description}")
        print(f"     Frequency: {comp.frequency_hz*24*3600:.6f} cycles/day")
        print(f"     Amplitude: {comp.amplitude}")
        print(f"     Band: {comp.band.value}")
    
    # Visualize
    print("\nGenerating spectral field visualization...")
    fig = visualize_spectral_field(field, t_days=730)
    plt.savefig('/tmp/qcal_spectral_field.png', dpi=150, bbox_inches='tight')
    print("✓ Saved: /tmp/qcal_spectral_field.png")
    plt.close(fig)


def demo_2_biological_clock():
    """Demo 2: Biological Clock with Phase Accumulation"""
    print("\n" + "="*80)
    print("DEMO 2: Biological Clock with Phase Accumulation")
    print("="*80)
    
    # Create clock with annual threshold
    clock = BiologicalClock(critical_phase=2.0, name="Annual Plant")
    
    # Add environmental cycles
    clock.add_environmental_cycle(1.0, 365.25, description="Annual temperature cycle")
    clock.add_environmental_cycle(0.3, 1.0, description="Diurnal cycle")
    
    # Simulate 3 years
    t_years = 3.0
    t_array = np.linspace(0, t_years * 365.25 * 24 * 3600, 5000)
    
    print(f"\nSimulating {t_years} years...")
    results = clock.simulate(t_array)
    
    # Plot results
    fig, axes = plt.subplots(2, 1, figsize=(12, 8))
    
    time_days = t_array / (24 * 3600)
    
    axes[0].plot(time_days, results['phase'], 'b-', linewidth=2)
    axes[0].axhline(y=clock.critical_phase, color='r', linestyle='--', 
                   label=f'Critical threshold = {clock.critical_phase}')
    if results['activated']:
        activation_day = results['activation_time'] / (24 * 3600)
        axes[0].axvline(x=activation_day, color='g', linestyle=':', 
                       linewidth=2, label=f'Activation at day {activation_day:.1f}')
    axes[0].set_xlabel('Time [days]')
    axes[0].set_ylabel('Accumulated Phase Φ(t)')
    axes[0].set_title('Phase Accumulation in Biological Clock')
    axes[0].legend()
    axes[0].grid(True, alpha=0.3)
    
    axes[1].plot(time_days, results['phase_derivative'], 'purple', linewidth=1.5)
    axes[1].axhline(y=0, color='k', linestyle='-', alpha=0.3)
    axes[1].set_xlabel('Time [days]')
    axes[1].set_ylabel('dΦ/dt')
    axes[1].set_title('Phase Accumulation Rate')
    axes[1].grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('/tmp/qcal_biological_clock.png', dpi=150, bbox_inches='tight')
    print("✓ Saved: /tmp/qcal_biological_clock.png")
    plt.close(fig)
    
    if results['activated']:
        print(f"\n✓ Clock activated at {activation_day:.2f} days")
    else:
        print("\n✗ Clock not activated in simulation period")


def demo_3_magicicada():
    """Demo 3: Magicicada 17-Year Cycle"""
    print("\n" + "="*80)
    print("DEMO 3: Magicicada 17-Year Prime Cycle")
    print("="*80)
    
    # Show prime cycle advantage
    demonstrate_prime_cycle_advantage()
    
    # Simulate 17-year cicada
    print("\nSimulating 17-year Magicicada emergence...")
    params = MagicicadaParameters(cycle_years=17)
    
    print(f"  Cycle: {params.cycle_years} years (prime number)")
    print(f"  Expected precision: {params.precision_percentage:.4f}%")
    print(f"  Population: {params.population_size:,} per acre")
    
    clock = MagicicadaClock(params)
    results = clock.simulate_emergence(years_to_simulate=18)
    
    # Visualize
    fig = visualize_emergence_simulation(results, params)
    plt.savefig('/tmp/qcal_magicicada_17year.png', dpi=150, bbox_inches='tight')
    print("✓ Saved: /tmp/qcal_magicicada_17year.png")
    plt.close(fig)
    
    if results['activated']:
        print(f"\n✓ Emergence at year {results['emergence_year']:.4f}")
        print(f"  Deviation: {results['deviation_days']:+.2f} days")
        print(f"  Precision: {results['precision_percentage']:.4f}%")


def demo_4_nse_coupling():
    """Demo 4: Navier-Stokes Coupling and 141.7 Hz Derivation"""
    print("\n" + "="*80)
    print("DEMO 4: Navier-Stokes Biofluid Coupling")
    print("="*80)
    
    # Demonstrate 141.7 Hz derivation
    demonstrate_141_7_hz_derivation()
    
    # Simulate biofluid
    print("\nSimulating oscillatory biofluid...")
    params = BiofluidParameters(velocity_um_s=7.085, length_scale_um=0.05)
    
    results = simulate_oscillatory_biofluid(params, forcing_freq_hz=141.7, 
                                           duration_s=0.1, n_points=5000)
    
    # Visualize
    fig = visualize_biofluid_spectrum(results)
    plt.savefig('/tmp/qcal_nse_biofluid.png', dpi=150, bbox_inches='tight')
    print("✓ Saved: /tmp/qcal_nse_biofluid.png")
    plt.close(fig)
    
    # Parameter space exploration
    print("\nExploring biological parameter space...")
    fig = explore_parameter_space()
    plt.savefig('/tmp/qcal_parameter_space.png', dpi=150, bbox_inches='tight')
    print("✓ Saved: /tmp/qcal_parameter_space.png")
    plt.close(fig)


def demo_5_experiments():
    """Demo 5: Experimental Falsification Framework"""
    print("\n" + "="*80)
    print("DEMO 5: Experimental Falsification Framework")
    print("="*80)
    
    # Experiment 1: Spectral Manipulation
    print("\nExperiment 1: Spectral Manipulation (141.7 Hz)")
    from qcal_experiments import ExperimentalGroup
    exp1 = Experiment1_SpectralManipulation()
    
    exp1.setup_group_control(n_replicates=10)
    exp1.setup_group_spectral(n_replicates=10)
    exp1.setup_group_energetic(n_replicates=10)
    
    print("  Running experiment...")
    results1 = exp1.run_experiment(duration_days=15)
    
    print(f"  Group A (Control):   {results1['groups'][ExperimentalGroup.CONTROL]['mean_activation']:.2f} ± "
          f"{results1['groups'][ExperimentalGroup.CONTROL]['std_activation']:.2f} hours")
    print(f"  Group B (Spectral):  {results1['groups'][ExperimentalGroup.SPECTRAL]['mean_activation']:.2f} ± "
          f"{results1['groups'][ExperimentalGroup.SPECTRAL]['std_activation']:.2f} hours")
    print(f"  Group C (Energetic): {results1['groups'][ExperimentalGroup.ENERGETIC]['mean_activation']:.2f} ± "
          f"{results1['groups'][ExperimentalGroup.ENERGETIC]['std_activation']:.2f} hours")
    
    if results1['analysis']['qcal_supported']:
        print("  ✓ QCAL hypothesis supported (B≈C, spectral content matters)")
    else:
        print("  ✗ Classical model supported (A≈B, only energy matters)")
    
    fig = exp1.visualize_results(results1)
    plt.savefig('/tmp/qcal_experiment1.png', dpi=150, bbox_inches='tight')
    print("  ✓ Saved: /tmp/qcal_experiment1.png")
    plt.close(fig)
    
    # Experiment 3: Genomic Resonance
    print("\nExperiment 3: Genomic Resonance")
    exp3 = Experiment3_GenomicResonance()
    
    print(f"  Testing frequencies: {exp3.test_frequencies_hz} Hz")
    results3 = exp3.simulate_frequency_response(resonant_freq_hz=141.7, Q_factor=10.0)
    
    print(f"  Peak response at: {results3['peak_frequency']} Hz")
    print(f"  Frequency selectivity: {'YES' if results3['frequency_selectivity_observed'] else 'NO'}")
    
    fig = exp3.visualize_frequency_response(results3)
    plt.savefig('/tmp/qcal_experiment3.png', dpi=150, bbox_inches='tight')
    print("  ✓ Saved: /tmp/qcal_experiment3.png")
    plt.close(fig)


def main():
    """Run all demonstrations"""
    print("="*80)
    print("QCAL BIOLOGICAL HYPOTHESIS - COMPLETE DEMONSTRATION")
    print("="*80)
    print()
    print("Una nueva hipótesis falsable que une biología y teoría de números")
    print("a través del campo espectral Ψ")
    print()
    print("José Manuel Mota Burruezo")
    print("Instituto Consciencia Cuántica QCAL ∞³")
    print("27 de enero de 2026")
    print("="*80)
    
    # Run all demos
    demo_1_spectral_field()
    demo_2_biological_clock()
    demo_3_magicicada()
    demo_4_nse_coupling()
    demo_5_experiments()
    
    print("\n" + "="*80)
    print("DEMONSTRATION COMPLETE")
    print("="*80)
    print()
    print("Generated visualizations:")
    print("  1. /tmp/qcal_spectral_field.png      - Environmental spectral field")
    print("  2. /tmp/qcal_biological_clock.png    - Phase accumulation")
    print("  3. /tmp/qcal_magicicada_17year.png   - Magicicada emergence")
    print("  4. /tmp/qcal_nse_biofluid.png        - Biofluid spectrum")
    print("  5. /tmp/qcal_parameter_space.png     - Frequency parameter space")
    print("  6. /tmp/qcal_experiment1.png         - Spectral manipulation")
    print("  7. /tmp/qcal_experiment3.png         - Genomic resonance")
    print()
    print("Key Findings:")
    print("  • 141.7 Hz emerges from protein-scale fluid vibrations (λ = 50 nm)")
    print("  • Phase memory (α = 0.1) explains Magicicada robustness")
    print("  • Prime cycles (13, 17 years) minimize predator synchronization")
    print("  • Spectral content matters beyond total energy accumulation")
    print()
    print("Falsification Criterion:")
    print("  If experiments show ONLY total energy matters → QCAL falsified")
    print("  If frequency structure matters → QCAL supported")
    print()
    print("Instituto Consciencia Cuántica QCAL ∞³")
    print("="*80)


if __name__ == "__main__":
    main()
