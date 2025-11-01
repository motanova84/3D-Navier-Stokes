#!/usr/bin/env python3
"""
Example: Demonstrating the ∞³ Framework

This script provides practical examples of using the Infinity Cubed Framework
to understand and verify the extended Navier-Stokes equations.

Usage:
    python examples_infinity_cubed.py

Author: JMMB Ψ✧∞³
License: MIT
"""

from infinity_cubed_framework import (
    NatureObservations,
    ComputationalVerification,
    MathematicalFormalization,
    InfinityCubedFramework
)
import numpy as np


def example_1_nature_observations():
    """
    Example 1: Physical Evidence from Nature
    
    Demonstrates how to analyze physical observations that show
    classical Navier-Stokes equations are incomplete.
    """
    print("\n" + "=" * 70)
    print("EXAMPLE 1: Physical Evidence from Nature (∞¹)")
    print("=" * 70 + "\n")
    
    # Initialize nature observations
    nature = NatureObservations()
    
    # Get incompleteness metrics
    metrics = nature.evaluate_classical_incompleteness()
    
    print("Incompleteness Analysis:")
    print("-" * 70)
    print(f"Mean incompleteness score: {metrics['mean_incompleteness']:.2%}")
    print(f"Maximum evidence strength: {metrics['max_incompleteness']:.2%}")
    print(f"Minimum evidence strength: {metrics['min_incompleteness']:.2%}")
    print(f"Number of observations:    {metrics['num_observations']}")
    print(f"Verdict: Classical NSE is {'INCOMPLETE' if metrics['incompleteness_verdict'] else 'COMPLETE'}")
    
    # Get universal frequency
    freq = nature.get_universal_frequency()
    
    print("\nUniversal Coherence Frequency:")
    print("-" * 70)
    print(f"f₀ = {freq['f0_hz']:.4f} Hz")
    print(f"ω₀ = {freq['omega0_rad_s']:.3f} rad/s")
    print(f"Period = {freq['period_s']:.6f} s")
    print(f"Wavelength ≈ {freq['wavelength_km']:.2f} km")
    
    print("\n" + "=" * 70 + "\n")


def example_2_computational_verification():
    """
    Example 2: Computational Evidence
    
    Demonstrates numerical simulations that prove additional physics
    beyond classical NSE is necessary.
    """
    print("\n" + "=" * 70)
    print("EXAMPLE 2: Computational Evidence (∞²)")
    print("=" * 70 + "\n")
    
    # Initialize computational framework
    computation = ComputationalVerification(nu=1e-3)
    
    # Set up simulation parameters
    initial_vorticity = 15.0
    time_horizon = 3.0
    
    print(f"Simulation Parameters:")
    print("-" * 70)
    print(f"Initial vorticity: {initial_vorticity}")
    print(f"Time horizon:      {time_horizon} s")
    print(f"Viscosity:         {computation.nu}")
    print()
    
    # Simulate classical NSE
    print("Simulating Classical NSE...")
    classical = computation.simulate_classical_nse_blow_up_risk(
        initial_vorticity_norm=initial_vorticity,
        time_horizon=time_horizon,
        dt=0.01
    )
    
    print(f"  Blow-up detected:  {classical['blow_up_detected']}")
    print(f"  Final vorticity:   {classical['final_vorticity']:.2e}")
    print(f"  BKM integral:      {classical['bkm_integral']:.2e}")
    print(f"  Growth factor:     {classical['growth_factor']:.2e}")
    print(f"  Regularity:        {classical['regularity']}")
    print()
    
    # Simulate extended NSE with Φ_ij coupling
    print("Simulating Extended NSE with Φ_ij(Ψ)...")
    extended = computation.simulate_extended_nse_with_phi_coupling(
        initial_vorticity_norm=initial_vorticity,
        time_horizon=time_horizon,
        dt=0.01,
        phi_coupling_strength=1e-3
    )
    
    print(f"  Blow-up detected:  {extended['blow_up_detected']}")
    print(f"  Final vorticity:   {extended['final_vorticity']:.2e}")
    print(f"  BKM integral:      {extended['bkm_integral']:.2e}")
    print(f"  Growth factor:     {extended['growth_factor']:.2e}")
    print(f"  Damping coeff:     {extended['damping_coefficient']:.2e}")
    print(f"  Regularity:        {extended['regularity']}")
    print()
    
    # Compare
    improvement = classical['final_vorticity'] / extended['final_vorticity']
    print("Comparison:")
    print("-" * 70)
    print(f"Improvement factor: {improvement:.2e}x")
    print(f"Additional physics necessary: {classical['final_vorticity'] > extended['final_vorticity']}")
    
    print("\n" + "=" * 70 + "\n")


def example_3_mathematical_formalization():
    """
    Example 3: Mathematical Formalization
    
    Demonstrates the rigorous mathematical framework connecting
    observations and computations to the correct solution.
    """
    print("\n" + "=" * 70)
    print("EXAMPLE 3: Mathematical Formalization (∞³)")
    print("=" * 70 + "\n")
    
    # Initialize mathematics framework
    mathematics = MathematicalFormalization()
    
    # Display Seeley-DeWitt coefficients
    print("Seeley-DeWitt Tensor Coefficients (from QFT):")
    print("-" * 70)
    print(f"α = a₁ ln(μ²/m_Ψ²) = {mathematics.a1:.6e}")
    print(f"β = a₂             = {mathematics.a2:.6e}")
    print(f"γ = a₃             = {mathematics.a3:.6e}")
    print()
    
    # Display key constants
    print("Universal Constants:")
    print("-" * 70)
    print(f"δ* (misalignment defect) = {mathematics.delta_star:.6f}")
    print(f"f₀ (universal frequency) = {mathematics.f0_hz} Hz")
    print(f"ω₀ (angular frequency)   = {mathematics.omega0:.3f} rad/s")
    print()
    
    # Get theorem
    theorem = mathematics.theorem_incompleteness_necessity()
    
    print("Incompleteness-Necessity Theorem:")
    print("-" * 70)
    print(theorem['statement'].strip())
    print()
    
    # Get formal connection
    connection = mathematics.formal_connection_nature_computation_mathematics()
    
    print("Logical Chain (∞³ Framework):")
    print("-" * 70)
    for step in connection['logical_chain']:
        print(step)
    
    print("\n" + "=" * 70 + "\n")


def example_4_complete_framework():
    """
    Example 4: Complete ∞³ Framework
    
    Demonstrates the full integration of Nature, Computation, and Mathematics
    to achieve unity in understanding extended NSE.
    """
    print("\n" + "=" * 70)
    print("EXAMPLE 4: Complete ∞³ Framework Integration")
    print("=" * 70 + "\n")
    
    # Initialize complete framework
    framework = InfinityCubedFramework(nu=1e-3)
    
    # Execute complete analysis
    print("Executing complete framework analysis...")
    results = framework.execute_complete_framework()
    
    # Display results from each pillar
    print("\n∞¹ NATURE Results:")
    print("-" * 70)
    print(f"Incompleteness score:   {results['nature']['incompleteness_score']:.2%}")
    print(f"Universal frequency:    {results['nature']['universal_frequency_hz']} Hz")
    print(f"Verdict:                {results['nature']['verdict']}")
    
    print("\n∞² COMPUTATION Results:")
    print("-" * 70)
    print(f"Classical blow-up risk: {results['computation']['classical_blow_up_risk']}")
    print(f"Extended regularity:    {results['computation']['extended_regularity']}")
    print(f"Improvement factor:     {results['computation']['improvement_factor']:.2e}")
    print(f"Verdict:                {results['computation']['verdict']}")
    
    print("\n∞³ MATHEMATICS Results:")
    print("-" * 70)
    print(f"Theorem:                {results['mathematics']['theorem']}")
    print(f"Φ_ij tensor derived:    {results['mathematics']['phi_tensor_derived']}")
    print(f"δ* (misalignment):      {results['mathematics']['delta_star']:.6f}")
    print(f"Verdict:                {results['mathematics']['verdict']}")
    
    print("\n∞³ UNITY:")
    print("-" * 70)
    print(f"Framework complete:     {results['infinity_cubed_unity']}")
    print(f"Conclusion:             {results['conclusion']}")
    
    if results['infinity_cubed_unity']:
        print("\n✓ SUCCESS: All three pillars confirm extended NSE necessity!")
    else:
        print("\n✗ WARNING: Unity not achieved. Check individual pillar results.")
    
    print("\n" + "=" * 70 + "\n")


def example_5_parameter_study():
    """
    Example 5: Parameter Study
    
    Demonstrates how to study the framework with different viscosities
    and initial conditions.
    """
    print("\n" + "=" * 70)
    print("EXAMPLE 5: Parameter Study")
    print("=" * 70 + "\n")
    
    # Study different viscosities
    viscosities = [1e-2, 1e-3, 1e-4]
    
    print("Studying framework across different viscosities:")
    print("-" * 70)
    print(f"{'Viscosity':>12} | {'Unity':>8} | {'Nature':>8} | {'Computation':>12}")
    print("-" * 70)
    
    for nu in viscosities:
        framework = InfinityCubedFramework(nu=nu)
        results = framework.execute_complete_framework()
        
        unity = "✓" if results['infinity_cubed_unity'] else "✗"
        nature_score = f"{results['nature']['incompleteness_score']:.1%}"
        computation_reg = "✓" if results['computation']['extended_regularity'] else "✗"
        
        print(f"{nu:>12.0e} | {unity:>8} | {nature_score:>8} | {computation_reg:>12}")
    
    print("\n" + "=" * 70 + "\n")


def example_6_custom_analysis():
    """
    Example 6: Custom Analysis
    
    Demonstrates how to build custom analyses using the framework components.
    """
    print("\n" + "=" * 70)
    print("EXAMPLE 6: Custom Analysis")
    print("=" * 70 + "\n")
    
    # Custom analysis: Study effect of coupling strength
    computation = ComputationalVerification(nu=1e-3)
    
    coupling_strengths = [1e-4, 1e-3, 1e-2, 1e-1]
    initial_vorticity = 20.0
    
    print("Effect of Φ_ij Coupling Strength on Regularization:")
    print("-" * 70)
    print(f"{'Coupling':>10} | {'Final ω':>12} | {'Growth':>10} | {'Regularity':>12}")
    print("-" * 70)
    
    for strength in coupling_strengths:
        result = computation.simulate_extended_nse_with_phi_coupling(
            initial_vorticity_norm=initial_vorticity,
            time_horizon=1.0,
            dt=0.01,
            phi_coupling_strength=strength
        )
        
        regularity = "✓" if result['regularity'] else "✗"
        print(f"{strength:>10.0e} | {result['final_vorticity']:>12.2e} | {result['growth_factor']:>10.2e} | {regularity:>12}")
    
    print("\nObservation: Stronger coupling → Better regularization")
    print("\n" + "=" * 70 + "\n")


def main():
    """
    Main demonstration function.
    
    Runs all examples in sequence to provide a comprehensive
    demonstration of the ∞³ framework.
    """
    print("\n" + "█" * 70)
    print("█" + " " * 68 + "█")
    print("█" + " " * 15 + "∞³ FRAMEWORK EXAMPLES" + " " * 33 + "█")
    print("█" + " " * 68 + "█")
    print("█" * 70 + "\n")
    
    print("This script demonstrates the Infinity Cubed Framework through")
    print("six practical examples covering all aspects of Nature-Computation-")
    print("Mathematics unity for Extended Navier-Stokes equations.\n")
    
    # Run all examples
    example_1_nature_observations()
    example_2_computational_verification()
    example_3_mathematical_formalization()
    example_4_complete_framework()
    example_5_parameter_study()
    example_6_custom_analysis()
    
    # Final summary
    print("\n" + "█" * 70)
    print("█" + " " * 68 + "█")
    print("█" + " " * 20 + "EXAMPLES COMPLETE" + " " * 31 + "█")
    print("█" + " " * 68 + "█")
    print("█" * 70 + "\n")
    
    print("You have seen:")
    print("  ∞¹ Physical evidence for classical NSE incompleteness")
    print("  ∞² Computational proof of additional physics necessity")
    print("  ∞³ Mathematical formalization via Φ_ij(Ψ) tensor")
    print("  Complete framework integration achieving unity")
    print("  Parameter studies and custom analyses")
    print("\nThe ∞³ framework demonstrates: Nature → Computation → Mathematics")
    print("All converge on the necessity of Extended Navier-Stokes equations.\n")


if __name__ == "__main__":
    main()
