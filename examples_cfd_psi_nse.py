#!/usr/bin/env python3
"""
Practical CFD Examples Using Ψ-NSE
===================================

This script provides practical examples for CFD engineers to get started
with the Ψ-NSE stabilized solver.
"""

import numpy as np
from cfd_psi_nse_solver import PsiNSECFDSolver, CFDProblem
import matplotlib.pyplot as plt


def example_1_basic_usage():
    """
    Example 1: Basic usage of Ψ-NSE CFD solver
    
    This is the simplest way to use the solver.
    """
    print("\n" + "="*70)
    print("EXAMPLE 1: Basic Usage")
    print("="*70)
    
    # Define problem
    problem = CFDProblem(
        domain_size=(1.0, 1.0, 1.0),
        resolution=(32, 32, 32),
        viscosity=1e-3,
        initial_condition='taylor_green_vortex'
    )
    
    # Create solver with stabilization
    solver = PsiNSECFDSolver(problem, enable_stabilization=True)
    
    # Run simulation
    print("\nRunning simulation...")
    results = solver.solve(t_final=5.0, dt_output=0.5)
    
    # Check results
    if results['success']:
        print("✓ Simulation completed successfully!")
        print(f"  Final energy: {results['energy'][-1]:.6f}")
        print(f"  Max vorticity: {max(results['max_vorticity']):.2e}")
    else:
        print("⚠ Blow-up detected")
    
    # Plot results
    solver.plot_results('example1_results.png')
    print("✓ Results saved to example1_results.png")
    
    return results


def example_2_low_viscosity_challenge():
    """
    Example 2: Challenging case with low viscosity
    
    Demonstrates how Ψ-NSE handles flows that would blow up in classical NSE.
    """
    print("\n" + "="*70)
    print("EXAMPLE 2: Low Viscosity Challenge")
    print("="*70)
    print("\nThis example shows Ψ-NSE handling a challenging low-viscosity case")
    print("that would typically cause blow-up in classical NSE.\n")
    
    # Low viscosity problem
    problem = CFDProblem(
        domain_size=(1.0, 1.0, 1.0),
        resolution=(48, 48, 48),
        viscosity=1e-4,  # Very low viscosity - challenging!
        initial_condition='taylor_green_vortex'
    )
    
    print("Problem parameters:")
    print(f"  Viscosity: ν = {problem.viscosity:.1e} (very low)")
    print(f"  Reynolds number: Re ≈ {1.0/problem.viscosity:.1e}")
    
    # Create solver
    solver = PsiNSECFDSolver(problem, enable_stabilization=True)
    
    # Run simulation
    results = solver.solve(t_final=3.0)
    
    # Analyze stabilization
    print("\nStabilization analysis:")
    print(f"  Max vorticity: {max(results['max_vorticity']):.2e}")
    print(f"  Average coupling strength: {np.mean(results['stability_indicator']):.2e}")
    print(f"  Natural frequency active: f₀ = {solver.F0_NATURAL:.4f} Hz")
    
    solver.plot_results('example2_low_viscosity.png')
    
    return results


def example_3_comparison_nse_vs_psi_nse():
    """
    Example 3: Direct comparison of NSE vs Ψ-NSE
    
    Shows the difference between classical and stabilized equations.
    """
    print("\n" + "="*70)
    print("EXAMPLE 3: NSE vs Ψ-NSE Comparison")
    print("="*70)
    print("\nComparing classical NSE with Ψ-NSE on the same problem...")
    
    # Common problem
    problem = CFDProblem(
        domain_size=(1.0, 1.0, 1.0),
        resolution=(32, 32, 32),
        viscosity=5e-4,
        initial_condition='taylor_green_vortex'
    )
    
    # Classical NSE
    print("\n[1/2] Running classical NSE...")
    solver_classical = PsiNSECFDSolver(problem, enable_stabilization=False)
    results_classical = solver_classical.solve(t_final=2.0)
    
    # Ψ-NSE
    print("\n[2/2] Running Ψ-NSE...")
    solver_psi = PsiNSECFDSolver(problem, enable_stabilization=True)
    results_psi = solver_psi.solve(t_final=2.0)
    
    # Comparison plot
    fig, axes = plt.subplots(2, 2, figsize=(12, 10))
    
    # Max vorticity
    axes[0, 0].semilogy(results_classical['time'], results_classical['max_vorticity'],
                        'r-', label='Classical NSE', linewidth=2)
    axes[0, 0].semilogy(results_psi['time'], results_psi['max_vorticity'],
                        'g-', label='Ψ-NSE', linewidth=2)
    axes[0, 0].set_xlabel('Time (s)')
    axes[0, 0].set_ylabel('Max Vorticity (log)')
    axes[0, 0].set_title('Vorticity Growth Comparison')
    axes[0, 0].legend()
    axes[0, 0].grid(True, alpha=0.3)
    
    # Energy
    axes[0, 1].plot(results_classical['time'], results_classical['energy'],
                    'r-', label='Classical NSE', linewidth=2)
    axes[0, 1].plot(results_psi['time'], results_psi['energy'],
                    'g-', label='Ψ-NSE', linewidth=2)
    axes[0, 1].set_xlabel('Time (s)')
    axes[0, 1].set_ylabel('Kinetic Energy')
    axes[0, 1].set_title('Energy Evolution')
    axes[0, 1].legend()
    axes[0, 1].grid(True, alpha=0.3)
    
    # Enstrophy
    axes[1, 0].semilogy(results_classical['time'], results_classical['enstrophy'],
                        'r-', label='Classical NSE', linewidth=2)
    axes[1, 0].semilogy(results_psi['time'], results_psi['enstrophy'],
                        'g-', label='Ψ-NSE', linewidth=2)
    axes[1, 0].set_xlabel('Time (s)')
    axes[1, 0].set_ylabel('Enstrophy (log)')
    axes[1, 0].set_title('Enstrophy Evolution')
    axes[1, 0].legend()
    axes[1, 0].grid(True, alpha=0.3)
    
    # Stability indicator
    axes[1, 1].plot(results_psi['time'], results_psi['stability_indicator'],
                    'm-', linewidth=2)
    axes[1, 1].set_xlabel('Time (s)')
    axes[1, 1].set_ylabel('Stability Indicator')
    axes[1, 1].set_title('Ψ-NSE Stabilization Strength')
    axes[1, 1].grid(True, alpha=0.3)
    
    fig.suptitle('Classical NSE vs Ψ-NSE: Stabilization Effect', fontsize=14, fontweight='bold')
    plt.tight_layout()
    plt.savefig('example3_comparison.png', dpi=300)
    print("\n✓ Comparison plot saved to example3_comparison.png")
    
    # Summary
    print("\nComparison Summary:")
    print("-" * 40)
    print(f"Classical NSE:")
    print(f"  Max vorticity: {max(results_classical['max_vorticity']):.2e}")
    print(f"  Blow-up: {'YES ⚠' if results_classical['blowup_detected'] else 'NO ✓'}")
    print(f"\nΨ-NSE:")
    print(f"  Max vorticity: {max(results_psi['max_vorticity']):.2e}")
    print(f"  Blow-up: {'YES ⚠' if results_psi['blowup_detected'] else 'NO ✓'}")
    
    reduction = (1 - max(results_psi['max_vorticity']) / max(results_classical['max_vorticity'])) * 100
    print(f"\nVorticity reduction by Ψ-NSE: {reduction:.1f}%")
    
    return results_classical, results_psi


def example_4_shear_layer_instability():
    """
    Example 4: Kelvin-Helmholtz shear layer instability
    
    Tests stabilization on a notoriously unstable flow configuration.
    """
    print("\n" + "="*70)
    print("EXAMPLE 4: Shear Layer Instability (Kelvin-Helmholtz)")
    print("="*70)
    print("\nShear layers are prone to rapid instabilities and blow-up.")
    print("This example shows how Ψ-NSE handles such challenging cases.\n")
    
    # Shear layer problem
    problem = CFDProblem(
        domain_size=(2.0, 2.0, 1.0),
        resolution=(64, 64, 32),
        viscosity=1e-4,
        initial_condition='shear_layer'
    )
    
    print("Problem parameters:")
    print(f"  Domain: {problem.domain_size[0]}×{problem.domain_size[1]}×{problem.domain_size[2]} m³")
    print(f"  Resolution: {problem.resolution[0]}×{problem.resolution[1]}×{problem.resolution[2]}")
    print(f"  Viscosity: ν = {problem.viscosity:.1e}")
    
    # Run with stabilization
    solver = PsiNSECFDSolver(problem, enable_stabilization=True)
    results = solver.solve(t_final=5.0, dt_output=0.5)
    
    # Results
    print("\nResults:")
    if results['success']:
        print("✓ Simulation completed successfully despite shear instability")
        print(f"  Max vorticity: {max(results['max_vorticity']):.2e}")
        print(f"  Final time reached: {results['time'][-1]:.2f} s")
    else:
        print("⚠ Instability too strong even with stabilization")
    
    solver.plot_results('example4_shear_layer.png')
    
    return results


def example_5_parameter_study():
    """
    Example 5: Parameter study - varying viscosity
    
    Shows how Ψ-NSE performs across different flow regimes.
    """
    print("\n" + "="*70)
    print("EXAMPLE 5: Parameter Study - Varying Viscosity")
    print("="*70)
    print("\nStudying how Ψ-NSE stabilization performs at different viscosities...")
    
    viscosities = [1e-2, 5e-3, 1e-3, 5e-4, 1e-4]
    max_vorticities_classical = []
    max_vorticities_psi = []
    blowup_classical = []
    blowup_psi = []
    
    for i, nu in enumerate(viscosities):
        print(f"\n[{i+1}/{len(viscosities)}] Testing ν = {nu:.1e}...")
        
        problem = CFDProblem(
            resolution=(32, 32, 32),
            viscosity=nu,
            initial_condition='taylor_green_vortex'
        )
        
        # Classical NSE
        solver_classical = PsiNSECFDSolver(problem, enable_stabilization=False)
        results_classical = solver_classical.solve(t_final=1.0, dt_output=0.2)
        max_vorticities_classical.append(max(results_classical['max_vorticity']))
        blowup_classical.append(results_classical['blowup_detected'])
        
        # Ψ-NSE
        solver_psi = PsiNSECFDSolver(problem, enable_stabilization=True)
        results_psi = solver_psi.solve(t_final=1.0, dt_output=0.2)
        max_vorticities_psi.append(max(results_psi['max_vorticity']))
        blowup_psi.append(results_psi['blowup_detected'])
    
    # Plot results
    fig, ax = plt.subplots(figsize=(10, 6))
    
    reynolds = [1.0/nu for nu in viscosities]
    
    ax.loglog(reynolds, max_vorticities_classical, 'ro-', label='Classical NSE',
              markersize=8, linewidth=2)
    ax.loglog(reynolds, max_vorticities_psi, 'go-', label='Ψ-NSE',
              markersize=8, linewidth=2)
    
    # Mark blow-ups
    for i, (re, blowup) in enumerate(zip(reynolds, blowup_classical)):
        if blowup:
            ax.plot(re, max_vorticities_classical[i], 'rx', markersize=15, markeredgewidth=3)
    
    ax.set_xlabel('Reynolds Number', fontsize=12)
    ax.set_ylabel('Maximum Vorticity', fontsize=12)
    ax.set_title('Stabilization Effect vs Reynolds Number', fontsize=14, fontweight='bold')
    ax.legend(fontsize=11)
    ax.grid(True, alpha=0.3, which='both')
    
    plt.tight_layout()
    plt.savefig('example5_parameter_study.png', dpi=300)
    print("\n✓ Parameter study plot saved to example5_parameter_study.png")
    
    # Summary table
    print("\nResults Summary:")
    print("-" * 70)
    print(f"{'ν (m²/s)':<12} {'Re':<10} {'Classical':<20} {'Ψ-NSE':<20}")
    print("-" * 70)
    for i, nu in enumerate(viscosities):
        re = 1.0/nu
        classical_str = f"{max_vorticities_classical[i]:.2e}" + (" ⚠" if blowup_classical[i] else " ✓")
        psi_str = f"{max_vorticities_psi[i]:.2e}" + (" ⚠" if blowup_psi[i] else " ✓")
        print(f"{nu:<12.1e} {re:<10.1e} {classical_str:<20} {psi_str:<20}")
    print("-" * 70)
    
    return viscosities, max_vorticities_classical, max_vorticities_psi


def main():
    """Run all examples."""
    print("\n" + "="*70)
    print("Ψ-NSE CFD SOLVER - PRACTICAL EXAMPLES")
    print("="*70)
    print("\nThese examples demonstrate how to use the Ψ-NSE stabilized solver")
    print("for practical CFD applications where numerical blow-up is a problem.")
    print("\nPress Enter to continue through examples, or Ctrl+C to exit.")
    print("="*70)
    
    examples = [
        ("Basic Usage", example_1_basic_usage),
        ("Low Viscosity Challenge", example_2_low_viscosity_challenge),
        ("NSE vs Ψ-NSE Comparison", example_3_comparison_nse_vs_psi_nse),
        ("Shear Layer Instability", example_4_shear_layer_instability),
        ("Parameter Study", example_5_parameter_study),
    ]
    
    for i, (name, func) in enumerate(examples, 1):
        try:
            input(f"\n[Press Enter to run Example {i}: {name}]")
            func()
        except KeyboardInterrupt:
            print("\n\nExamples interrupted by user.")
            break
        except Exception as e:
            print(f"\n⚠ Error in example: {e}")
            import traceback
            traceback.print_exc()
    
    print("\n" + "="*70)
    print("EXAMPLES COMPLETED")
    print("="*70)
    print("\nGenerated files:")
    print("  - example1_results.png")
    print("  - example2_low_viscosity.png")
    print("  - example3_comparison.png")
    print("  - example4_shear_layer.png")
    print("  - example5_parameter_study.png")
    print("\nFor more information, see CFD_APPLICATION_README.md")
    print("="*70 + "\n")


if __name__ == "__main__":
    main()
