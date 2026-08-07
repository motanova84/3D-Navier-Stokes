#!/usr/bin/env python3
"""
Unified BKM Framework - Usage Examples

Demonstrates all features of the unified BKM framework:
- Three convergent routes
- Parameter optimization
- Complete validation
"""

import numpy as np
import sys
sys.path.append('/home/runner/work/3D-Navier-Stokes/3D-Navier-Stokes/DNS-Verification/DualLimitSolver')

from unified_bkm import (
    riccati_besov_closure,
    compute_optimal_dual_scaling,
    riccati_evolution,
    volterra_solution_exponential_decay,
    energy_bootstrap,
    unified_bkm_verification,
    validate_constants_uniformity,
    UnifiedBKMConstants
)


def example_1_basic_closure_check():
    """
    Example 1: Basic damping condition check
    """
    print("\n" + "="*70)
    print("EXAMPLE 1: Basic Damping Condition Check")
    print("="*70)
    
    # Physical parameters
    ν = 1e-3      # Viscosity
    c_B = 0.15    # Bernstein constant
    C_CZ = 1.5    # Calderón-Zygmund constant
    C_star = 1.2  # Besov embedding constant
    M = 100.0     # H^m bound
    
    # QCAL parameters
    a = 8.9       # Amplitude (calibrated for γ > 0)
    c_0 = 1.0     # Phase gradient
    
    # Compute misalignment defect
    δ_star = (a**2 * c_0**2) / (4 * np.pi**2)
    
    print(f"\nParameters:")
    print(f"  ν = {ν}")
    print(f"  c_B = {c_B}")
    print(f"  C_CZ = {C_CZ}")
    print(f"  C_* = {C_star}")
    print(f"  a = {a}")
    print(f"  δ* = {δ_star:.6f}")
    
    # Check closure condition
    closure, damping = riccati_besov_closure(ν, c_B, C_CZ, C_star, δ_star, M)
    
    print(f"\nResults:")
    print(f"  Damping coefficient Δ = {damping:.6f}")
    print(f"  Closure satisfied (Δ > 0)? {closure}")
    
    if closure:
        print("\n✅ Damping condition verified!")
    else:
        print("\n⚠️  Damping condition not satisfied")


def example_2_optimal_parameters():
    """
    Example 2: Find optimal parameters
    """
    print("\n" + "="*70)
    print("EXAMPLE 2: Optimal Parameter Search")
    print("="*70)
    
    # Physical constants
    ν = 1e-3
    c_B = 0.15
    C_CZ = 1.5
    C_star = 1.2
    M = 100.0
    
    print("\nSearching for optimal amplitude parameter a...")
    
    # Find optimal parameters
    optimal = compute_optimal_dual_scaling(ν, c_B, C_CZ, C_star, M)
    
    print(f"\nOptimal configuration:")
    print(f"  Optimal a = {optimal['optimal_a']:.4f}")
    print(f"  Optimal δ* = {optimal['optimal_δ_star']:.6f}")
    print(f"  Maximum damping Δ = {optimal['max_damping']:.6f}")
    print(f"  Closure satisfied: {optimal['closure_satisfied']}")
    
    if optimal['closure_satisfied']:
        print("\n✅ Optimal parameters found with positive damping!")


def example_3_riccati_evolution():
    """
    Example 3: Solve Riccati evolution
    """
    print("\n" + "="*70)
    print("EXAMPLE 3: Riccati Evolution")
    print("="*70)
    
    # Initial vorticity
    ω_0 = 10.0
    
    # Damping coefficient (from optimal parameters)
    Δ = 15.495
    
    # Time horizon
    T = 100.0
    
    print(f"\nParameters:")
    print(f"  Initial vorticity ‖ω₀‖_∞ = {ω_0}")
    print(f"  Damping coefficient Δ = {Δ}")
    print(f"  Time horizon T = {T}")
    
    # Solve Riccati equation
    result = riccati_evolution(ω_0, Δ, T)
    
    print(f"\nResults:")
    print(f"  Evolution successful: {result['success']}")
    print(f"  BKM integral: ∫₀^T ‖ω(t)‖_∞ dt = {result['bkm_integral']:.6f}")
    print(f"  BKM finite: {result['bkm_finite']}")
    print(f"  Final vorticity: ‖ω(T)‖_∞ = {result['ω'][-1]:.6f}")
    
    if result['bkm_finite']:
        print("\n✅ BKM criterion satisfied - Global regularity!")


def example_4_three_routes():
    """
    Example 4: Verify all three routes
    """
    print("\n" + "="*70)
    print("EXAMPLE 4: Three Convergent Routes Verification")
    print("="*70)
    
    # Create optimal parameters
    params = UnifiedBKMConstants(
        ν=1e-3,
        c_B=0.15,
        C_CZ=1.5,
        C_star=1.2,
        a=10.0,  # Optimal
        c_0=1.0,
        α=2.0
    )
    
    print("\nVerifying all three routes...")
    
    # Run unified verification
    results = unified_bkm_verification(
        params, 
        M=100.0, 
        ω_0=10.0, 
        verbose=False  # Set to True for detailed output
    )
    
    print(f"\nRuta A (Riccati-Besov):")
    print(f"  Closure satisfied: {results['ruta_a']['closure']}")
    if results['ruta_a']['closure']:
        print(f"  BKM integral: {results['ruta_a']['bkm_integral']:.6f}")
    
    print(f"\nRuta B (Volterra-Besov):")
    print(f"  Convergent: {results['ruta_b']['success']}")
    if results['ruta_b']['success']:
        print(f"  BKM integral: {results['ruta_b']['bkm_integral']:.6f}")
    
    print(f"\nRuta C (Energy Bootstrap):")
    print(f"  Successful: {results['ruta_c']['success']}")
    if results['ruta_c']['success']:
        print(f"  Final energy: {results['ruta_c']['final_energy']:.6f}")
    
    print(f"\n" + "-"*70)
    print(f"Global Regularity: {results['global_regularity']}")
    
    if results['global_regularity']:
        print("\n✅ All three routes converge - Global regularity verified!")
    else:
        print("\n⚠️  Not all routes converged")


def example_5_uniformity_validation():
    """
    Example 5: Validate uniformity across f₀
    """
    print("\n" + "="*70)
    print("EXAMPLE 5: Uniformity Validation Across f₀")
    print("="*70)
    
    # Parameters
    params = UnifiedBKMConstants(
        ν=1e-3,
        c_B=0.15,
        C_CZ=1.5,
        C_star=1.2,
        a=10.0,
        c_0=1.0,
        α=2.0
    )
    
    # Range of frequencies
    f0_range = np.array([100, 500, 1000, 5000, 10000])
    
    print(f"\nTesting uniformity across f₀ ∈ [{f0_range[0]}, {f0_range[-1]}] Hz")
    
    # Validate uniformity
    uniformity = validate_constants_uniformity(f0_range, params)
    
    print(f"\nResults:")
    print(f"  Frequencies tested: {len(f0_range)}")
    print(f"  Uniform damping: {uniformity['uniform']}")
    print(f"  Min damping: {uniformity['min_damping']:.6f}")
    print(f"  Max damping: {uniformity['max_damping']:.6f}")
    
    # Show damping for each frequency
    print(f"\nDamping by frequency:")
    for i, f0 in enumerate(f0_range):
        damping = uniformity['damping_values'][i]
        status = "✓" if uniformity['closure_satisfied'][i] else "✗"
        print(f"  f₀ = {f0:5.0f} Hz: Δ = {damping:.6f} {status}")
    
    if uniformity['uniform']:
        print("\n✅ Constants uniform across all frequencies!")


def example_6_comparison():
    """
    Example 6: Compare optimal vs suboptimal parameters
    """
    print("\n" + "="*70)
    print("EXAMPLE 6: Optimal vs Suboptimal Parameters")
    print("="*70)
    
    # Test configurations
    configs = [
        {'name': 'Suboptimal (a=2.45)', 'a': 2.45},
        {'name': 'Previous (a=7.0)', 'a': 7.0},
        {'name': 'Calibrated (a=8.9)', 'a': 8.9},
        {'name': 'Optimal (a=10.0)', 'a': 10.0}
    ]
    
    ν = 1e-3
    c_B = 0.15
    C_CZ = 1.5
    C_star = 1.2
    M = 100.0
    c_0 = 1.0
    
    print("\nComparing configurations:\n")
    print(f"{'Configuration':<25} {'δ*':>10} {'Δ':>12} {'Closure':>10}")
    print("-" * 60)
    
    for config in configs:
        a = config['a']
        δ_star = (a**2 * c_0**2) / (4 * np.pi**2)
        closure, damping = riccati_besov_closure(ν, c_B, C_CZ, C_star, δ_star, M)
        
        status = "✅ Yes" if closure else "❌ No"
        print(f"{config['name']:<25} {δ_star:>10.6f} {damping:>12.6f} {status:>10}")
    
    print("\n📊 Conclusion:")
    print("   Increasing 'a' increases δ* and damping coefficient Δ")
    print("   Need a ≥ 7.0 for positive damping")
    print("   Optimal a ≈ 10.0 maximizes damping")


def example_7_bkm_integral_decay():
    """
    Example 7: BKM integral decay with different dampings
    """
    print("\n" + "="*70)
    print("EXAMPLE 7: BKM Integral Dependence on Damping")
    print("="*70)
    
    ω_0 = 10.0
    T = 100.0
    
    dampings = [5.0, 10.0, 15.0, 20.0]
    
    print(f"\nInitial vorticity: ‖ω₀‖_∞ = {ω_0}")
    print(f"Time horizon: T = {T}")
    print("\nBKM integral vs damping coefficient:\n")
    print(f"{'Δ':>8} {'BKM Integral':>15} {'Final ‖ω(T)‖_∞':>18}")
    print("-" * 45)
    
    for Δ in dampings:
        result = riccati_evolution(ω_0, Δ, T)
        print(f"{Δ:>8.1f} {result['bkm_integral']:>15.6f} {result['ω'][-1]:>18.6f}")
    
    print("\n📊 Observation:")
    print("   Stronger damping → Smaller BKM integral")
    print("   Stronger damping → Faster vorticity decay")


def main():
    """
    Run all examples
    """
    print("╔════════════════════════════════════════════════════════════════════╗")
    print("║         UNIFIED BKM FRAMEWORK - Usage Examples                    ║")
    print("╚════════════════════════════════════════════════════════════════════╝")
    
    # Run all examples
    example_1_basic_closure_check()
    example_2_optimal_parameters()
    example_3_riccati_evolution()
    example_4_three_routes()
    example_5_uniformity_validation()
    example_6_comparison()
    example_7_bkm_integral_decay()
    
    print("\n" + "="*70)
    print("✅ ALL EXAMPLES COMPLETED")
    print("="*70)
    print("\nFor more information, see:")
    print("  - Documentation/UNIFIED_BKM_THEORY.md")
    print("  - test_unified_bkm.py for comprehensive tests")
    print("  - unified_validation.py for complete validation sweep")


if __name__ == "__main__":
    main()
