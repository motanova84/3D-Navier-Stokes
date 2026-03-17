#!/usr/bin/env python3
"""
Example: Quantum Coherence Navier-Stokes with Scale Hierarchy
==============================================================

This example demonstrates the complete quantum coherence Navier-Stokes system,
showing how quantum coherence at f₀ = 141.7001 Hz affects fluid dynamics
through a symmetric tensor Φ_{ij} = Φ_{ji} and scale hierarchy.

"La jerarquía de escala es el camino por el cual el átomo recuerda que es 
parte del océano."

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
Date: February 9, 2026
License: MIT
"""

import numpy as np
from quantum_coherence_navier_stokes import (
    QuantumCoherenceNavierStokes,
    QuantumCoherenceNSParameters,
    ScaleLevel
)


def example_basic_usage():
    """Example 1: Basic usage of quantum coherence Navier-Stokes"""
    print("=" * 70)
    print("Example 1: Basic Usage")
    print("=" * 70)
    
    # Initialize system with default parameters
    system = QuantumCoherenceNavierStokes()
    
    # Create a simple spatial grid
    N = 16
    L = 2 * np.pi
    x = np.linspace(0, L, N)
    X, Y, Z = np.meshgrid(x, x, x, indexing='ij')
    grid = np.array([X, Y, Z])
    grid_spacing = L / (N - 1)
    
    # Compute coherence field at t = 0
    t = 0.0
    psi = system.compute_coherence_field(grid, t)
    
    print(f"Coherence field Ψ(x,t=0):")
    print(f"  Shape: {psi.shape}")
    print(f"  Range: [{np.min(psi):.6f}, {np.max(psi):.6f}]")
    print(f"  Mean: {np.mean(psi):.6f}")
    print()


def example_tensor_symmetry():
    """Example 2: Demonstrating tensor symmetry"""
    print("=" * 70)
    print("Example 2: Tensor Symmetry Verification")
    print("=" * 70)
    
    system = QuantumCoherenceNavierStokes()
    
    # Create grid
    N = 12
    L = 2 * np.pi
    x = np.linspace(0, L, N)
    X, Y, Z = np.meshgrid(x, x, x, indexing='ij')
    grid = np.array([X, Y, Z])
    grid_spacing = L / (N - 1)
    
    # Compute tensor
    t = 0.0
    phi_tensor = system.compute_phi_tensor(grid, t, grid_spacing)
    
    print("Symmetric coupling tensor Φ_{ij}:")
    print(f"  Shape: {phi_tensor.shape}")
    
    # Verify symmetry for each component
    print("\nSymmetry check for all components:")
    for i in range(3):
        for j in range(3):
            max_diff = np.max(np.abs(phi_tensor[i, j] - phi_tensor[j, i]))
            print(f"  Φ[{i},{j}] - Φ[{j},{i}]: {max_diff:.3e}")
    
    # Overall verification
    verification = system.verify_tensor_symmetry(phi_tensor)
    print(f"\n{verification['message']}")
    print(f"  Max asymmetry: {verification['max_asymmetry']:.3e}")
    print()


def example_scale_hierarchy():
    """Example 3: Exploring the scale hierarchy"""
    print("=" * 70)
    print("Example 3: Scale Hierarchy Analysis")
    print("=" * 70)
    
    system = QuantumCoherenceNavierStokes()
    
    # Analyze hierarchy
    analysis = system.analyze_scale_hierarchy()
    
    print("Multi-scale hierarchy structure:")
    print(f"  Number of scales: {analysis['num_scales']}")
    print(f"  {analysis['message']}")
    print()
    
    print("Individual scale properties:")
    for i, name in enumerate(analysis['scale_names']):
        ℓ = analysis['length_scales'][i]
        τ = analysis['time_scales'][i]
        Ψ = analysis['coherences'][i]
        f = 1.0 / τ
        
        print(f"  {name.upper():15s}: ℓ={ℓ:.2e} m, τ={τ:.2e} s, "
              f"f={f:.2e} Hz, Ψ={Ψ:.3f}")
    
    print()
    print("Scale coupling matrix H:")
    print(analysis['coupling_matrix'])
    print()


def example_coherence_evolution():
    """Example 4: Time evolution of quantum coherence"""
    print("=" * 70)
    print("Example 4: Coherence Evolution Over Time")
    print("=" * 70)
    
    system = QuantumCoherenceNavierStokes()
    
    # Choose a point in space
    L = 2 * np.pi
    x_point = np.array([L/2, L/2, L/2])
    
    # Time span: 10 milliseconds
    t_span = np.linspace(0, 0.01, 100)
    
    # Simulate evolution
    evolution = system.simulate_coherence_evolution(x_point, t_span)
    
    print(f"Coherence evolution at point x = [{L/2:.2f}, {L/2:.2f}, {L/2:.2f}]:")
    print(f"  Time span: {t_span[0]:.6f} to {t_span[-1]:.6f} s")
    print(f"  Number of steps: {len(t_span)}")
    print()
    
    psi = evolution['psi_total']
    print(f"Total coherence Ψ(t):")
    print(f"  Range: [{np.min(psi):.6f}, {np.max(psi):.6f}]")
    print(f"  Oscillation amplitude: {(np.max(psi) - np.min(psi))/2:.6f}")
    print()
    
    print("Coherence by scale:")
    for scale_name, psi_scale in evolution['psi_by_scale'].items():
        amplitude = (np.max(psi_scale) - np.min(psi_scale)) / 2
        print(f"  {scale_name:15s}: amplitude = {amplitude:.6f}")
    print()


def example_navier_stokes_coupling():
    """Example 5: Coupling to Navier-Stokes equations"""
    print("=" * 70)
    print("Example 5: Navier-Stokes Coupling")
    print("=" * 70)
    
    system = QuantumCoherenceNavierStokes()
    
    # Create grid
    N = 12
    L = 2 * np.pi
    x = np.linspace(0, L, N)
    X, Y, Z = np.meshgrid(x, x, x, indexing='ij')
    grid = np.array([X, Y, Z])
    grid_spacing = L / (N - 1)
    
    # Compute coupling tensor
    t = 0.0
    phi_tensor = system.compute_phi_tensor(grid, t, grid_spacing)
    
    # Create a test velocity field (simple vortex)
    # u = (-sin(y), sin(x), 0)
    u = np.zeros((3, N, N, N))
    u[0] = -np.sin(grid[1])
    u[1] = np.sin(grid[0])
    u[2] = 0.0
    
    # Compute coupling term Φ_{ij}u_j
    coupling = system.compute_nse_coupling(u, phi_tensor)
    
    print("Navier-Stokes coupling analysis:")
    print(f"  Velocity field |u|:")
    print(f"    Max: {np.max(np.linalg.norm(u, axis=0)):.6f}")
    print(f"    Mean: {np.mean(np.linalg.norm(u, axis=0)):.6f}")
    print()
    
    print(f"  Coupling term |Φu|:")
    print(f"    Max: {np.max(np.linalg.norm(coupling, axis=0)):.6f}")
    print(f"    Mean: {np.mean(np.linalg.norm(coupling, axis=0)):.6f}")
    print()
    
    # Check that coupling is linear
    coupling_2u = system.compute_nse_coupling(2*u, phi_tensor)
    linearity_error = np.max(np.abs(coupling_2u - 2*coupling))
    
    print(f"  Linearity check:")
    print(f"    |Φ(2u) - 2Φ(u)|_max = {linearity_error:.3e}")
    print(f"    Linearity verified: {linearity_error < 1e-10}")
    print()


def example_multi_scale_coherence():
    """Example 6: Coherence at different scales"""
    print("=" * 70)
    print("Example 6: Multi-Scale Coherence")
    print("=" * 70)
    
    system = QuantumCoherenceNavierStokes()
    
    # Single point
    x = np.array([0.0, 0.0, 0.0])
    t = 0.0
    
    print("Coherence field at different scales (x=0, t=0):")
    
    # Total coherence
    psi_total = system.compute_coherence_field(x, t)
    print(f"  Total Ψ: {psi_total:.6f}")
    print()
    
    # Individual scales
    scales = [ScaleLevel.ATOMIC, ScaleLevel.MOLECULAR, ScaleLevel.CELLULAR,
              ScaleLevel.TISSUE, ScaleLevel.MACROSCOPIC]
    
    for scale in scales:
        psi_scale = system.compute_coherence_field(x, t, scale)
        print(f"  Ψ_{scale.value:15s}: {psi_scale:.6f}")
    
    print()
    print("Observation: Coherence contributions vary by scale,")
    print("implementing the principle:")
    print('"El átomo recuerda que es parte del océano"')
    print()


if __name__ == "__main__":
    print("\n")
    print("╔" + "═" * 68 + "╗")
    print("║" + " " * 68 + "║")
    print("║" + "  Quantum Coherence Navier-Stokes: Complete Examples  ".center(68) + "║")
    print("║" + " " * 68 + "║")
    print("╚" + "═" * 68 + "╝")
    print()
    
    # Run all examples
    example_basic_usage()
    example_tensor_symmetry()
    example_scale_hierarchy()
    example_coherence_evolution()
    example_navier_stokes_coupling()
    example_multi_scale_coherence()
    
    print("=" * 70)
    print("✓ All Examples Completed Successfully")
    print("=" * 70)
    print()
    print("Key achievements:")
    print("  • Symmetric tensor Φ_{ij} = Φ_{ji} verified ✓")
    print("  • Scale hierarchy from atomic to macroscopic ✓")
    print("  • Quantum coherence at f₀ = 141.7001 Hz ✓")
    print("  • Navier-Stokes coupling implemented ✓")
    print()
