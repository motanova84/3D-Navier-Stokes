#!/usr/bin/env python3
"""
Visualization examples for dimensional flow tensor framework.

Creates visual demonstrations of:
1. 7-layer gravity hierarchy
2. P=NP transition via superfluidity
3. Vortex quantum bridge
4. Calabi-Yau flow mapping
"""

import numpy as np
import matplotlib
matplotlib.use('Agg')  # Use non-interactive backend
import matplotlib.pyplot as plt
from matplotlib import cm
from mpl_toolkits.mplot3d import Axes3D
import os

from dimensional_flow_tensor import (
    DimensionalFlowTensor,
    DimensionalFlowConfig,
    VortexQuantumBridge
)


def visualize_seven_layer_hierarchy(output_dir='Results/DimensionalFlow'):
    """
    Visualize the 7-layer gravity hierarchy.
    """
    print("\n" + "=" * 70)
    print("Generating: 7-Layer Gravity Hierarchy Visualization")
    print("=" * 70)
    
    config = DimensionalFlowConfig()
    dft = DimensionalFlowTensor(config)
    
    frequencies = dft.compute_layer_frequencies()
    
    # Create figure with 7 subplots
    fig, axes = plt.subplots(7, 1, figsize=(12, 16))
    fig.suptitle('7-Layer Dimensional Gravity Hierarchy\nHarmonics of f₀ = 141.7001 Hz', 
                 fontsize=16, fontweight='bold')
    
    # Time array
    t = np.linspace(0, 0.1, 1000)
    
    for i, (ax, freq) in enumerate(zip(axes, frequencies)):
        # Generate harmonic oscillation for this layer
        omega = 2 * np.pi * freq
        amplitude = 1.0 / (i + 1)  # Decreasing amplitude
        signal = amplitude * np.cos(omega * t)
        
        # Plot
        ax.plot(t, signal, linewidth=2, label=f'Layer {i+1}')
        ax.axhline(y=0, color='k', linestyle='--', alpha=0.3)
        ax.set_ylabel(f'Layer {i+1}\n{freq:.1f} Hz', fontsize=10)
        ax.grid(True, alpha=0.3)
        ax.legend(loc='upper right')
        
        if i == 6:
            ax.set_xlabel('Time (s)', fontsize=12)
    
    plt.tight_layout()
    
    # Save
    os.makedirs(output_dir, exist_ok=True)
    filepath = os.path.join(output_dir, 'seven_layer_hierarchy.png')
    plt.savefig(filepath, dpi=150, bbox_inches='tight')
    plt.close()
    
    print(f"✓ Saved: {filepath}")
    return filepath


def visualize_pnp_transition(output_dir='Results/DimensionalFlow'):
    """
    Visualize P→NP transition as coherence changes.
    """
    print("\n" + "=" * 70)
    print("Generating: P=NP Transition Visualization")
    print("=" * 70)
    
    config = DimensionalFlowConfig()
    dft = DimensionalFlowTensor(config)
    
    # Coherence range from turbulent to superfluid
    psi_values = np.linspace(0.1, 1.0, 50)
    
    # Calculate metrics
    pnp_metrics = []
    viscosities = []
    coupling_strengths = []
    
    for psi in psi_values:
        # Create coherence field
        psi_field = np.ones((10, 10, 10)) * psi
        result = dft.check_superfluidity_condition(psi_field)
        pnp_metrics.append(result['pnp_resolution_metric'])
        
        # Viscosity (information resistance)
        nu = dft.viscosity_as_information_resistance(0, psi)
        viscosities.append(nu)
        
        # Layer coupling (0-1 coupling)
        coupling = dft.laminar_layer_coupling(0, 1, psi)
        coupling_strengths.append(coupling)
    
    # Create figure
    fig, axes = plt.subplots(3, 1, figsize=(12, 10))
    fig.suptitle('P=NP Transition via Superfluidity\nCoherence Ψ → 1 at f₀ = 141.7001 Hz',
                 fontsize=16, fontweight='bold')
    
    # Plot 1: P=NP Resolution Metric
    ax1 = axes[0]
    ax1.plot(psi_values, pnp_metrics, 'b-', linewidth=2.5)
    ax1.axhline(y=0.95, color='r', linestyle='--', label='Superfluid Threshold')
    ax1.axvspan(0.95, 1.0, alpha=0.2, color='green', label='P=NP Region')
    ax1.set_ylabel('P=NP Resolution Metric', fontsize=12, fontweight='bold')
    ax1.set_title('Computational Complexity Collapse', fontsize=14)
    ax1.grid(True, alpha=0.3)
    ax1.legend()
    ax1.set_ylim([0, 1.05])
    
    # Add regime labels
    ax1.text(0.3, 0.5, 'P≠NP\n(Turbulent)', fontsize=11, 
             bbox=dict(boxstyle='round', facecolor='red', alpha=0.3))
    ax1.text(0.97, 0.5, 'P=NP\n(Superfluid)', fontsize=11,
             bbox=dict(boxstyle='round', facecolor='green', alpha=0.3))
    
    # Plot 2: Information Resistance (Viscosity)
    ax2 = axes[1]
    ax2.semilogy(psi_values, viscosities, 'r-', linewidth=2.5)
    ax2.set_ylabel('Information Resistance\n(Effective Viscosity)', 
                   fontsize=12, fontweight='bold')
    ax2.set_title('Dimensional Coupling Cost', fontsize=14)
    ax2.grid(True, alpha=0.3, which='both')
    
    # Plot 3: Layer Coupling Strength
    ax3 = axes[2]
    ax3.plot(psi_values, coupling_strengths, 'g-', linewidth=2.5)
    ax3.set_xlabel('Coherence Field Ψ', fontsize=12, fontweight='bold')
    ax3.set_ylabel('Inter-Layer Coupling\n(Friction)', fontsize=12, fontweight='bold')
    ax3.set_title('7-Layer Dimensional Coupling (κ = 1/7)', fontsize=14)
    ax3.grid(True, alpha=0.3)
    ax3.set_ylim([0, max(coupling_strengths) * 1.1])
    
    plt.tight_layout()
    
    # Save
    os.makedirs(output_dir, exist_ok=True)
    filepath = os.path.join(output_dir, 'pnp_transition.png')
    plt.savefig(filepath, dpi=150, bbox_inches='tight')
    plt.close()
    
    print(f"✓ Saved: {filepath}")
    return filepath


def visualize_vortex_quantum_bridge(output_dir='Results/DimensionalFlow'):
    """
    Visualize vortex as quantum bridge (wormhole).
    """
    print("\n" + "=" * 70)
    print("Generating: Vortex Quantum Bridge Visualization")
    print("=" * 70)
    
    bridge = VortexQuantumBridge(f0=141.7001)
    
    # Radial distance from core
    r = np.linspace(0.01, 3.0, 200)
    theta = np.zeros_like(r)
    
    # Calculate vortex properties
    v_theta, pressure = bridge.vortex_core_singularity(r, theta)
    tunnel_metric = bridge.interdimensional_tunnel_metric(r, t=0)
    
    # Jump probability for different coherence levels
    psi_values = [0.5, 0.75, 0.9, 0.99]
    jump_probs = {}
    for psi in psi_values:
        jump_probs[psi] = bridge.dramaturgo_jump_probability(r, psi)
    
    # Create figure
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    fig.suptitle('Vortex as Quantum Bridge: Wormhole in a Glass of Water\nf₀ = 141.7001 Hz',
                 fontsize=16, fontweight='bold')
    
    # Plot 1: Velocity field (singular at r→0)
    ax1 = axes[0, 0]
    ax1.semilogy(r, v_theta, 'b-', linewidth=2.5)
    ax1.set_xlabel('Distance from Core r', fontsize=11)
    ax1.set_ylabel('Tangential Velocity v_θ', fontsize=11, fontweight='bold')
    ax1.set_title('Velocity → ∞ at Core', fontsize=13)
    ax1.grid(True, alpha=0.3, which='both')
    ax1.axvspan(0, 0.1, alpha=0.2, color='red', label='Singular Region')
    ax1.legend()
    
    # Plot 2: Pressure field (minimum at r→0)
    ax2 = axes[0, 1]
    ax2.plot(r, pressure, 'r-', linewidth=2.5)
    ax2.set_xlabel('Distance from Core r', fontsize=11)
    ax2.set_ylabel('Pressure p', fontsize=11, fontweight='bold')
    ax2.set_title('Pressure → 0 at Core', fontsize=13)
    ax2.grid(True, alpha=0.3)
    ax2.axvspan(0, 0.1, alpha=0.2, color='red', label='Portal Zone')
    ax2.legend()
    
    # Plot 3: Tunnel metric (diverges at r→0)
    ax3 = axes[1, 0]
    ax3.semilogy(r, tunnel_metric, 'g-', linewidth=2.5)
    ax3.set_xlabel('Distance from Core r', fontsize=11)
    ax3.set_ylabel('Tunnel Metric g_rr', fontsize=11, fontweight='bold')
    ax3.set_title('Wormhole Throat Strength', fontsize=13)
    ax3.grid(True, alpha=0.3, which='both')
    ax3.axvspan(0, 0.1, alpha=0.2, color='green', label='Wormhole Throat')
    ax3.legend()
    
    # Plot 4: Jump probability
    ax4 = axes[1, 1]
    for psi, probs in jump_probs.items():
        ax4.plot(r, probs, linewidth=2.5, label=f'Ψ = {psi:.2f}')
    ax4.set_xlabel('Distance from Core r', fontsize=11)
    ax4.set_ylabel('Dramaturgo Jump Probability', fontsize=11, fontweight='bold')
    ax4.set_title('Interdimensional Jump Access', fontsize=13)
    ax4.grid(True, alpha=0.3)
    ax4.axhline(y=0.7, color='k', linestyle='--', alpha=0.5, label='Portal Threshold')
    ax4.legend()
    ax4.set_ylim([0, 1])
    
    plt.tight_layout()
    
    # Save
    os.makedirs(output_dir, exist_ok=True)
    filepath = os.path.join(output_dir, 'vortex_quantum_bridge.png')
    plt.savefig(filepath, dpi=150, bbox_inches='tight')
    plt.close()
    
    print(f"✓ Saved: {filepath}")
    return filepath


def visualize_calabi_yau_flow_layers(output_dir='Results/DimensionalFlow'):
    """
    Visualize flow on Calabi-Yau geometry with 7 layers.
    """
    print("\n" + "=" * 70)
    print("Generating: Calabi-Yau Flow Layers Visualization")
    print("=" * 70)
    
    config = DimensionalFlowConfig()
    dft = DimensionalFlowTensor(config)
    
    # Generate Calabi-Yau quintic geometry
    resolution = 30
    u = np.linspace(0, 2*np.pi, resolution)
    v = np.linspace(0, np.pi, resolution)
    U, V = np.meshgrid(u, v)
    
    # Quintic structure
    phi = U
    theta = V
    r = 1.0 + 0.3 * np.cos(5 * theta) * np.sin(5 * phi)
    x = r * np.sin(theta) * np.cos(phi)
    y = r * np.sin(theta) * np.sin(phi)
    z = r * np.cos(theta)
    
    # Get 7-layer flow field
    flow_field = dft.gravity_as_curvature_packing(x, y, z)
    
    # Create figure with 7 3D subplots (simplified to 4 for space)
    fig = plt.figure(figsize=(16, 12))
    fig.suptitle('Dimensional Flow on Calabi-Yau Quintic\n7 Gravity Layers at Harmonics of f₀ = 141.7001 Hz',
                 fontsize=16, fontweight='bold')
    
    layers_to_plot = [0, 2, 4, 6]  # Layers 1, 3, 5, 7
    
    for idx, layer in enumerate(layers_to_plot):
        ax = fig.add_subplot(2, 2, idx+1, projection='3d')
        
        # Color by flow intensity
        colors = flow_field[layer]
        
        # Plot surface
        surf = ax.plot_surface(x, y, z, facecolors=cm.viridis(
            (colors - colors.min()) / (colors.max() - colors.min() + 1e-10)),
            alpha=0.8, antialiased=True)
        
        freq = (layer + 1) * 141.7001
        ax.set_title(f'Layer {layer+1}: {freq:.1f} Hz', fontsize=12, fontweight='bold')
        ax.set_xlabel('X')
        ax.set_ylabel('Y')
        ax.set_zlabel('Z')
        
        # Set viewing angle
        ax.view_init(elev=20, azim=45)
    
    plt.tight_layout()
    
    # Save
    os.makedirs(output_dir, exist_ok=True)
    filepath = os.path.join(output_dir, 'calabi_yau_flow_layers.png')
    plt.savefig(filepath, dpi=150, bbox_inches='tight')
    plt.close()
    
    print(f"✓ Saved: {filepath}")
    return filepath


def generate_all_visualizations():
    """Generate all visualization examples."""
    print("\n")
    print("╔" + "=" * 68 + "╗")
    print("║" + " " * 68 + "║")
    print("║" + "  DIMENSIONAL FLOW TENSOR - Visualization Suite  ".center(68) + "║")
    print("║" + " " * 68 + "║")
    print("╚" + "=" * 68 + "╝")
    print("\n")
    
    output_dir = 'Results/DimensionalFlow'
    
    # Generate all visualizations
    viz1 = visualize_seven_layer_hierarchy(output_dir)
    viz2 = visualize_pnp_transition(output_dir)
    viz3 = visualize_vortex_quantum_bridge(output_dir)
    viz4 = visualize_calabi_yau_flow_layers(output_dir)
    
    print("\n" + "=" * 70)
    print("VISUALIZATION SUITE COMPLETE")
    print("=" * 70)
    print(f"\nAll visualizations saved to: {output_dir}/")
    print("\nGenerated files:")
    print(f"  1. {os.path.basename(viz1)}")
    print(f"  2. {os.path.basename(viz2)}")
    print(f"  3. {os.path.basename(viz3)}")
    print(f"  4. {os.path.basename(viz4)}")
    print("\n✓ Complete\n")


if __name__ == "__main__":
    generate_all_visualizations()
