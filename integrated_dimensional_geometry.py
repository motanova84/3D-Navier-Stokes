#!/usr/bin/env python3
"""
Integration module for Dimensional Flow Tensor with Calabi-Yau geometry.

This module connects the dimensional flow tensor framework to the existing
Calabi-Yau visualizer and Navier-Stokes solvers.
"""

import numpy as np
import sys
import os
from typing import Tuple, Optional, Dict

# Add scripts directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'scripts', 'geometrías_reguladoras'))

try:
    from visualizador_calabi_yau_3d import CalabiYauVisualizer
except ImportError:
    CalabiYauVisualizer = None

from dimensional_flow_tensor import (
    DimensionalFlowTensor,
    DimensionalFlowConfig,
    VortexQuantumBridge
)


class IntegratedFluidGeometry:
    """
    Integrates dimensional flow tensors with Calabi-Yau geometry.
    
    This class connects:
    - 7-layer dimensional flow tensors
    - Calabi-Yau quintic geometry
    - Vortex quantum bridges
    - Noetic coherence field Ψ
    """
    
    def __init__(self, resolution: int = 50, f0: float = 141.7001):
        """
        Initialize integrated system.
        
        Args:
            resolution: Spatial resolution for geometry
            f0: Root frequency (Hz)
        """
        self.resolution = resolution
        self.f0 = f0
        
        # Initialize dimensional flow tensor
        config = DimensionalFlowConfig(f0=f0)
        self.dft = DimensionalFlowTensor(config)
        
        # Initialize vortex bridge
        self.vortex_bridge = VortexQuantumBridge(f0=f0)
        
        # Initialize Calabi-Yau visualizer if available
        if CalabiYauVisualizer is not None:
            self.cy_viz = CalabiYauVisualizer(resolution=resolution, f0=f0)
        else:
            self.cy_viz = None
    
    def generate_calabi_yau_flow_field(self, t: float = 0.0) -> Tuple[np.ndarray, ...]:
        """
        Generate flow field over Calabi-Yau geometry.
        
        Maps the 7 dimensional gravity layers onto Calabi-Yau quintic,
        showing how fluid flows as tensors through geometric constraints.
        
        Args:
            t: Time parameter
            
        Returns:
            x, y, z: Geometry coordinates
            flow_tensors: 7-layer flow tensor field
            psi_field: Coherence field
        """
        # Generate Calabi-Yau geometry
        u = np.linspace(0, 2*np.pi, self.resolution)
        v = np.linspace(0, np.pi, self.resolution)
        U, V = np.meshgrid(u, v)
        
        if self.cy_viz is not None:
            x, y, z = self.cy_viz.calabi_yau_quintic(U, V)
            psi_field = self.cy_viz.noetic_field_psi(x, y, z, t=t)
        else:
            # Fallback: simple quintic approximation
            phi = U
            theta = V
            r = 1.0 + 0.3 * np.cos(5 * theta) * np.sin(5 * phi)
            x = r * np.sin(theta) * np.cos(phi)
            y = r * np.sin(theta) * np.sin(phi)
            z = r * np.cos(theta)
            
            # Simple coherence field
            r_squared = x**2 + y**2 + z**2
            psi_field = np.exp(-0.1 * r_squared) * (0.88 + 0.12 * np.cos(self.dft.omega0 * t))
        
        # Generate 7-layer flow tensor field
        flow_tensors = self.dft.gravity_as_curvature_packing(x, y, z)
        
        return x, y, z, flow_tensors, psi_field
    
    def compute_laminar_to_turbulent_transition(self, 
                                               psi_field: np.ndarray) -> Dict[str, any]:
        """
        Analyze transition from laminar (P) to turbulent (NP) flow.
        
        Args:
            psi_field: Coherence field Ψ(x,t)
            
        Returns:
            analysis: Dictionary with transition metrics
        """
        # Check superfluidity condition (P=NP resolution)
        superfluid_result = self.dft.check_superfluidity_condition(psi_field)
        
        # Calculate fraction of space in each regime
        psi_mean = np.mean(psi_field)
        psi_std = np.std(psi_field)
        
        # Laminar regions: Ψ > 0.85 (following κ_Π geometry)
        laminar_fraction = np.sum(psi_field > 0.85) / psi_field.size
        
        # Turbulent regions: Ψ < 0.5 (breaking coherence)
        turbulent_fraction = np.sum(psi_field < 0.5) / psi_field.size
        
        # Transitional regions
        transitional_fraction = 1.0 - laminar_fraction - turbulent_fraction
        
        analysis = {
            'psi_mean': psi_mean,
            'psi_std': psi_std,
            'laminar_fraction': laminar_fraction,
            'turbulent_fraction': turbulent_fraction,
            'transitional_fraction': transitional_fraction,
            'is_superfluid': superfluid_result['is_superfluid'],
            'pnp_regime': superfluid_result['flow_regime'],
            'computational_complexity': 'P' if laminar_fraction > 0.8 else 'NP'
        }
        
        return analysis
    
    def analyze_vortex_interdimensional_portal(self, 
                                               vortex_center: Tuple[float, float, float],
                                               psi_coherence: float = 0.9,
                                               radius_range: float = 2.0) -> Dict[str, any]:
        """
        Analyze vortex as quantum portal between dimensions.
        
        The Dramaturgo uses vortex cores to jump between 34 repositories
        through wormholes in fluid space.
        
        Args:
            vortex_center: (x, y, z) coordinates of vortex center
            psi_coherence: Quantum coherence at vortex
            radius_range: Maximum radius to analyze
            
        Returns:
            portal_analysis: Dictionary with portal metrics
        """
        # Generate radial points from vortex center
        r = np.linspace(0.01, radius_range, 100)
        theta = np.zeros_like(r)
        
        # Calculate vortex properties
        v_theta, pressure = self.vortex_bridge.vortex_core_singularity(r, theta)
        tunnel_metric = self.vortex_bridge.interdimensional_tunnel_metric(r, t=0)
        jump_prob = self.vortex_bridge.dramaturgo_jump_probability(r, psi_coherence)
        
        # Find optimal jump radius (highest probability)
        optimal_idx = np.argmax(jump_prob)
        optimal_radius = r[optimal_idx]
        max_jump_prob = jump_prob[optimal_idx]
        
        portal_analysis = {
            'vortex_center': vortex_center,
            'coherence': psi_coherence,
            'optimal_jump_radius': optimal_radius,
            'max_jump_probability': max_jump_prob,
            'core_velocity': v_theta[0],
            'core_pressure': pressure[0],
            'tunnel_strength': tunnel_metric[0],
            'is_portal_active': max_jump_prob > 0.7,
            'dramaturgo_access': 'ENABLED' if max_jump_prob > 0.7 else 'LIMITED'
        }
        
        return portal_analysis
    
    def demonstrate_water_as_gravity_layers(self):
        """
        Demonstrate viewing water as hierarchical gravity layers.
        
        Shows how the fluid is not simple matter but dimensional tensors
        organized in 7 layers of gravitational hierarchy.
        """
        print("\n" + "=" * 70)
        print("DEMONSTRATION: Water as 7 Gravity Layers")
        print("=" * 70 + "\n")
        
        # Generate geometry and flow
        x, y, z, flow_tensors, psi_field = self.generate_calabi_yau_flow_field(t=0)
        
        print("Calabi-Yau Geometric Constraints:")
        print(f"  Grid resolution: {self.resolution}×{self.resolution}")
        print(f"  Geometry points: {x.size}")
        print()
        
        print("7 Gravity Layers (Dimensional Tensors):")
        frequencies = self.dft.compute_layer_frequencies()
        for i, freq in enumerate(frequencies):
            layer_energy = np.mean(np.abs(flow_tensors[i]))
            print(f"  Layer {i+1}: {freq:8.4f} Hz - Energy: {layer_energy:.6f}")
        print()
        
        # Analyze laminar-turbulent transition
        analysis = self.compute_laminar_to_turbulent_transition(psi_field)
        
        print("Flow Regime Analysis (P vs NP):")
        print(f"  Mean Coherence Ψ: {analysis['psi_mean']:.4f}")
        print(f"  Laminar (P):      {analysis['laminar_fraction']*100:.1f}%")
        print(f"  Turbulent (NP):   {analysis['turbulent_fraction']*100:.1f}%")
        print(f"  Transitional:     {analysis['transitional_fraction']*100:.1f}%")
        print(f"  Regime: {analysis['pnp_regime']}")
        print()
        
        # Calculate viscosity as information resistance
        nu_eff = self.dft.viscosity_as_information_resistance(0, analysis['psi_mean'])
        print(f"Information Resistance (Viscosity): {nu_eff:.6f}")
        print(f"  → How much it costs for one dimension to yield to another")
        print()
        
        print("=" * 70 + "\n")
    
    def demonstrate_vortex_wormhole(self):
        """
        Demonstrate vortex as wormhole for interdimensional jumps.
        """
        print("\n" + "=" * 70)
        print("DEMONSTRATION: Vortex as Wormhole (Dramaturgo Portal)")
        print("=" * 70 + "\n")
        
        # Analyze vortex at origin
        vortex_center = (0.0, 0.0, 0.0)
        portal = self.analyze_vortex_interdimensional_portal(
            vortex_center,
            psi_coherence=0.92
        )
        
        print(f"Vortex Analysis at {vortex_center}:")
        print(f"  Coherence Ψ: {portal['coherence']:.2f}")
        print(f"  Core Velocity: {portal['core_velocity']:.2f} (→ ∞ at r=0)")
        print(f"  Core Pressure: {portal['core_pressure']:.2f} (→ 0 at r=0)")
        print(f"  Tunnel Strength: {portal['tunnel_strength']:.2f}")
        print()
        
        print(f"Interdimensional Jump Analysis:")
        print(f"  Optimal Jump Radius: {portal['optimal_jump_radius']:.4f}")
        print(f"  Max Jump Probability: {portal['max_jump_probability']:.4f}")
        print(f"  Portal Status: {portal['dramaturgo_access']}")
        print()
        
        if portal['is_portal_active']:
            print("✓ PORTAL ACTIVE: Dramaturgo can jump between 34 repositories")
            print("  → Wormhole in a glass of water operational!")
        else:
            print("⚠ PORTAL LIMITED: Need higher coherence for full access")
        
        print()
        print("=" * 70 + "\n")


def main():
    """Main demonstration of integrated framework."""
    print("\n")
    print("╔" + "=" * 68 + "╗")
    print("║" + " " * 68 + "║")
    print("║" + "  INTEGRATED DIMENSIONAL FLOW + CALABI-YAU GEOMETRY  ".center(68) + "║")
    print("║" + "  Water as 7-Layer Gravity Hierarchy  ".center(68) + "║")
    print("║" + "  Vortex as Interdimensional Wormhole  ".center(68) + "║")
    print("║" + " " * 68 + "║")
    print("╚" + "=" * 68 + "╝")
    print("\n")
    
    # Create integrated system
    system = IntegratedFluidGeometry(resolution=30, f0=141.7001)
    
    # Run demonstrations
    system.demonstrate_water_as_gravity_layers()
    system.demonstrate_vortex_wormhole()
    
    print("\n✓ Integrated Framework Demonstration Complete\n")


if __name__ == "__main__":
    main()
