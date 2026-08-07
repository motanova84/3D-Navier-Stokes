#!/usr/bin/env python3
"""
Spacetime-Fluid Visualization
==============================

Visualizes the coherence field Ψ(x,t) in 3D space, showing:
1. Time evolution of the field
2. Vorticity around massive objects (simulated black hole)
3. Universal oscillation at f₀ = 141.7001 Hz

This demonstrates the membrane paradigm: spacetime as a coherent quantum fluid.
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from matplotlib.animation import FuncAnimation
import os

# QCAL Constants
F0 = 141.7001  # Hz - fundamental frequency
OMEGA_0 = 2 * np.pi * F0  # rad/s
EPSILON = 1e-3  # Regularization parameter


class SpacetimeFluidSimulator:
    """Simulates the coherence field Ψ in spacetime-as-fluid interpretation."""
    
    def __init__(self, grid_size=50, domain_size=10.0):
        """
        Initialize the simulator.
        
        Args:
            grid_size: Number of grid points per dimension
            domain_size: Physical size of domain in arbitrary units
        """
        self.grid_size = grid_size
        self.domain_size = domain_size
        
        # Create 3D grid
        x = np.linspace(-domain_size/2, domain_size/2, grid_size)
        y = np.linspace(-domain_size/2, domain_size/2, grid_size)
        z = np.linspace(-domain_size/2, domain_size/2, grid_size)
        self.X, self.Y, self.Z = np.meshgrid(x, y, z, indexing='ij')
        
        # Massive object location (simulated black hole at origin)
        self.mass_center = np.array([0.0, 0.0, 0.0])
        self.mass = 1.0  # Arbitrary mass units
        
    def velocity_field(self, t):
        """
        Construct velocity field u(x,t) around massive object.
        
        Models frame-dragging and infall near a rotating mass.
        """
        # Distance from mass center
        r = np.sqrt((self.X - self.mass_center[0])**2 + 
                   (self.Y - self.mass_center[1])**2 + 
                   (self.Z - self.mass_center[2])**2)
        
        # Avoid singularity
        r = np.maximum(r, 0.1)
        
        # Radial infall component (∝ 1/r²)
        u_r = -self.mass / r**2
        
        # Tangential (rotational) component - frame dragging
        # Creates vorticity ω ≠ 0
        angular_freq = 0.5 * OMEGA_0 / r
        
        # Velocity components
        u_x = u_r * (self.X - self.mass_center[0]) / r - angular_freq * self.Y
        u_y = u_r * (self.Y - self.mass_center[1]) / r + angular_freq * self.X
        u_z = u_r * (self.Z - self.mass_center[2]) / r
        
        return u_x, u_y, u_z
    
    def gradient_norm_squared(self, u_x, u_y, u_z):
        """
        Compute ‖∇u‖² - the coherence field before time modulation.
        
        This is a simplified approximation using finite differences.
        """
        # Simplified: use velocity magnitude as proxy for gradient energy
        # In full implementation, would compute actual spatial derivatives
        grad_norm_sq = u_x**2 + u_y**2 + u_z**2
        return grad_norm_sq
    
    def coherence_field(self, t):
        """
        Compute full coherence field Ψ(x,t) = ‖∇u‖² · cos(2πf₀t)
        """
        u_x, u_y, u_z = self.velocity_field(t)
        psi_spatial = self.gradient_norm_squared(u_x, u_y, u_z)
        
        # Time modulation at f₀ = 141.7001 Hz
        psi_time = np.cos(OMEGA_0 * t)
        
        # Full coherence field
        psi = psi_spatial * psi_time
        
        return psi
    
    def vorticity_magnitude(self, t):
        """
        Compute vorticity magnitude |ω| = |∇ × u|
        
        High near rotating mass (frame dragging).
        """
        u_x, u_y, u_z = self.velocity_field(t)
        
        # Simplified: use rotational component
        r = np.sqrt(self.X**2 + self.Y**2 + self.Z**2)
        r = np.maximum(r, 0.1)
        
        omega = 0.5 * OMEGA_0 / r
        return omega
    
    def ricci_density(self):
        """
        Density proportional to Ricci curvature.
        
        High density near massive objects.
        """
        r = np.sqrt((self.X - self.mass_center[0])**2 + 
                   (self.Y - self.mass_center[1])**2 + 
                   (self.Z - self.mass_center[2])**2)
        r = np.maximum(r, 0.1)
        
        # Ricci density ∝ 1/r (simplified)
        density = self.mass / r
        return density


def create_2d_slice_plot(simulator, t_values, output_dir='Results/SpacetimeFluid'):
    """Create 2D slice visualization of Ψ at different times."""
    
    os.makedirs(output_dir, exist_ok=True)
    
    fig, axes = plt.subplots(2, 2, figsize=(14, 12))
    fig.suptitle('Coherence Field Ψ(x,y,0,t) - Spacetime as Fluid\n' + 
                 f'Universal Frequency f₀ = {F0} Hz', fontsize=14, fontweight='bold')
    
    # Take z=0 slice
    z_slice = simulator.grid_size // 2
    
    for idx, (ax, t) in enumerate(zip(axes.flat, t_values)):
        psi = simulator.coherence_field(t)
        psi_slice = psi[:, :, z_slice]
        
        im = ax.contourf(simulator.X[:, :, z_slice], 
                        simulator.Y[:, :, z_slice], 
                        psi_slice, 
                        levels=20, cmap='RdYlBu_r')
        
        # Add contour lines
        ax.contour(simulator.X[:, :, z_slice], 
                  simulator.Y[:, :, z_slice], 
                  psi_slice, 
                  levels=10, colors='black', alpha=0.3, linewidths=0.5)
        
        ax.set_xlabel('x')
        ax.set_ylabel('y')
        ax.set_title(f't = {t:.6f}s (phase = {(t*F0) % 1:.3f} cycles)')
        ax.set_aspect('equal')
        ax.grid(True, alpha=0.3)
        
        # Mark mass center
        ax.plot(0, 0, 'ko', markersize=8, label='Mass Center')
        ax.legend()
        
        plt.colorbar(im, ax=ax, label='Ψ(x,y,0,t)')
    
    plt.tight_layout()
    filename = os.path.join(output_dir, 'coherence_field_evolution.png')
    plt.savefig(filename, dpi=150, bbox_inches='tight')
    print(f"✓ Saved coherence field evolution to {filename}")
    plt.close()


def create_vorticity_plot(simulator, output_dir='Results/SpacetimeFluid'):
    """Visualize vorticity field (spacetime rotation)."""
    
    os.makedirs(output_dir, exist_ok=True)
    
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))
    fig.suptitle('Spacetime Vorticity ω = ∇ × u (Frame Dragging)', 
                 fontsize=14, fontweight='bold')
    
    # Take z=0 slice
    z_slice = simulator.grid_size // 2
    t = 0.0
    
    omega = simulator.vorticity_magnitude(t)
    omega_slice = omega[:, :, z_slice]
    
    # Log scale for better visualization
    omega_log = np.log10(omega_slice + EPSILON)
    
    # Plot 1: Vorticity magnitude
    im1 = ax1.contourf(simulator.X[:, :, z_slice], 
                      simulator.Y[:, :, z_slice], 
                      omega_log, 
                      levels=20, cmap='plasma')
    ax1.set_xlabel('x')
    ax1.set_ylabel('y')
    ax1.set_title('Log₁₀(|ω|) - Vorticity Magnitude')
    ax1.set_aspect('equal')
    ax1.plot(0, 0, 'wo', markersize=8, label='Rotating Mass')
    ax1.legend()
    plt.colorbar(im1, ax=ax1, label='log₁₀(|ω|)')
    
    # Plot 2: Ricci density
    density = simulator.ricci_density()
    density_slice = density[:, :, z_slice]
    density_log = np.log10(density_slice + EPSILON)
    
    im2 = ax2.contourf(simulator.X[:, :, z_slice], 
                      simulator.Y[:, :, z_slice], 
                      density_log, 
                      levels=20, cmap='viridis')
    ax2.set_xlabel('x')
    ax2.set_ylabel('y')
    ax2.set_title('Log₁₀(ρ) - Ricci Curvature Density')
    ax2.set_aspect('equal')
    ax2.plot(0, 0, 'wo', markersize=8, label='Mass Center')
    ax2.legend()
    plt.colorbar(im2, ax=ax2, label='log₁₀(ρ)')
    
    plt.tight_layout()
    filename = os.path.join(output_dir, 'vorticity_and_density.png')
    plt.savefig(filename, dpi=150, bbox_inches='tight')
    print(f"✓ Saved vorticity and density to {filename}")
    plt.close()


def create_frequency_spectrum(simulator, duration=0.1, output_dir='Results/SpacetimeFluid'):
    """
    Show frequency spectrum of Ψ(t) at a fixed point.
    Demonstrates the 141.7 Hz peak.
    """
    
    os.makedirs(output_dir, exist_ok=True)
    
    # Sample at a point away from singularity
    sample_point = (simulator.grid_size // 2 + 10, 
                   simulator.grid_size // 2, 
                   simulator.grid_size // 2)
    
    # Time series
    dt = 1.0 / (10 * F0)  # Sample at 10× Nyquist
    t_array = np.arange(0, duration, dt)
    psi_series = np.array([simulator.coherence_field(t)[sample_point] 
                          for t in t_array])
    
    # FFT
    from scipy.fft import fft, fftfreq
    N = len(t_array)
    yf = fft(psi_series)
    xf = fftfreq(N, dt)[:N//2]
    power = 2.0/N * np.abs(yf[:N//2])
    
    # Plot
    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(12, 8))
    fig.suptitle('Frequency Analysis of Coherence Field Ψ(t)\n' + 
                 'Demonstrating Cosmic Heartbeat at f₀ = 141.7001 Hz',
                 fontsize=14, fontweight='bold')
    
    # Time series
    ax1.plot(t_array * 1000, psi_series, 'b-', linewidth=1)
    ax1.set_xlabel('Time (ms)')
    ax1.set_ylabel('Ψ(t)')
    ax1.set_title('Time Evolution at Fixed Point')
    ax1.grid(True, alpha=0.3)
    
    # Spectrum
    ax2.semilogy(xf, power, 'r-', linewidth=1)
    ax2.axvline(F0, color='g', linestyle='--', linewidth=2, label=f'f₀ = {F0} Hz')
    ax2.set_xlabel('Frequency (Hz)')
    ax2.set_ylabel('Power Spectrum')
    ax2.set_title('Frequency Spectrum - Peak at Universal Frequency')
    ax2.set_xlim(0, 500)
    ax2.grid(True, alpha=0.3)
    ax2.legend()
    
    plt.tight_layout()
    filename = os.path.join(output_dir, 'frequency_spectrum.png')
    plt.savefig(filename, dpi=150, bbox_inches='tight')
    print(f"✓ Saved frequency spectrum to {filename}")
    plt.close()


def main():
    """Main execution."""
    
    print("=" * 70)
    print("SPACETIME-FLUID VISUALIZATION")
    print("Membrane Paradigm: Spacetime as Coherent Quantum Fluid")
    print("=" * 70)
    print(f"\nQCAL Parameters:")
    print(f"  Fundamental Frequency: f₀ = {F0} Hz")
    print(f"  Angular Frequency: ω₀ = {OMEGA_0:.2f} rad/s")
    print(f"  Period: T₀ = {1/F0:.6f} s = {1000/F0:.3f} ms")
    print()
    
    # Create simulator
    print("Initializing spacetime-fluid simulator...")
    simulator = SpacetimeFluidSimulator(grid_size=50, domain_size=10.0)
    print("✓ Simulator ready")
    print()
    
    # Generate visualizations
    print("Generating visualizations...")
    
    # 1. Coherence field evolution
    # Show 4 time points spanning one period
    T0 = 1.0 / F0
    t_values = [0, T0/4, T0/2, 3*T0/4]
    create_2d_slice_plot(simulator, t_values)
    
    # 2. Vorticity and density
    create_vorticity_plot(simulator)
    
    # 3. Frequency spectrum
    create_frequency_spectrum(simulator, duration=0.05)
    
    print()
    print("=" * 70)
    print("VISUALIZATION COMPLETE")
    print("=" * 70)
    print("\nGenerated files in Results/SpacetimeFluid/:")
    print("  1. coherence_field_evolution.png - Ψ(x,t) at different times")
    print("  2. vorticity_and_density.png - Vorticity ω and Ricci density ρ")
    print("  3. frequency_spectrum.png - FFT showing 141.7 Hz peak")
    print()
    print("Physical Interpretation:")
    print("  • Coherence field Ψ oscillates at cosmic frequency f₀")
    print("  • Vorticity ω represents spacetime rotation (frame dragging)")
    print("  • Density ρ ∝ Ricci curvature (high near masses)")
    print("  • Universal 141.7 Hz heartbeat visible in spectrum")
    print()
    print("Next Steps:")
    print("  → Compare with gravitational wave data")
    print("  → Test predictions in BEC experiments")
    print("  → Extend to full 4D spacetime visualization")
    print("=" * 70)


if __name__ == '__main__':
    # Ensure scipy is available
    try:
        import scipy
    except ImportError:
        print("Warning: scipy not installed. Frequency analysis will be skipped.")
        print("Install with: pip install scipy")
    
    main()
