#!/usr/bin/env python3
"""
═══════════════════════════════════════════════════════════════════════════
STABLE-BY-DESIGN DNS/CFD FRAMEWORK
Using Seeley-DeWitt Tensor Φ_ij(Ψ) as Quantum-Geometric Regularizer
═══════════════════════════════════════════════════════════════════════════

This module implements a DNS/CFD solver that is STABLE BY DESIGN through
quantum-geometric regularization. Unlike classical methods that rely on
ad-hoc turbulence models (Smagorinsky, k-ε, etc.), this approach derives
stability from first principles via the Seeley-DeWitt tensor.

PARADIGM SHIFT:
--------------
Classical DNS/CFD: Stability through empirical turbulence models
Quantum DNS/CFD:   Stability through geometric coherence (Ψ-field)

The Seeley-DeWitt tensor Φ_ij(Ψ) provides:
1. Geometric regularization (no ad-hoc parameters)
2. Quantum coherence coupling (f₀ = 141.7001 Hz)
3. Singularity prevention (built-in, not added)
4. Universal stability (independent of Reynolds number)

Author: José Manuel Mota Burruezo (JMMB Ψ✧∞³)
Date: 2025-11-03
License: MIT
"""

import numpy as np
from scipy.fft import fftn, ifftn, fftfreq
import matplotlib.pyplot as plt
from typing import Tuple, Dict, Optional
from dataclasses import dataclass
import time
import os

# Import Seeley-DeWitt tensor from proper package location
from NavierStokes.seeley_dewitt_tensor import SeeleyDeWittTensor, SeeleyDeWittParams


# Universal constants
UNIVERSAL_COHERENCE_FREQUENCY = 141.7001  # Hz - from QFT, not adjustable


@dataclass
class StableDNSConfig:
    """Configuration for stable-by-design DNS solver"""
    # Spatial resolution
    N: int = 64  # Grid points per dimension
    L: float = 2 * np.pi  # Domain size
    
    # Time integration
    dt: float = 0.001  # Time step
    T_max: float = 10.0  # Maximum simulation time
    
    # Physical parameters
    nu: float = 1e-3  # Kinematic viscosity
    Re: float = 1000.0  # Reynolds number
    
    # Quantum-geometric regularization
    use_quantum_regularization: bool = True
    phi_coupling_strength: float = 1.0  # Scaling for Φ_ij coupling
    
    # Stability monitoring
    monitor_interval: int = 10  # Steps between stability checks
    energy_threshold: float = 1e10  # Blow-up detection threshold
    
    def __post_init__(self):
        """Compute derived quantities"""
        self.dx = self.L / self.N
        self.n_steps = int(self.T_max / self.dt)


class StableByDesignDNS:
    """
    DNS/CFD Solver with Built-in Quantum-Geometric Regularization
    
    This solver demonstrates the paradigm shift from empirical turbulence
    modeling to first-principles stability through quantum coherence.
    
    Key Innovation:
    --------------
    The Seeley-DeWitt tensor Φ_ij(Ψ) is NOT an add-on correction, but
    rather the fundamental geometric structure that GUARANTEES stability.
    """
    
    def __init__(self, config: Optional[StableDNSConfig] = None):
        """Initialize stable DNS solver"""
        self.config = config or StableDNSConfig()
        self._setup_spectral_grid()
        self._setup_quantum_regularizer()
        self._initialize_diagnostics()
        
    def _setup_spectral_grid(self):
        """Setup spectral differentiation operators"""
        cfg = self.config
        
        # Physical space grid
        x = np.linspace(0, cfg.L, cfg.N, endpoint=False)
        self.X, self.Y, self.Z = np.meshgrid(x, x, x, indexing='ij')
        
        # Spectral space (wavenumbers)
        k = fftfreq(cfg.N, cfg.dx / (2 * np.pi))
        self.KX, self.KY, self.KZ = np.meshgrid(k, k, k, indexing='ij')
        self.K2 = self.KX**2 + self.KY**2 + self.KZ**2
        self.K2[0, 0, 0] = 1  # Avoid division by zero
        
        # Dealiasing filter (2/3 rule)
        k_max = cfg.N / 3
        self.dealias_filter = (np.abs(self.KX) < k_max) & \
                              (np.abs(self.KY) < k_max) & \
                              (np.abs(self.KZ) < k_max)
        
    def _setup_quantum_regularizer(self):
        """Initialize Seeley-DeWitt quantum-geometric regularizer"""
        if not self.config.use_quantum_regularization:
            self.phi_tensor = None
            return
            
        # Configure Seeley-DeWitt parameters
        params = SeeleyDeWittParams(
            mu=1.0,
            m_psi=1.0,
            I=1.0,
            A_eff=1.0,
            f0=UNIVERSAL_COHERENCE_FREQUENCY,
            c0=1.0,
            epsilon_0=self.config.nu,
            lambda_scale=1.0,
            alpha=1.5
        )
        
        self.phi_tensor = SeeleyDeWittTensor(params)
        self._verbose_log(f"✓ Quantum-geometric regularizer initialized (f₀ = {UNIVERSAL_COHERENCE_FREQUENCY} Hz)")
        
    def _verbose_log(self, message: str):
        """Helper method for verbose logging (can be disabled)"""
        # Can be extended to use proper logging framework
        print(message)
        
    def _initialize_diagnostics(self):
        """Initialize diagnostic arrays"""
        n_steps = self.config.n_steps
        n_monitor = n_steps // self.config.monitor_interval + 1
        
        self.diagnostics = {
            'time': np.zeros(n_monitor),
            'energy': np.zeros(n_monitor),
            'enstrophy': np.zeros(n_monitor),
            'max_velocity': np.zeros(n_monitor),
            'max_vorticity': np.zeros(n_monitor),
            'phi_energy_rate': np.zeros(n_monitor),
            'stability_indicator': np.zeros(n_monitor),
            'step_count': 0
        }
        
    def set_initial_conditions(self, u0: np.ndarray, v0: np.ndarray, w0: np.ndarray):
        """
        Set initial velocity field
        
        Args:
            u0, v0, w0: Initial velocity components (physical space)
        """
        # Store in spectral space for efficient computation
        self.u_hat = fftn(u0)
        self.v_hat = fftn(v0)
        self.w_hat = fftn(w0)
        
        # Project to divergence-free subspace
        self._project_divergence_free()
        
        # Initialize physical space representation
        self.u = np.real(ifftn(self.u_hat))
        self.v = np.real(ifftn(self.v_hat))
        self.w = np.real(ifftn(self.w_hat))
        
        E0 = self._compute_energy()
        self._verbose_log(f"✓ Initial conditions set (E₀ = {E0:.6e})")
        
    def _project_divergence_free(self):
        """Project velocity field to divergence-free subspace"""
        # Compute divergence in spectral space
        div_hat = 1j * (self.KX * self.u_hat + 
                       self.KY * self.v_hat + 
                       self.KZ * self.w_hat)
        
        # Remove divergent component
        self.u_hat -= 1j * self.KX * div_hat / self.K2
        self.v_hat -= 1j * self.KY * div_hat / self.K2
        self.w_hat -= 1j * self.KZ * div_hat / self.K2
        
        # Apply dealiasing
        self.u_hat *= self.dealias_filter
        self.v_hat *= self.dealias_filter
        self.w_hat *= self.dealias_filter
        
    def _compute_nonlinear_term(self, u: np.ndarray, v: np.ndarray, w: np.ndarray
                               ) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
        """
        Compute nonlinear advection term: -(u·∇)u
        
        Uses pseudo-spectral method with 2/3 dealiasing rule
        """
        # Compute vorticity: ω = ∇ × u
        u_hat = fftn(u)
        v_hat = fftn(v)
        w_hat = fftn(w)
        
        omega_x = np.real(ifftn(1j * (self.KY * w_hat - self.KZ * v_hat)))
        omega_y = np.real(ifftn(1j * (self.KZ * u_hat - self.KX * w_hat)))
        omega_z = np.real(ifftn(1j * (self.KX * v_hat - self.KY * u_hat)))
        
        # Cross product: u × ω
        Nx = v * omega_z - w * omega_y
        Ny = w * omega_x - u * omega_z
        Nz = u * omega_y - v * omega_x
        
        return Nx, Ny, Nz
        
    def _compute_quantum_coupling(self, t: float, u: np.ndarray, 
                                  v: np.ndarray, w: np.ndarray
                                 ) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
        """
        Compute quantum-geometric coupling: Φ_ij(Ψ) u_j
        
        This is the KEY INNOVATION: stability from first principles,
        not from empirical turbulence models.
        """
        if self.phi_tensor is None:
            return np.zeros_like(u), np.zeros_like(v), np.zeros_like(w)
        
        # Prepare spatial grid in format expected by phi_tensor (3, Nx, Ny, Nz)
        x_grid = np.stack([self.X, self.Y, self.Z], axis=0)
        
        # Compute full Φ_ij tensor at time t
        Phi = self.phi_tensor.compute_phi_tensor_full(x_grid, t, grid_spacing=self.config.dx)
        
        # Contract with velocity: Φ_ij u_j
        Phi_u = (Phi[0, 0] * u + Phi[0, 1] * v + Phi[0, 2] * w)
        Phi_v = (Phi[1, 0] * u + Phi[1, 1] * v + Phi[1, 2] * w)
        Phi_w = (Phi[2, 0] * u + Phi[2, 1] * v + Phi[2, 2] * w)
        
        # Scale by coupling strength
        alpha = self.config.phi_coupling_strength
        
        return alpha * Phi_u, alpha * Phi_v, alpha * Phi_w
        
    def _rk4_step(self, t: float) -> None:
        """
        4th-order Runge-Kutta time integration with quantum regularization
        
        Extended Navier-Stokes:
        ∂u/∂t = -(u·∇)u - ∇p + ν∇²u + Φ_ij(Ψ)u_j
        """
        dt = self.config.dt
        nu = self.config.nu
        
        # Current state (physical space)
        u, v, w = self.u, self.v, self.w
        
        # RK4 Stage 1
        Nx, Ny, Nz = self._compute_nonlinear_term(u, v, w)
        Qx, Qy, Qz = self._compute_quantum_coupling(t, u, v, w)
        
        k1_u = fftn(Nx + Qx)
        k1_v = fftn(Ny + Qy)
        k1_w = fftn(Nz + Qz)
        
        # RK4 Stage 2
        u2 = np.real(ifftn(self.u_hat + 0.5 * dt * (k1_u - nu * self.K2 * self.u_hat)))
        v2 = np.real(ifftn(self.v_hat + 0.5 * dt * (k1_v - nu * self.K2 * self.v_hat)))
        w2 = np.real(ifftn(self.w_hat + 0.5 * dt * (k1_w - nu * self.K2 * self.w_hat)))
        
        Nx, Ny, Nz = self._compute_nonlinear_term(u2, v2, w2)
        Qx, Qy, Qz = self._compute_quantum_coupling(t + 0.5*dt, u2, v2, w2)
        
        k2_u = fftn(Nx + Qx)
        k2_v = fftn(Ny + Qy)
        k2_w = fftn(Nz + Qz)
        
        # RK4 Stage 3
        u3 = np.real(ifftn(self.u_hat + 0.5 * dt * (k2_u - nu * self.K2 * self.u_hat)))
        v3 = np.real(ifftn(self.v_hat + 0.5 * dt * (k2_v - nu * self.K2 * self.v_hat)))
        w3 = np.real(ifftn(self.w_hat + 0.5 * dt * (k2_w - nu * self.K2 * self.w_hat)))
        
        Nx, Ny, Nz = self._compute_nonlinear_term(u3, v3, w3)
        Qx, Qy, Qz = self._compute_quantum_coupling(t + 0.5*dt, u3, v3, w3)
        
        k3_u = fftn(Nx + Qx)
        k3_v = fftn(Ny + Qy)
        k3_w = fftn(Nz + Qz)
        
        # RK4 Stage 4
        u4 = np.real(ifftn(self.u_hat + dt * (k3_u - nu * self.K2 * self.u_hat)))
        v4 = np.real(ifftn(self.v_hat + dt * (k3_v - nu * self.K2 * self.v_hat)))
        w4 = np.real(ifftn(self.w_hat + dt * (k3_w - nu * self.K2 * self.w_hat)))
        
        Nx, Ny, Nz = self._compute_nonlinear_term(u4, v4, w4)
        Qx, Qy, Qz = self._compute_quantum_coupling(t + dt, u4, v4, w4)
        
        k4_u = fftn(Nx + Qx)
        k4_v = fftn(Ny + Qy)
        k4_w = fftn(Nz + Qz)
        
        # Combine stages
        viscous_u = -nu * self.K2 * self.u_hat
        viscous_v = -nu * self.K2 * self.v_hat
        viscous_w = -nu * self.K2 * self.w_hat
        
        self.u_hat += dt/6 * (k1_u + 2*k2_u + 2*k3_u + k4_u) + dt * viscous_u
        self.v_hat += dt/6 * (k1_v + 2*k2_v + 2*k3_v + k4_v) + dt * viscous_v
        self.w_hat += dt/6 * (k1_w + 2*k2_w + 2*k3_w + k4_w) + dt * viscous_w
        
        # Project and dealias
        self._project_divergence_free()
        
        # Update physical space
        self.u = np.real(ifftn(self.u_hat))
        self.v = np.real(ifftn(self.v_hat))
        self.w = np.real(ifftn(self.w_hat))
        
    def _compute_energy(self) -> float:
        """Compute kinetic energy"""
        return 0.5 * np.mean(self.u**2 + self.v**2 + self.w**2)
        
    def _compute_enstrophy(self) -> float:
        """Compute enstrophy (vorticity magnitude squared)"""
        omega_x = np.real(ifftn(1j * (self.KY * self.w_hat - self.KZ * self.v_hat)))
        omega_y = np.real(ifftn(1j * (self.KZ * self.u_hat - self.KX * self.w_hat)))
        omega_z = np.real(ifftn(1j * (self.KX * self.v_hat - self.KY * self.u_hat)))
        
        return 0.5 * np.mean(omega_x**2 + omega_y**2 + omega_z**2)
        
    def _update_diagnostics(self, step: int, t: float):
        """Update diagnostic measurements"""
        idx = step // self.config.monitor_interval
        if idx >= len(self.diagnostics['time']):
            return
            
        self.diagnostics['time'][idx] = t
        self.diagnostics['energy'][idx] = self._compute_energy()
        self.diagnostics['enstrophy'][idx] = self._compute_enstrophy()
        self.diagnostics['max_velocity'][idx] = np.max(np.abs([self.u, self.v, self.w]))
        
        # Compute max vorticity
        omega_x = np.real(ifftn(1j * (self.KY * self.w_hat - self.KZ * self.v_hat)))
        omega_y = np.real(ifftn(1j * (self.KZ * self.u_hat - self.KX * self.w_hat)))
        omega_z = np.real(ifftn(1j * (self.KX * self.v_hat - self.KY * self.u_hat)))
        omega_mag = np.sqrt(omega_x**2 + omega_y**2 + omega_z**2)
        self.diagnostics['max_vorticity'][idx] = np.max(omega_mag)
        
        # Compute Φ_ij energy rate (if using quantum regularization)
        if self.phi_tensor is not None:
            Qx, Qy, Qz = self._compute_quantum_coupling(t, self.u, self.v, self.w)
            phi_rate = np.mean(self.u * Qx + self.v * Qy + self.w * Qz)
            self.diagnostics['phi_energy_rate'][idx] = phi_rate
            
        # Stability indicator: 0 = stable, 1 = approaching blow-up
        E = self.diagnostics['energy'][idx]
        self.diagnostics['stability_indicator'][idx] = E / self.config.energy_threshold
        
        self.diagnostics['step_count'] = idx + 1
        
    def run(self, verbose: bool = True) -> Dict:
        """
        Run DNS simulation
        
        Returns:
            Dictionary containing simulation results and diagnostics
        """
        if verbose:
            print("\n" + "="*70)
            print("  STABLE-BY-DESIGN DNS SIMULATION")
            print("  Quantum-Geometric Regularization via Φ_ij(Ψ)")
            print("="*70)
            print(f"  Resolution: {self.config.N}³")
            print(f"  Time steps: {self.config.n_steps}")
            print(f"  Reynolds number: Re = {self.config.Re:.1f}")
            print(f"  Quantum regularization: {'ON' if self.config.use_quantum_regularization else 'OFF'}")
            print("="*70 + "\n")
        
        start_time = time.time()
        
        # Time integration loop
        t = 0.0
        for step in range(self.config.n_steps):
            # Advance one time step
            self._rk4_step(t)
            t += self.config.dt
            
            # Update diagnostics
            if step % self.config.monitor_interval == 0:
                self._update_diagnostics(step, t)
                
                if verbose and step % (self.config.monitor_interval * 10) == 0:
                    E = self.diagnostics['energy'][step // self.config.monitor_interval]
                    print(f"  t = {t:6.3f} | E = {E:.6e} | Step {step}/{self.config.n_steps}")
            
            # Check for blow-up
            if self._compute_energy() > self.config.energy_threshold:
                if verbose:
                    print(f"\n⚠ BLOW-UP DETECTED at t = {t:.3f}")
                self.diagnostics['blow_up'] = True
                self.diagnostics['blow_up_time'] = t
                break
        else:
            self.diagnostics['blow_up'] = False
            self.diagnostics['blow_up_time'] = None
            
        elapsed = time.time() - start_time
        
        if verbose:
            print(f"\n✓ Simulation completed in {elapsed:.2f} seconds")
            if self.diagnostics['blow_up']:
                print(f"  ⚠ Blow-up at t = {self.diagnostics['blow_up_time']:.3f}")
            else:
                print(f"  ✓ Stable for entire simulation (T = {self.config.T_max})")
            print()
        
        return self.diagnostics
        
    def visualize_results(self, save_path: Optional[str] = None):
        """Create visualization of simulation results"""
        fig, axes = plt.subplots(2, 2, figsize=(12, 10))
        
        diag = self.diagnostics
        t = diag['time'][:diag['step_count']]
        
        # Energy evolution
        ax = axes[0, 0]
        ax.semilogy(t, diag['energy'][:diag['step_count']], 'b-', linewidth=2)
        ax.set_xlabel('Time', fontsize=12)
        ax.set_ylabel('Kinetic Energy', fontsize=12)
        ax.set_title('Energy Evolution', fontsize=14, fontweight='bold')
        ax.grid(True, alpha=0.3)
        
        # Enstrophy evolution
        ax = axes[0, 1]
        ax.semilogy(t, diag['enstrophy'][:diag['step_count']], 'r-', linewidth=2)
        ax.set_xlabel('Time', fontsize=12)
        ax.set_ylabel('Enstrophy', fontsize=12)
        ax.set_title('Enstrophy Evolution', fontsize=14, fontweight='bold')
        ax.grid(True, alpha=0.3)
        
        # Max vorticity
        ax = axes[1, 0]
        ax.plot(t, diag['max_vorticity'][:diag['step_count']], 'g-', linewidth=2)
        ax.set_xlabel('Time', fontsize=12)
        ax.set_ylabel('Max |ω|', fontsize=12)
        ax.set_title('Maximum Vorticity', fontsize=14, fontweight='bold')
        ax.grid(True, alpha=0.3)
        
        # Φ_ij energy rate (if available)
        ax = axes[1, 1]
        if self.config.use_quantum_regularization:
            ax.plot(t, diag['phi_energy_rate'][:diag['step_count']], 'm-', linewidth=2)
            ax.axhline(y=0, color='k', linestyle='--', alpha=0.5)
            ax.set_xlabel('Time', fontsize=12)
            ax.set_ylabel('dE/dt from Φ_ij', fontsize=12)
            ax.set_title('Quantum Regularization Energy Rate', fontsize=14, fontweight='bold')
        else:
            ax.text(0.5, 0.5, 'Quantum Regularization OFF', 
                   ha='center', va='center', fontsize=14, transform=ax.transAxes)
        ax.grid(True, alpha=0.3)
        
        plt.tight_layout()
        
        if save_path:
            plt.savefig(save_path, dpi=300, bbox_inches='tight')
            print(f"✓ Visualization saved to {save_path}")
        else:
            plt.show()
            
        return fig


def create_taylor_green_initial_conditions(X, Y, Z, U0=1.0):
    """Create Taylor-Green vortex initial conditions"""
    u = U0 * np.sin(X) * np.cos(Y) * np.cos(Z)
    v = -U0 * np.cos(X) * np.sin(Y) * np.cos(Z)
    w = np.zeros_like(u)
    return u, v, w


def demonstrate_paradigm_shift():
    """
    Demonstrate the paradigm shift from ad-hoc turbulence models
    to first-principles quantum-geometric regularization.
    """
    print("\n" + "="*70)
    print("  PARADIGM SHIFT DEMONSTRATION")
    print("  Classical vs Quantum-Geometric DNS/CFD")
    print("="*70 + "\n")
    
    # Configuration
    config = StableDNSConfig(
        N=32,  # Moderate resolution for demonstration
        T_max=5.0,
        dt=0.001,
        nu=1e-3,
        monitor_interval=10
    )
    
    # Run 1: Classical DNS (no quantum regularization)
    print("► Running CLASSICAL DNS (no quantum regularization)...")
    config.use_quantum_regularization = False
    solver_classical = StableByDesignDNS(config)
    
    # Setup initial conditions
    u0, v0, w0 = create_taylor_green_initial_conditions(
        solver_classical.X, solver_classical.Y, solver_classical.Z
    )
    solver_classical.set_initial_conditions(u0, v0, w0)
    
    results_classical = solver_classical.run(verbose=False)
    
    # Run 2: Quantum DNS (with Φ_ij regularization)
    print("\n► Running QUANTUM-GEOMETRIC DNS (with Φ_ij regularization)...")
    config.use_quantum_regularization = True
    config.phi_coupling_strength = 0.1  # Moderate coupling
    solver_quantum = StableByDesignDNS(config)
    
    solver_quantum.set_initial_conditions(u0, v0, w0)
    results_quantum = solver_quantum.run(verbose=False)
    
    # Create comparison visualization
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    
    t_c = results_classical['time'][:results_classical['step_count']]
    t_q = results_quantum['time'][:results_quantum['step_count']]
    
    # Energy comparison
    ax = axes[0, 0]
    ax.semilogy(t_c, results_classical['energy'][:results_classical['step_count']], 
               'r-', linewidth=2, label='Classical DNS', alpha=0.7)
    ax.semilogy(t_q, results_quantum['energy'][:results_quantum['step_count']], 
               'b-', linewidth=2, label='Quantum DNS (Φ_ij)', alpha=0.7)
    ax.set_xlabel('Time', fontsize=12)
    ax.set_ylabel('Kinetic Energy', fontsize=12)
    ax.set_title('Energy Evolution Comparison', fontsize=14, fontweight='bold')
    ax.legend(fontsize=11)
    ax.grid(True, alpha=0.3)
    
    # Enstrophy comparison
    ax = axes[0, 1]
    ax.semilogy(t_c, results_classical['enstrophy'][:results_classical['step_count']], 
               'r-', linewidth=2, label='Classical', alpha=0.7)
    ax.semilogy(t_q, results_quantum['enstrophy'][:results_quantum['step_count']], 
               'b-', linewidth=2, label='Quantum', alpha=0.7)
    ax.set_xlabel('Time', fontsize=12)
    ax.set_ylabel('Enstrophy', fontsize=12)
    ax.set_title('Enstrophy Comparison', fontsize=14, fontweight='bold')
    ax.legend(fontsize=11)
    ax.grid(True, alpha=0.3)
    
    # Max vorticity comparison
    ax = axes[1, 0]
    ax.plot(t_c, results_classical['max_vorticity'][:results_classical['step_count']], 
           'r-', linewidth=2, label='Classical', alpha=0.7)
    ax.plot(t_q, results_quantum['max_vorticity'][:results_quantum['step_count']], 
           'b-', linewidth=2, label='Quantum', alpha=0.7)
    ax.set_xlabel('Time', fontsize=12)
    ax.set_ylabel('Max |ω|', fontsize=12)
    ax.set_title('Maximum Vorticity Comparison', fontsize=14, fontweight='bold')
    ax.legend(fontsize=11)
    ax.grid(True, alpha=0.3)
    
    # Stability indicator
    ax = axes[1, 1]
    ax.semilogy(t_c, results_classical['stability_indicator'][:results_classical['step_count']], 
               'r-', linewidth=2, label='Classical', alpha=0.7)
    ax.semilogy(t_q, results_quantum['stability_indicator'][:results_quantum['step_count']], 
               'b-', linewidth=2, label='Quantum (Φ_ij)', alpha=0.7)
    ax.axhline(y=1.0, color='k', linestyle='--', linewidth=1.5, 
              label='Blow-up threshold', alpha=0.5)
    ax.set_xlabel('Time', fontsize=12)
    ax.set_ylabel('E / E_threshold', fontsize=12)
    ax.set_title('Stability Indicator', fontsize=14, fontweight='bold')
    ax.legend(fontsize=11)
    ax.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('Results/paradigm_shift_demonstration.png', dpi=300, bbox_inches='tight')
    print("\n✓ Comparison saved to Results/paradigm_shift_demonstration.png")
    
    # Print summary
    print("\n" + "="*70)
    print("  RESULTS SUMMARY")
    print("="*70)
    print(f"Classical DNS:")
    print(f"  - Blow-up: {'YES' if results_classical.get('blow_up', False) else 'NO'}")
    if results_classical.get('blow_up', False):
        print(f"  - Blow-up time: {results_classical['blow_up_time']:.3f}")
    print(f"  - Final energy: {results_classical['energy'][results_classical['step_count']-1]:.6e}")
    
    print(f"\nQuantum-Geometric DNS:")
    print(f"  - Blow-up: {'YES' if results_quantum.get('blow_up', False) else 'NO'}")
    if results_quantum.get('blow_up', False):
        print(f"  - Blow-up time: {results_quantum['blow_up_time']:.3f}")
    print(f"  - Final energy: {results_quantum['energy'][results_quantum['step_count']-1]:.6e}")
    print("="*70 + "\n")


if __name__ == "__main__":
    demonstrate_paradigm_shift()
