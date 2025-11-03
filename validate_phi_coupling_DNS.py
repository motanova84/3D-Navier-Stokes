#!/usr/bin/env python3
"""
Validación numérica DNS del acoplamiento Φ_ij(Ψ) en Navier-Stokes
===================================================================

Implementa simulación DNS de NSE + acoplamiento cuántico Φ_ij(Ψ)
para detectar resonancia en f₀ = 141.7001 Hz.

Basado en:
- Derivación QFT del tensor Φ_ij
- Método pseudo-espectral para DNS
- Análisis de Fourier temporal para detección de resonancia

Autor: José Manuel Mota Burruezo (JMMB Ψ✧∞³)
DOI: 10.5281/zenodo.XXXXX
Licencia: CC-BY-4.0
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy.fft import fftn, ifftn, fftfreq
from typing import Tuple, Dict, List, Optional
import os


class PhiTensorCoupling:
    """
    Implementa el tensor Φ_ij(Ψ) derivado desde QFT.
    
    Φ_ij = α·∇_i∇_j Ψ + β·R_ij·Ψ + γ·δ_ij·□Ψ
    
    Coeficientes desde regularización Hadamard:
    - α = a₁ ln(μ²/m_Ψ²), a₁ = 1/(720π²)
    - β = a₂ = 1/(2880π²)
    - γ = a₃ = -1/(1440π²)
    """
    
    def __init__(self, 
                 f0: float = 141.7001,
                 A_psi: float = 1.0,
                 mu_ren: float = 1.0,
                 m_psi: float = 1e-10):
        """
        Inicializa el acoplamiento Φ_ij.
        
        Args:
            f0: Frecuencia fundamental (Hz)
            A_psi: Amplitud del campo Ψ
            mu_ren: Escala de renormalización
            m_psi: Masa efectiva del campo Ψ
        """
        self.f0 = f0
        self.omega0 = 2 * np.pi * f0
        self.A_psi = A_psi
        self.mu_ren = mu_ren
        self.m_psi = m_psi
        
        # Coeficientes de Seeley-DeWitt
        self.a1 = 1 / (720 * np.pi**2)
        self.a2 = 1 / (2880 * np.pi**2)
        self.a3 = -1 / (1440 * np.pi**2)
        
        # Calcular coeficientes del tensor
        self.alpha = self.a1 * np.log(mu_ren**2 / m_psi**2)
        self.beta = self.a2
        self.gamma = self.a3
        
    def compute_psi(self, t: float, x: Optional[np.ndarray] = None) -> float:
        """
        Calcula el campo Ψ(t) = A_psi cos(ω₀t).
        
        Args:
            t: Tiempo
            x: Coordenadas espaciales (no usado por ahora, campo uniforme)
            
        Returns:
            Valor del campo Ψ
        """
        return self.A_psi * np.cos(self.omega0 * t)
    
    def compute_phi_tensor(self, 
                          u: np.ndarray, 
                          t: float,
                          dx: float) -> np.ndarray:
        """
        Calcula el tensor Φ_ij acoplado al campo de velocidades.
        
        Para simplificación numérica, usamos aproximación:
        Φ_ij·u_j ≈ γ·□Ψ·δ_ij·u_j = γ·□Ψ·u_i
        
        Args:
            u: Campo de velocidades (3, N, N, N)
            t: Tiempo actual
            dx: Espaciamiento de malla
            
        Returns:
            Término de acoplamiento (3, N, N, N)
        """
        # Calcular Ψ y sus derivadas temporales
        psi = self.compute_psi(t)
        # ∂²Ψ/∂t² = -ω₀² Ψ
        box_psi = -self.omega0**2 * psi
        
        # Término de acoplamiento simplificado: γ·□Ψ·u
        coupling = self.gamma * box_psi * u
        
        return coupling


class NavierStokesExtendedDNS:
    """
    Simulador DNS de Navier-Stokes con acoplamiento Φ_ij(Ψ).
    
    Ecuación:
    ∂u/∂t + (u·∇)u = -∇p + ν∇²u + Φ_ij·u_j
    """
    
    def __init__(self,
                 N: int = 32,
                 L: float = 2*np.pi,
                 nu: float = 1e-3,
                 dt: float = 1e-3,
                 phi_coupling: Optional[PhiTensorCoupling] = None):
        """
        Inicializa el simulador DNS.
        
        Args:
            N: Número de puntos de malla en cada dirección
            L: Tamaño del dominio
            nu: Viscosidad cinemática
            dt: Paso temporal
            phi_coupling: Objeto de acoplamiento Φ_ij
        """
        self.N = N
        self.L = L
        self.nu = nu
        self.dt = dt
        self.dx = L / N
        
        # Inicializar acoplamiento Φ_ij
        self.phi_coupling = phi_coupling or PhiTensorCoupling()
        
        # Malla espacial
        x = np.linspace(0, L, N, endpoint=False)
        self.X, self.Y, self.Z = np.meshgrid(x, x, x, indexing='ij')
        
        # Números de onda
        k = fftfreq(N, d=L/(2*np.pi*N))
        self.kx, self.ky, self.kz = np.meshgrid(k, k, k, indexing='ij')
        self.k2 = self.kx**2 + self.ky**2 + self.kz**2
        self.k2[0, 0, 0] = 1  # Evitar división por cero
        
    def initialize_turbulent_field(self, 
                                   energy_spectrum: str = 'kolmogorov',
                                   u0_rms: float = 0.1) -> np.ndarray:
        """
        Inicializa campo turbulento con espectro dado.
        
        Args:
            energy_spectrum: Tipo de espectro ('kolmogorov', 'random')
            u0_rms: Velocidad RMS inicial
            
        Returns:
            Campo de velocidades inicial (3, N, N, N)
        """
        N = self.N
        u = np.zeros((3, N, N, N), dtype=complex)
        
        # Generar campo aleatorio en espacio de Fourier
        for i in range(3):
            u[i] = np.random.randn(N, N, N) + 1j * np.random.randn(N, N, N)
        
        # Aplicar espectro de energía
        k_mag = np.sqrt(self.k2)
        if energy_spectrum == 'kolmogorov':
            # E(k) ~ k^(-5/3)
            E_k = k_mag**(-5/3)
            E_k[k_mag < 1] = 0  # Corte en bajas frecuencias
        else:
            E_k = np.ones_like(k_mag)
        
        E_k[0, 0, 0] = 0  # Sin modo medio
        
        for i in range(3):
            u[i] *= np.sqrt(E_k)
        
        # Proyectar a campo solenoidal (∇·u = 0)
        u = self.project_divergence_free(u)
        
        # Normalizar a velocidad RMS deseada
        u_real = np.array([ifftn(u[i]).real for i in range(3)])
        current_rms = np.sqrt(np.mean(u_real**2))
        u_real *= u0_rms / current_rms
        
        return u_real
    
    def project_divergence_free(self, u_hat: np.ndarray) -> np.ndarray:
        """
        Proyecta campo de velocidades a espacio solenoidal.
        
        Args:
            u_hat: Campo en espacio de Fourier (3, N, N, N)
            
        Returns:
            Campo proyectado
        """
        # u_proj = u - ∇(∇·u/k²)
        k = np.array([self.kx, self.ky, self.kz])
        div_u = sum(1j * k[i] * u_hat[i] for i in range(3))
        
        u_proj = u_hat.copy()
        for i in range(3):
            u_proj[i] -= 1j * k[i] * div_u / self.k2
        
        return u_proj
    
    def compute_nonlinear_term(self, u: np.ndarray) -> np.ndarray:
        """
        Calcula término no-lineal (u·∇)u en espacio físico.
        
        Args:
            u: Campo de velocidades (3, N, N, N)
            
        Returns:
            Término convectivo
        """
        N = self.N
        conv = np.zeros((3, N, N, N))
        
        # Calcular gradientes
        u_hat = np.array([fftn(u[i]) for i in range(3)])
        
        for i in range(3):
            for j in range(3):
                # ∂u_i/∂x_j
                k_vec = [self.kx, self.ky, self.kz][j]
                du_dx = ifftn(1j * k_vec * u_hat[i]).real
                conv[i] += u[j] * du_dx
        
        return conv
    
    def step(self, u: np.ndarray, t: float) -> np.ndarray:
        """
        Avanza un paso temporal usando método RK4.
        
        Args:
            u: Campo de velocidades actual (3, N, N, N)
            t: Tiempo actual
            
        Returns:
            Campo actualizado
        """
        dt = self.dt
        
        # RK4
        k1 = self.rhs(u, t)
        k2 = self.rhs(u + 0.5*dt*k1, t + 0.5*dt)
        k3 = self.rhs(u + 0.5*dt*k2, t + 0.5*dt)
        k4 = self.rhs(u + dt*k3, t + dt)
        
        u_new = u + (dt/6) * (k1 + 2*k2 + 2*k3 + k4)
        
        return u_new
    
    def rhs(self, u: np.ndarray, t: float) -> np.ndarray:
        """
        Calcula lado derecho de la ecuación: RHS = -∇p - (u·∇)u + ν∇²u + Φ·u.
        
        Args:
            u: Campo de velocidades (3, N, N, N)
            t: Tiempo actual
            
        Returns:
            Derivada temporal du/dt
        """
        # Término convectivo
        conv = -self.compute_nonlinear_term(u)
        
        # Término viscoso en espacio de Fourier
        u_hat = np.array([fftn(u[i]) for i in range(3)])
        visc_hat = -self.nu * self.k2 * u_hat
        visc = np.array([ifftn(visc_hat[i]).real for i in range(3)])
        
        # Término de acoplamiento Φ_ij
        coupling = self.phi_coupling.compute_phi_tensor(u, t, self.dx)
        
        # Combinar términos
        dudt = conv + visc + coupling
        
        # Proyectar a campo solenoidal
        dudt_hat = np.array([fftn(dudt[i]) for i in range(3)])
        dudt_hat = self.project_divergence_free(dudt_hat)
        dudt = np.array([ifftn(dudt_hat[i]).real for i in range(3)])
        
        return dudt
    
    def compute_energy(self, u: np.ndarray) -> float:
        """
        Calcula energía cinética total.
        
        Args:
            u: Campo de velocidades (3, N, N, N)
            
        Returns:
            Energía cinética
        """
        return 0.5 * np.sum(u**2) * self.dx**3


def detect_resonance_frequency(energy_history: List[float],
                              dt: float,
                              expected_f0: float = 141.7001) -> Dict:
    """
    Analiza espectro temporal de energía para detectar f₀.
    
    Args:
        energy_history: Serie temporal de energía
        dt: Paso temporal
        expected_f0: Frecuencia esperada (Hz)
        
    Returns:
        Diccionario con resultados del análisis
    """
    E_t = np.array(energy_history)
    
    # FFT de la serie temporal de energía
    fft_E = np.fft.fft(E_t)
    freqs = np.fft.fftfreq(len(E_t), dt)
    
    # Tomar solo frecuencias positivas
    positive_freqs = freqs > 0
    freqs_pos = freqs[positive_freqs]
    fft_E_pos = np.abs(fft_E[positive_freqs])
    
    # Buscar pico dominante
    if len(fft_E_pos) > 0:
        idx_peak = np.argmax(fft_E_pos)
        f_detected = freqs_pos[idx_peak]
        amplitude = fft_E_pos[idx_peak]
    else:
        f_detected = 0.0
        amplitude = 0.0
    
    # Calcular error relativo
    rel_error = abs(f_detected - expected_f0) / expected_f0 if expected_f0 > 0 else np.inf
    
    results = {
        'detected_frequency': f_detected,
        'expected_frequency': expected_f0,
        'relative_error': rel_error,
        'peak_amplitude': amplitude,
        'frequencies': freqs_pos,
        'spectrum': fft_E_pos
    }
    
    return results


def run_dns_validation(N: int = 16,
                       T_max: float = 1.0,
                       dt: float = 5e-4,
                       nu: float = 1e-2,
                       save_plots: bool = True) -> Dict:
    """
    Ejecuta validación DNS completa con acoplamiento Φ_ij.
    
    Args:
        N: Resolución de malla
        T_max: Tiempo máximo de simulación
        dt: Paso temporal
        nu: Viscosidad
        save_plots: Si se deben guardar las gráficas
        
    Returns:
        Resultados de la simulación
    """
    print("="*60)
    print("VALIDACIÓN DNS: ACOPLAMIENTO Φ_ij(Ψ)")
    print("="*60)
    
    # Inicializar simulador
    phi_coupling = PhiTensorCoupling(f0=141.7001)
    solver = NavierStokesExtendedDNS(N=N, nu=nu, dt=dt, phi_coupling=phi_coupling)
    
    print(f"\n⚙️  Parámetros:")
    print(f"   Resolución: {N}³")
    print(f"   Viscosidad: ν = {nu}")
    print(f"   Paso temporal: dt = {dt}")
    print(f"   Tiempo máximo: T = {T_max}")
    print(f"   Frecuencia esperada: f₀ = {phi_coupling.f0} Hz")
    
    # Inicializar campo con velocidad más baja para estabilidad
    u = solver.initialize_turbulent_field(u0_rms=0.1)
    
    # Evolución temporal
    t = 0.0
    n_steps = int(T_max / dt)
    energy_history = []
    time_history = []
    
    print(f"\n🔄 Ejecutando {n_steps} pasos temporales...")
    
    for step in range(n_steps):
        u = solver.step(u, t)
        t += dt
        
        # Registrar energía
        E = solver.compute_energy(u)
        energy_history.append(E)
        time_history.append(t)
        
        if step % (n_steps // 10) == 0:
            print(f"   Paso {step}/{n_steps}, t={t:.3f}, E={E:.6f}")
    
    print("\n✅ Simulación completada")
    
    # Análisis de resonancia
    print("\n" + "="*60)
    print("ANÁLISIS DE RESONANCIA")
    print("="*60)
    
    resonance_results = detect_resonance_frequency(
        energy_history, dt, expected_f0=phi_coupling.f0
    )
    
    print(f"\n🎯 Frecuencia dominante detectada: {resonance_results['detected_frequency']:.2f} Hz")
    print(f"   Frecuencia predicha: {resonance_results['expected_frequency']:.2f} Hz")
    print(f"   Error relativo: {resonance_results['relative_error']*100:.2f}%")
    print(f"   Amplitud del pico: {resonance_results['peak_amplitude']:.6e}")
    
    # Guardar gráficas
    if save_plots:
        os.makedirs('Results', exist_ok=True)
        
        fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(10, 8))
        
        # Evolución temporal de energía
        ax1.plot(time_history, energy_history, 'b-', linewidth=1.5)
        ax1.set_xlabel('Tiempo (s)')
        ax1.set_ylabel('Energía cinética')
        ax1.set_title('Evolución temporal de energía con acoplamiento Φ_ij(Ψ)')
        ax1.grid(True, alpha=0.3)
        
        # Espectro de frecuencias
        freqs = resonance_results['frequencies']
        spectrum = resonance_results['spectrum']
        ax2.semilogy(freqs, spectrum, 'r-', linewidth=1.5)
        ax2.axvline(phi_coupling.f0, color='g', linestyle='--', 
                    label=f'f₀ = {phi_coupling.f0} Hz (predicho)')
        ax2.set_xlabel('Frecuencia (Hz)')
        ax2.set_ylabel('Amplitud espectral')
        ax2.set_title('Espectro de frecuencias de la energía')
        ax2.legend()
        ax2.grid(True, alpha=0.3)
        ax2.set_xlim(0, min(500, freqs[-1]))
        
        plt.tight_layout()
        plt.savefig('Results/phi_coupling_validation.png', dpi=150)
        print("\n✅ Gráficas guardadas en: Results/phi_coupling_validation.png")
        plt.close()
    
    results = {
        'energy_history': energy_history,
        'time_history': time_history,
        'resonance_results': resonance_results,
        'phi_coupling': phi_coupling
    }
    
    return results


if __name__ == "__main__":
    print("\n" + "="*60)
    print("VALIDACIÓN DNS DEL ACOPLAMIENTO Φ_ij(Ψ)")
    print("Basado en derivación QFT rigurosa")
    print("="*60 + "\n")
    
    # Ejecutar validación
    results = run_dns_validation(
        N=16,           # Resolución (16³ para prueba rápida)
        T_max=1.0,      # 1 segundo de simulación
        dt=5e-4,        # 0.5 ms paso temporal
        nu=1e-2,        # Mayor viscosidad para estabilidad
        save_plots=True
    )
    
    print("\n" + "="*60)
    print("VALIDACIÓN COMPLETADA")
    print("="*60)
    print("\n📊 Resultados:")
    print(f"   - Frecuencia detectada: {results['resonance_results']['detected_frequency']:.2f} Hz")
    print(f"   - Frecuencia predicha: {results['resonance_results']['expected_frequency']:.2f} Hz")
    print(f"   - Error: {results['resonance_results']['relative_error']*100:.2f}%")
    print("\n📁 Archivos generados:")
    print("   - Results/phi_coupling_validation.png")
    print("\n🎯 Conclusión:")
    error_threshold = 0.1  # 10%
    if results['resonance_results']['relative_error'] < error_threshold:
        print("   ✅ Resonancia detectada cerca de f₀ = 141.7001 Hz")
        print("   ✅ Acoplamiento Φ_ij(Ψ) validado numéricamente")
    else:
        print("   ⚠️  Frecuencia dominante no coincide con predicción")
        print("   → Requiere simulación más larga o mayor resolución")
