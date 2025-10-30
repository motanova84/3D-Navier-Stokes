"""
Solver DNS para sistema Ψ-NS con escala dual-límite

Este módulo implementa un solver pseudo-espectral para las ecuaciones 
de Navier-Stokes 3D con fuerza oscilatoria de regularización.
"""

import numpy as np
from scipy import fft
from dataclasses import dataclass
from typing import Tuple, Dict, List


@dataclass
class DualLimitScaling:
    """Parámetros de escala dual-límite"""
    lambda_val: float = 1.0      # Intensidad base
    a: float = 40.0         # Amplitud (δ* = 40.528)
    alpha: float = 2.0          # Exponente de escala (alpha > 1)
    f0_base: float = 141.7001  # Frecuencia QCAL
    
    def epsilon(self, f0: float) -> float:
        """Calcular epsilon = lambda_valf0^(-alpha)"""
        return self.lambda_val * f0**(-self.alpha)
    
    def amplitude(self, f0: float) -> float:
        """Calcular A = af0"""
        return self.a * f0


class PsiNSSolver:
    """Solver DNS para sistema Ψ-NS con escala dual"""
    
    def __init__(self, N: int = 256, L: float = 2*np.pi, Re: float = 1000):
        """
        Inicializar solver
        
        Args:
            N: Número de puntos de malla por dimensión
            L: Tamaño del dominio
            Re: Número de Reynolds
        """
        self.N = N
        self.L = L
        self.Re = Re
        self.nu = 1.0 / Re  # Viscosidad
        self.scaling = DualLimitScaling()
        
        # Malla espectral
        k = np.fft.fftfreq(N, L/N) * 2 * np.pi
        self.kx, self.ky, self.kz = np.meshgrid(k, k, k, indexing='ij')
        self.k2 = self.kx**2 + self.ky**2 + self.kz**2
        self.k2[0, 0, 0] = 1.0  # Evitar división por cero
        
        # Proyección para incompresibilidad
        self.P = self._projection_operator()
    
    def _projection_operator(self) -> np.ndarray:
        """Crear operador de proyección P_k = I - k⊗k/|k|²"""
        P = np.zeros((3, 3, self.N, self.N, self.N))
        for i in range(3):
            for j in range(3):
                if i == j:
                    P[i, j] = 1.0
                k_components = [self.kx, self.ky, self.kz]
                P[i, j] -= k_components[i] * k_components[j] / self.k2
        return P
    
    def oscillatory_force(self, x: np.ndarray, y: np.ndarray, z: np.ndarray, 
                         t: float, f0: float) -> np.ndarray:
        """
        Fuerza oscilatoria epsilonnablaPhi con escala dual
        
        Args:
            x, y, z: Coordenadas espaciales (grids)
            t: Tiempo
            f0: Frecuencia
            
        Returns:
            Vector de fuerza [fx, fy, fz]
        """
        epsilon = self.scaling.epsilon(f0)
        A = self.scaling.amplitude(f0)
        
        # Gradiente de fase espacial (ejemplo: |nablaφ| ≥ c0 > 0)
        nablaφ_x = np.cos(x) * np.sin(y)
        nablaφ_y = np.sin(x) * np.cos(z)
        nablaφ_z = np.cos(y) * np.sin(z)
        
        # Normalización para asegurar |nablaφ| ≥ c0
        nablaφ_norm = np.sqrt(nablaφ_x**2 + nablaφ_y**2 + nablaφ_z**2 + 1e-12)
        c0 = 1.0
        nablaφ_x *= c0 / (nablaφ_norm + 1e-12)
        nablaφ_y *= c0 / (nablaφ_norm + 1e-12)
        nablaφ_z *= c0 / (nablaφ_norm + 1e-12)
        
        # Potencial oscilatorio
        Phi_amp = A * np.sin(2*np.pi*f0*t + x + y + z)
        
        return epsilon * Phi_amp * np.array([nablaφ_x, nablaφ_y, nablaφ_z])
    
    def vorticity(self, u_field: np.ndarray) -> np.ndarray:
        """
        Calcular vorticidad omega = nabla × u en espacio de Fourier
        
        Args:
            u_field: Campo de velocidad [3, N, N, N]
            
        Returns:
            Campo de vorticidad [3, N, N, N]
        """
        # Transformada de Fourier
        u_hat = np.array([fft.fftn(u_field[i]) for i in range(3)])
        
        # Vorticidad en espacio de Fourier: omega_hat = ik × u_hat
        omega_hat = np.zeros_like(u_hat, dtype=complex)
        omega_hat[0] = 1j * (self.ky * u_hat[2] - self.kz * u_hat[1])
        omega_hat[1] = 1j * (self.kz * u_hat[0] - self.kx * u_hat[2])
        omega_hat[2] = 1j * (self.kx * u_hat[1] - self.ky * u_hat[0])
        
        # Transformada inversa
        omega = np.array([fft.ifftn(omega_hat[i]).real for i in range(3)])
        return omega
    
    def compute_misalignment(self, u_field: np.ndarray) -> Tuple[float, float]:
        """
        Calcular defecto de desalineamiento delta(t)
        
        Args:
            u_field: Campo de velocidad [3, N, N, N]
            
        Returns:
            (delta_mean, delta_std): Media y desviación estándar de delta
        """
        # Gradiente de velocidad
        du_dx = np.gradient(u_field, axis=1)
        du_dy = np.gradient(u_field, axis=2)
        du_dz = np.gradient(u_field, axis=3)
        
        # Tensor de deformación S = 1/2(nablau + nablauᵀ)
        S = np.zeros((3, 3, self.N, self.N, self.N))
        grads = [du_dx, du_dy, du_dz]
        
        for i in range(3):
            for j in range(3):
                S[i, j] = 0.5 * (grads[j][i] + grads[i][j])
        
        # Vorticidad
        omega = self.vorticity(u_field)
        
        # Calcular Somega
        Somega = np.zeros_like(omega)
        for i in range(3):
            for j in range(3):
                Somega[i] += S[i, j] * omega[j]
        
        # Producto Somega · omega
        Somega_dot_omega = np.sum(Somega * omega, axis=0)
        
        # Normas
        S_norm = np.sqrt(np.sum(S**2, axis=(0, 1)))
        omega_norm_sq = np.sum(omega**2, axis=0)
        
        # Defecto delta = 1 - (Somega·omega)/(‖S‖‖omega‖²)
        delta = 1 - Somega_dot_omega / (S_norm * omega_norm_sq + 1e-12)
        
        return np.mean(delta), np.std(delta)
    
    def initialize_turbulent_field(self) -> np.ndarray:
        """
        Inicializar campo de velocidad turbulento
        
        Returns:
            Campo de velocidad inicial [3, N, N, N]
        """
        # Taylor-Green vortex como condición inicial
        x = np.linspace(0, self.L, self.N, endpoint=False)
        y = np.linspace(0, self.L, self.N, endpoint=False)
        z = np.linspace(0, self.L, self.N, endpoint=False)
        X, Y, Z = np.meshgrid(x, y, z, indexing='ij')
        
        u = np.zeros((3, self.N, self.N, self.N))
        u[0] = np.sin(X) * np.cos(Y) * np.cos(Z)
        u[1] = -np.cos(X) * np.sin(Y) * np.cos(Z)
        u[2] = 0.0
        
        return u
    
    def time_step(self, u: np.ndarray, t: float, f0: float, dt: float = 0.01) -> np.ndarray:
        """
        Avanzar un paso temporal usando esquema pseudo-espectral
        
        Args:
            u: Campo de velocidad actual
            t: Tiempo actual
            f0: Frecuencia
            dt: Paso temporal
            
        Returns:
            Campo de velocidad actualizado
        """
        # Malla espacial
        x = np.linspace(0, self.L, self.N, endpoint=False)
        y = np.linspace(0, self.L, self.N, endpoint=False)
        z = np.linspace(0, self.L, self.N, endpoint=False)
        X, Y, Z = np.meshgrid(x, y, z, indexing='ij')
        
        # Fuerza oscilatoria
        f_osc = self.oscillatory_force(X, Y, Z, t, f0)
        
        # Transformada de Fourier
        u_hat = np.array([fft.fftn(u[i]) for i in range(3)])
        f_hat = np.array([fft.fftn(f_osc[i]) for i in range(3)])
        
        # Término no lineal (u·nabla)u en espacio físico
        du_dx = np.array([fft.ifftn(1j * self.kx * u_hat[i]).real for i in range(3)])
        du_dy = np.array([fft.ifftn(1j * self.ky * u_hat[i]).real for i in range(3)])
        du_dz = np.array([fft.ifftn(1j * self.kz * u_hat[i]).real for i in range(3)])
        
        nonlinear = np.zeros_like(u)
        nonlinear[0] = u[0]*du_dx[0] + u[1]*du_dy[0] + u[2]*du_dz[0]
        nonlinear[1] = u[0]*du_dx[1] + u[1]*du_dy[1] + u[2]*du_dz[1]
        nonlinear[2] = u[0]*du_dx[2] + u[1]*du_dy[2] + u[2]*du_dz[2]
        
        nonlinear_hat = np.array([fft.fftn(nonlinear[i]) for i in range(3)])
        
        # Actualización en espacio de Fourier (Euler explícito)
        u_hat_new = u_hat + dt * (f_hat - nonlinear_hat - self.nu * self.k2 * u_hat)
        
        # Proyección para incompresibilidad
        k_dot_u = self.kx * u_hat_new[0] + self.ky * u_hat_new[1] + self.kz * u_hat_new[2]
        u_hat_new[0] -= self.kx * k_dot_u / self.k2
        u_hat_new[1] -= self.ky * k_dot_u / self.k2
        u_hat_new[2] -= self.kz * k_dot_u / self.k2
        
        # Transformada inversa
        u_new = np.array([fft.ifftn(u_hat_new[i]).real for i in range(3)])
        
        return u_new
    
    def run_simulation(self, f0_values: List[float], T_max: float = 10.0, 
                      dt: float = 0.01) -> Dict:
        """
        Ejecutar simulaciones para diferentes f0
        
        Args:
            f0_values: Lista de frecuencias a simular
            T_max: Tiempo máximo de simulación
            dt: Paso temporal
            
        Returns:
            Diccionario con resultados para cada f0
        """
        results = {}
        
        for f0 in f0_values:
            print(f"Simulando f0 = {f0:.1f} Hz")
            
            # Inicializar campo de velocidad
            u = self.initialize_turbulent_field()
            
            delta_history = []
            omega_inf_history = []
            
            n_steps = int(T_max / dt)
            for step in range(n_steps):
                t = step * dt
                
                # Paso temporal
                u = self.time_step(u, t, f0, dt)
                
                # Métricas cada 10 pasos
                if step % 10 == 0:
                    delta_mean, delta_std = self.compute_misalignment(u)
                    omega = self.vorticity(u)
                    omega_inf = np.max(np.sqrt(np.sum(omega**2, axis=0)))
                    
                    delta_history.append(delta_mean)
                    omega_inf_history.append(omega_inf)
            
            results[f0] = {
                'delta': np.array(delta_history),
                'omega_inf': np.array(omega_inf_history),
                'delta_star': np.mean(delta_history[-10:]) if len(delta_history) > 10 else np.mean(delta_history)
            }
        
        return results


if __name__ == "__main__":
    # Ejemplo de uso
    solver = PsiNSSolver(N=64, Re=1000)
    results = solver.run_simulation([100.0, 200.0], T_max=5.0)
    
    for f0, data in results.items():
        print(f"\nResultados para f0 = {f0} Hz:")
        print(f"  delta* = {data['delta_star']:.4f}")
        print(f"  omega_inf final = {data['omega_inf'][-1]:.4f}")
