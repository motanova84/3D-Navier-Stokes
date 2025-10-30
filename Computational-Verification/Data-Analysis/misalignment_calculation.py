"""
Herramientas para cálculo de defecto de desalineamiento
"""

import json
import numpy as np
from typing import Tuple, Dict
from scipy import fft


def compute_strain_tensor(u_field: np.ndarray, dx: float = 1.0) -> np.ndarray:
    """
    Calcular tensor de deformación S = 1/2(nablau + nablauᵀ)
    
    Args:
        u_field: Campo de velocidad [3, Nx, Ny, Nz]
        dx: Espaciado de malla
        
    Returns:
        Tensor S [3, 3, Nx, Ny, Nz]
    """
    N = u_field.shape[1]
    S = np.zeros((3, 3, N, N, N))
    
    # Gradientes de velocidad
    du_dx = np.gradient(u_field, dx, axis=1)
    du_dy = np.gradient(u_field, dx, axis=2)
    du_dz = np.gradient(u_field, dx, axis=3)
    
    grads = [du_dx, du_dy, du_dz]
    
    # S_ij = 1/2(∂u_i/∂x_j + ∂u_j/∂x_i)
    for i in range(3):
        for j in range(3):
            S[i, j] = 0.5 * (grads[j][i] + grads[i][j])
    
    return S


def compute_vorticity_from_velocity(u_field: np.ndarray, dx: float = 1.0) -> np.ndarray:
    """
    Calcular vorticidad omega = nabla × u
    
    Args:
        u_field: Campo de velocidad [3, Nx, Ny, Nz]
        dx: Espaciado de malla
        
    Returns:
        Campo de vorticidad [3, Nx, Ny, Nz]
    """
    omega = np.zeros_like(u_field)
    
    # omega_x = ∂u_z/∂y - ∂u_y/∂z
    omega[0] = (np.gradient(u_field[2], dx, axis=1) - 
            np.gradient(u_field[1], dx, axis=2))
    
    # omega_y = ∂u_x/∂z - ∂u_z/∂x
    omega[1] = (np.gradient(u_field[0], dx, axis=2) - 
            np.gradient(u_field[2], dx, axis=0))
    
    # omega_z = ∂u_y/∂x - ∂u_x/∂y
    omega[2] = (np.gradient(u_field[1], dx, axis=0) - 
            np.gradient(u_field[0], dx, axis=1))
    
    return omega


def compute_misalignment_field(S: np.ndarray, omega: np.ndarray) -> np.ndarray:
    """
    Calcular campo de defecto de desalineamiento delta(x)
    
    Args:
        S: Tensor de deformación [3, 3, Nx, Ny, Nz]
        omega: Vorticidad [3, Nx, Ny, Nz]
        
    Returns:
        Campo delta [Nx, Ny, Nz]
    """
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
    
    # delta = 1 - (Somega·omega)/(‖S‖‖omega‖²)
    # Evitar división por cero
    denominator = S_norm * omega_norm_sq + 1e-12
    delta = 1 - Somega_dot_omega / denominator
    
    # Clamp para estabilidad numérica
    delta = np.clip(delta, -1.0, 2.0)
    
    return delta


def compute_alignment_angle(S: np.ndarray, omega: np.ndarray) -> np.ndarray:
    """
    Calcular ángulo de desalineamiento theta entre Somega y omega
    
    Args:
        S: Tensor de deformación
        omega: Vorticidad
        
    Returns:
        Ángulo theta en radianes [Nx, Ny, Nz]
    """
    # Calcular Somega
    Somega = np.zeros_like(omega)
    for i in range(3):
        for j in range(3):
            Somega[i] += S[i, j] * omega[j]
    
    # cos(theta) = (Somega·omega)/(‖Somega‖‖omega‖)
    Somega_dot_omega = np.sum(Somega * omega, axis=0)
    Somega_norm = np.sqrt(np.sum(Somega**2, axis=0))
    omega_norm = np.sqrt(np.sum(omega**2, axis=0))
    
    cos_theta = Somega_dot_omega / (Somega_norm * omega_norm + 1e-12)
    cos_theta = np.clip(cos_theta, -1.0, 1.0)
    
    theta = np.arccos(cos_theta)
    
    return theta


def spatial_statistics(field: np.ndarray) -> Dict[str, float]:
    """
    Calcular estadísticas espaciales de un campo
    
    Args:
        field: Campo escalar [Nx, Ny, Nz]
        
    Returns:
        Diccionario con estadísticas
    """
    stats = {
        'mean': np.mean(field),
        'std': np.std(field),
        'min': np.min(field),
        'max': np.max(field),
        'median': np.median(field),
        'q25': np.percentile(field, 25),
        'q75': np.percentile(field, 75)
    }
    
    return stats


def compute_delta_star_from_history(delta_history: np.ndarray, 
                                 fraction: float = 0.2) -> Tuple[float, float]:
    """
    Calcular delta* como promedio de la parte final de la historia
    
    Args:
        delta_history: Historia temporal de delta [n_times]
        fraction: Fracción final a promediar
        
    Returns:
        (delta_star, std_delta_star)
    """
    n_end = max(1, int(len(delta_history) * fraction))
    delta_star = np.mean(delta_history[-n_end:])
    std_delta_star = np.std(delta_history[-n_end:])
    
    return delta_star, std_delta_star


def spectral_analysis_misalignment(delta_field: np.ndarray) -> Dict:
    """
    Análisis espectral del campo de desalineamiento
    
    Args:
        delta_field: Campo de desalineamiento [Nx, Ny, Nz]
        
    Returns:
        Análisis espectral
    """
    # FFT 3D
    delta_hat = fft.fftn(delta_field)
    delta_spectrum = np.abs(delta_hat)**2
    
    N = delta_field.shape[0]
    k = np.fft.fftfreq(N) * N
    kx, ky, kz = np.meshgrid(k, k, k, indexing='ij')
    k_mag = np.sqrt(kx**2 + ky**2 + kz**2)
    
    # Espectro radial
    k_bins = np.arange(0, N//2)
    E_k = np.zeros_like(k_bins, dtype=float)
    
    for i, k_val in enumerate(k_bins):
        mask = (k_mag >= k_val) & (k_mag < k_val + 1)
        E_k[i] = np.sum(delta_spectrum[mask]) if np.any(mask) else 0
    
    analysis = {
        'k_bins': k_bins,
        'E_k': E_k,
        'total_energy': np.sum(delta_spectrum),
        'peak_k': k_bins[np.argmax(E_k)] if len(E_k) > 0 else 0
    }
    
    return analysis


def compute_enstrophy(omega: np.ndarray, dx: float = 1.0) -> float:
    """
    Calcular enstrofia total Omega = 1/2 ∫omega² dx
    
    Args:
        omega: Vorticidad [3, Nx, Ny, Nz]
        dx: Espaciado de malla
        
    Returns:
        Enstrofia total
    """
    omega_sq = np.sum(omega**2, axis=0)
    Omega = 0.5 * np.sum(omega_sq) * dx**3
    
    return Omega


def compute_strain_enstrophy_correlation(S: np.ndarray, omega: np.ndarray) -> float:
    """
    Calcular correlación entre deformación y enstrofia
    
    Args:
        S: Tensor de deformación
        omega: Vorticidad
        
    Returns:
        Coeficiente de correlación
    """
    S_norm = np.sqrt(np.sum(S**2, axis=(0, 1)))
    omega_norm = np.sqrt(np.sum(omega**2, axis=0))
    
    # Aplanar para correlación
    S_flat = S_norm.flatten()
    omega_flat = omega_norm.flatten()
    
    # Correlación de Pearson
    correlation = np.corrcoef(S_flat, omega_flat)[0, 1]
    
    return correlation


class MisalignmentCalculator:
    """Calculadora completa de defecto de desalineamiento"""
    
    def __init__(self, dx: float = 1.0):
        """
        Inicializar calculadora
        
        Args:
            dx: Espaciado de malla
        """
        self.dx = dx
    
    def full_analysis(self, u_field: np.ndarray) -> Dict:
        """
        Análisis completo de desalineamiento
        
        Args:
            u_field: Campo de velocidad [3, Nx, Ny, Nz]
            
        Returns:
            Diccionario con análisis completo
        """
        # Calcular campos
        S = compute_strain_tensor(u_field, self.dx)
        omega = compute_vorticity_from_velocity(u_field, self.dx)
        delta = compute_misalignment_field(S, omega)
        theta = compute_alignment_angle(S, omega)
        
        # Estadísticas
        delta_stats = spatial_statistics(delta)
        theta_stats = spatial_statistics(theta)
        
        # Métricas globales
        enstrophy = compute_enstrophy(omega, self.dx)
        correlation = compute_strain_enstrophy_correlation(S, omega)
        
        # Análisis espectral
        spectral = spectral_analysis_misalignment(delta)
        
        analysis = {
            'delta_statistics': delta_stats,
            'theta_statistics': theta_stats,
            'enstrophy': enstrophy,
            'strain_vorticity_correlation': correlation,
            'spectral_analysis': spectral,
            'fields': {
                'S': S,
                'omega': omega,
                'delta': delta,
                'theta': theta
            }
        }
        
        return analysis
    
    def temporal_evolution(self, u_history: list) -> Dict:
        """
        Analizar evolución temporal
        
        Args:
            u_history: Lista de campos de velocidad en diferentes tiempos
            
        Returns:
            Evolución temporal de métricas
        """
        n_times = len(u_history)
        
        delta_mean_history = []
        delta_std_history = []
        enstrophy_history = []
        correlation_history = []
        
        for u_field in u_history:
            analysis = self.full_analysis(u_field)
            
            delta_mean_history.append(analysis['delta_statistics']['mean'])
            delta_std_history.append(analysis['delta_statistics']['std'])
            enstrophy_history.append(analysis['enstrophy'])
            correlation_history.append(analysis['strain_vorticity_correlation'])
        
        # Calcular delta*
        delta_star, std_delta_star = compute_delta_star_from_history(np.array(delta_mean_history))
        
        evolution = {
            'delta_mean': np.array(delta_mean_history),
            'delta_std': np.array(delta_std_history),
            'enstrophy': np.array(enstrophy_history),
            'correlation': np.array(correlation_history),
            'delta_star': delta_star,
            'delta_star_std': std_delta_star
        }
        
        return evolution
    
    def export_delta_star_json(self, evolution: Dict, filename: str = "delta_star.json"):
        """
        Exportar delta* a archivo JSON
        
        Args:
            evolution: Diccionario con evolución temporal
            filename: Nombre del archivo de salida
        """
        # Convertir arrays numpy a listas para serialización JSON
        export_data = {
            'delta_star': float(evolution['delta_star']),
            'delta_star_std': float(evolution['delta_star_std']),
            'delta_mean': evolution['delta_mean'].tolist(),
            'delta_std': evolution['delta_std'].tolist(),
            'enstrophy': evolution['enstrophy'].tolist(),
            'correlation': evolution['correlation'].tolist(),
            'n_timesteps': len(evolution['delta_mean'])
        }
        
        with open(filename, 'w') as f:
            json.dump(export_data, f, indent=2)
        
        print(f"Delta* data exported to {filename}")
        print(f"  δ* = {export_data['delta_star']:.6f} ± {export_data['delta_star_std']:.6f}")


if __name__ == "__main__":
    # Ejemplo de uso
    print("Ejemplo de cálculo de defecto de desalineamiento")
    
    N = 32
    u_field = np.random.randn(3, N, N, N) * 0.1
    
    calculator = MisalignmentCalculator(dx=2*np.pi/N)
    analysis = calculator.full_analysis(u_field)
    
    print(f"\nEstadísticas de delta:")
    for key, val in analysis['delta_statistics'].items():
        print(f"  {key}: {val:.6f}")
    
    print(f"\nEnstrofia: {analysis['enstrophy']:.6f}")
    print(f"Correlación S-omega: {analysis['strain_vorticity_correlation']:.6f}")
    
    # Ejemplo de evolución temporal y exportación a JSON
    print("\n--- Evolución temporal y exportación ---")
    n_timesteps = 10
    u_history = [np.random.randn(3, N, N, N) * 0.1 for _ in range(n_timesteps)]
    
    evolution = calculator.temporal_evolution(u_history)
    calculator.export_delta_star_json(evolution, "delta_star.json")
