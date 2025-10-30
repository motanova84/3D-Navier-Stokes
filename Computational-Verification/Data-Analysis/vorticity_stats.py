"""
Estadísticas y análisis de vorticidad
"""

import numpy as np
from typing import Dict, Tuple
from scipy import fft


def compute_vorticity_norms(omega: np.ndarray, dx: float = 1.0) -> Dict[str, float]:
    """
    Calcular diferentes normas de vorticidad
    
    Args:
        omega: Campo de vorticidad [3, Nx, Ny, Nz]
        dx: Espaciado de malla
        
    Returns:
        Diccionario con normas
    """
    omega_magnitude = np.sqrt(np.sum(omega**2, axis=0))
    
    norms = {
        'L_inf': np.max(omega_magnitude),
        'L_2': np.sqrt(np.sum(omega_magnitude**2) * dx**3),
        'L_1': np.sum(omega_magnitude) * dx**3,
        'mean': np.mean(omega_magnitude),
        'std': np.std(omega_magnitude)
    }
    
    return norms


def compute_vorticity_spectrum(omega: np.ndarray) -> Dict:
    """
    Calcular espectro de energía de vorticidad
    
    Args:
        omega: Campo de vorticidad [3, Nx, Ny, Nz]
        
    Returns:
        Espectro y análisis
    """
    N = omega.shape[1]
    
    # FFT de cada componente
    omega_hat = np.array([fft.fftn(omega[i]) for i in range(3)])
    
    # Espectro de energía
    E_omega = np.sum(np.abs(omega_hat)**2, axis=0)
    
    # Números de onda
    k = np.fft.fftfreq(N) * N
    kx, ky, kz = np.meshgrid(k, k, k, indexing='ij')
    k_mag = np.sqrt(kx**2 + ky**2 + kz**2)
    
    # Espectro radial
    k_bins = np.arange(0, N//2)
    E_k = np.zeros_like(k_bins, dtype=float)
    
    for i, k_val in enumerate(k_bins):
        mask = (k_mag >= k_val) & (k_mag < k_val + 1)
        E_k[i] = np.sum(E_omega[mask]) if np.any(mask) else 0
    
    # Análisis espectral
    total_energy = np.sum(E_k)
    peak_k = k_bins[np.argmax(E_k)] if len(E_k) > 0 else 0
    
    # Estimar escala integral y de Kolmogorov
    if total_energy > 0 and peak_k > 0:
        integral_scale = 1.0 / peak_k
        # Aproximación simple de escala de Kolmogorov
        kolmogorov_scale = N / (2 * k_bins[-1])
    else:
        integral_scale = 0
        kolmogorov_scale = 0
    
    spectrum = {
        'k_bins': k_bins,
        'E_k': E_k,
        'total_energy': total_energy,
        'peak_k': peak_k,
        'integral_scale': integral_scale,
        'kolmogorov_scale': kolmogorov_scale
    }
    
    return spectrum


def compute_helicity(u: np.ndarray, omega: np.ndarray, dx: float = 1.0) -> float:
    """
    Calcular helicidad H = ∫ u·omega dx
    
    Args:
        u: Campo de velocidad [3, Nx, Ny, Nz]
        omega: Vorticidad [3, Nx, Ny, Nz]
        dx: Espaciado de malla
        
    Returns:
        Helicidad total
    """
    u_dot_omega = np.sum(u * omega, axis=0)
    H = np.sum(u_dot_omega) * dx**3
    
    return H


def compute_enstrophy_production(omega: np.ndarray, S: np.ndarray, 
                                 nu: float, dx: float = 1.0) -> Dict:
    """
    Calcular producción y disipación de enstrofia
    
    dOmega/dt = ∫omega·S·omega dx - nu∫|nablaomega|² dx
    
    Args:
        omega: Vorticidad [3, Nx, Ny, Nz]
        S: Tensor de deformación [3, 3, Nx, Ny, Nz]
        nu: Viscosidad
        dx: Espaciado de malla
        
    Returns:
        Términos de producción/disipación
    """
    # Término de producción: omega·S·omega
    Somega = np.zeros_like(omega)
    for i in range(3):
        for j in range(3):
            Somega[i] += S[i, j] * omega[j]
    
    production = np.sum(omega * Somega) * dx**3
    
    # Término de disipación: nu|nablaomega|²
    grad_omega_sq = 0
    for i in range(3):
        for dim in [1, 2, 3]:  # x, y, z
            grad_omega = np.gradient(omega[i], dx, axis=dim)
            grad_omega_sq += np.sum(grad_omega**2)
    
    dissipation = nu * grad_omega_sq * dx**3
    
    balance = {
        'production': production,
        'dissipation': dissipation,
        'net_rate': production - dissipation
    }
    
    return balance


def compute_vorticity_stretching(omega: np.ndarray, u: np.ndarray, 
                                 dx: float = 1.0) -> np.ndarray:
    """
    Calcular estiramiento de vorticidad omega·nablau
    
    Args:
        omega: Vorticidad [3, Nx, Ny, Nz]
        u: Velocidad [3, Nx, Ny, Nz]
        dx: Espaciado de malla
        
    Returns:
        Campo de estiramiento [3, Nx, Ny, Nz]
    """
    stretching = np.zeros_like(omega)
    
    # Gradiente de velocidad
    du_dx = np.gradient(u, dx, axis=1)
    du_dy = np.gradient(u, dx, axis=2)
    du_dz = np.gradient(u, dx, axis=3)
    
    grads = [du_dx, du_dy, du_dz]
    
    # (omega·nablau)_i = omega_j ∂u_i/∂x_j
    for i in range(3):
        for j in range(3):
            stretching[i] += omega[j] * grads[j][i]
    
    return stretching


def analyze_vortex_structures(omega: np.ndarray, threshold: float = None) -> Dict:
    """
    Identificar y analizar estructuras coherentes de vórtices
    
    Args:
        omega: Vorticidad [3, Nx, Ny, Nz]
        threshold: Umbral para identificación (default: 2*std)
        
    Returns:
        Análisis de estructuras
    """
    omega_magnitude = np.sqrt(np.sum(omega**2, axis=0))
    
    if threshold is None:
        threshold = np.mean(omega_magnitude) + 2 * np.std(omega_magnitude)
    
    # Identificar regiones de alta vorticidad
    vortex_regions = omega_magnitude > threshold
    
    # Estadísticas
    vortex_volume_fraction = np.sum(vortex_regions) / vortex_regions.size
    max_vorticity = np.max(omega_magnitude)
    mean_in_vortices = np.mean(omega_magnitude[vortex_regions]) if np.any(vortex_regions) else 0
    
    analysis = {
        'threshold': threshold,
        'vortex_volume_fraction': vortex_volume_fraction,
        'max_vorticity': max_vorticity,
        'mean_in_vortices': mean_in_vortices,
        'n_vortex_points': np.sum(vortex_regions)
    }
    
    return analysis


def compute_Q_criterion(u: np.ndarray, dx: float = 1.0) -> np.ndarray:
    """
    Calcular criterio Q para identificación de vórtices
    Q = 1/2(|Omega|² - |S|²)
    
    Args:
        u: Velocidad [3, Nx, Ny, Nz]
        dx: Espaciado de malla
        
    Returns:
        Campo Q [Nx, Ny, Nz]
    """
    N = u.shape[1]
    
    # Gradiente de velocidad
    du_dx = np.gradient(u, dx, axis=1)
    du_dy = np.gradient(u, dx, axis=2)
    du_dz = np.gradient(u, dx, axis=3)
    
    # Tensor de vorticidad Omega_ij = 1/2(∂u_i/∂x_j - ∂u_j/∂x_i)
    Omega = np.zeros((3, 3, N, N, N))
    grads = [du_dx, du_dy, du_dz]
    
    for i in range(3):
        for j in range(3):
            Omega[i, j] = 0.5 * (grads[j][i] - grads[i][j])
    
    # Tensor de deformación S_ij = 1/2(∂u_i/∂x_j + ∂u_j/∂x_i)
    S = np.zeros((3, 3, N, N, N))
    for i in range(3):
        for j in range(3):
            S[i, j] = 0.5 * (grads[j][i] + grads[i][j])
    
    # |Omega|² y |S|²
    Omega_sq = np.sum(Omega**2, axis=(0, 1))
    S_sq = np.sum(S**2, axis=(0, 1))
    
    Q = 0.5 * (Omega_sq - S_sq)
    
    return Q


class VorticityAnalyzer:
    """Analizador completo de vorticidad"""
    
    def __init__(self, dx: float = 1.0, nu: float = 0.001):
        """
        Inicializar analizador
        
        Args:
            dx: Espaciado de malla
            nu: Viscosidad
        """
        self.dx = dx
        self.nu = nu
    
    def comprehensive_analysis(self, u: np.ndarray, omega: np.ndarray, 
                              S: np.ndarray = None) -> Dict:
        """
        Análisis completo de vorticidad
        
        Args:
            u: Velocidad [3, Nx, Ny, Nz]
            omega: Vorticidad [3, Nx, Ny, Nz]
            S: Tensor de deformación (opcional)
            
        Returns:
            Análisis completo
        """
        # Normas
        norms = compute_vorticity_norms(omega, self.dx)
        
        # Espectro
        spectrum = compute_vorticity_spectrum(omega)
        
        # Helicidad
        helicity = compute_helicity(u, omega, self.dx)
        
        # Balance de enstrofia (si S está disponible)
        if S is not None:
            enstrophy_balance = compute_enstrophy_production(omega, S, self.nu, self.dx)
        else:
            enstrophy_balance = None
        
        # Estructuras de vórtices
        vortex_structures = analyze_vortex_structures(omega)
        
        # Criterio Q
        Q = compute_Q_criterion(u, self.dx)
        Q_stats = {
            'mean': np.mean(Q),
            'std': np.std(Q),
            'max': np.max(Q),
            'min': np.min(Q)
        }
        
        analysis = {
            'norms': norms,
            'spectrum': spectrum,
            'helicity': helicity,
            'enstrophy_balance': enstrophy_balance,
            'vortex_structures': vortex_structures,
            'Q_criterion': Q_stats
        }
        
        return analysis
    
    def temporal_statistics(self, omega_history: list) -> Dict:
        """
        Estadísticas temporales de vorticidad
        
        Args:
            omega_history: Lista de campos de vorticidad
            
        Returns:
            Estadísticas temporales
        """
        L_inf_history = []
        L_2_history = []
        helicity_history = []
        
        for omega in omega_history:
            norms = compute_vorticity_norms(omega, self.dx)
            L_inf_history.append(norms['L_inf'])
            L_2_history.append(norms['L_2'])
        
        stats = {
            'L_inf': np.array(L_inf_history),
            'L_2': np.array(L_2_history),
            'L_inf_max': np.max(L_inf_history),
            'L_inf_mean': np.mean(L_inf_history),
            'L_2_mean': np.mean(L_2_history)
        }
        
        return stats


if __name__ == "__main__":
    # Ejemplo de uso
    print("Ejemplo de análisis de vorticidad")
    
    N = 32
    u = np.random.randn(3, N, N, N) * 0.1
    omega = np.random.randn(3, N, N, N) * 0.1
    
    analyzer = VorticityAnalyzer(dx=2*np.pi/N, nu=0.001)
    analysis = analyzer.comprehensive_analysis(u, omega)
    
    print(f"\nNormas de vorticidad:")
    for key, val in analysis['norms'].items():
        print(f"  {key}: {val:.6f}")
    
    print(f"\nHelicidad: {analysis['helicity']:.6f}")
    
    print(f"\nEstructuras de vórtices:")
    for key, val in analysis['vortex_structures'].items():
        print(f"  {key}: {val}")
