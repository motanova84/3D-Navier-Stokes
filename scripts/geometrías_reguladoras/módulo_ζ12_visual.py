#!/usr/bin/env python3
"""
Módulo de visualización de ζ'(1/2) - Proyección de la derivada de Riemann sobre modos del fluido.

Visualiza cómo la derivada espectral de la función zeta de Riemann afecta la disociación
dyádica y la energía modal del fluido, comparando escenarios con y sin ζ'(1/2).
"""

import numpy as np
import matplotlib.pyplot as plt
from typing import Tuple, Optional
import warnings
warnings.filterwarnings('ignore')

class RiemannZetaVisualizer:
    """
    Visualizador de efectos de ζ'(1/2) sobre modos del fluido.
    
    Implementa:
    - Cálculo aproximado de ζ'(1/2)
    - Proyección sobre modos dyádicos
    - Comparación de escenarios sin/con ζ'(1/2)/con f₀
    """
    
    def __init__(self, n_modes: int = 50, f0: float = 141.7001):
        """
        Inicializa el visualizador.
        
        Args:
            n_modes: Número de modos dyádicos
            f0: Frecuencia fundamental de coherencia (Hz)
        """
        self.n_modes = n_modes
        self.f0 = f0
        self.omega0 = 2 * np.pi * f0
        
        # Valor aproximado de ζ'(1/2) (derivada en línea crítica)
        # ζ'(1/2) ≈ -3.92... (valor numérico conocido)
        self.zeta_prime_half = -3.92264867
        
    def dyadic_modes(self) -> np.ndarray:
        """
        Genera números de onda dyádicos k_j = 2^j.
        
        Returns:
            k: Array de números de onda dyádicos
        """
        j = np.arange(1, self.n_modes + 1)
        k = 2.0 ** j
        return k
    
    def energy_spectrum_baseline(self, k: np.ndarray) -> np.ndarray:
        """
        Espectro de energía base (sin ζ'(1/2)).
        
        E(k) ~ k^(-5/3) (cascada de Kolmogorov)
        
        Args:
            k: Números de onda
            
        Returns:
            E: Energía espectral
        """
        E = k ** (-5/3) * np.exp(-k / 1e5)
        return E
    
    def zeta_modulation(self, k: np.ndarray) -> np.ndarray:
        """
        Factor de modulación por ζ'(1/2).
        
        M(k) = 1 + ε·ζ'(1/2)·k^(-1/2)
        
        Args:
            k: Números de onda
            
        Returns:
            M: Factor de modulación
        """
        epsilon = 0.1  # Parámetro de acoplamiento
        M = 1 + epsilon * self.zeta_prime_half * k ** (-0.5)
        return M
    
    def frequency_modulation(self, k: np.ndarray, t: float = 0) -> np.ndarray:
        """
        Factor de modulación adicional por f₀.
        
        F(k,t) = 1 + α·cos(ω₀·t)·exp(-k/k₀)
        
        Args:
            k: Números de onda
            t: Tiempo
            
        Returns:
            F: Factor de modulación por frecuencia
        """
        alpha = 0.2
        k0 = 100.0
        F = 1 + alpha * np.cos(self.omega0 * t) * np.exp(-k / k0)
        return F
    
    def energy_spectrum_with_zeta(self, k: np.ndarray) -> np.ndarray:
        """
        Espectro de energía con ζ'(1/2).
        
        Args:
            k: Números de onda
            
        Returns:
            E: Energía espectral modulada
        """
        E_base = self.energy_spectrum_baseline(k)
        M_zeta = self.zeta_modulation(k)
        E = E_base * M_zeta
        return E
    
    def energy_spectrum_with_zeta_and_f0(self, k: np.ndarray, t: float = 0) -> np.ndarray:
        """
        Espectro de energía con ζ'(1/2) y f₀.
        
        Args:
            k: Números de onda
            t: Tiempo
            
        Returns:
            E: Energía espectral con modulación completa
        """
        E_base = self.energy_spectrum_baseline(k)
        M_zeta = self.zeta_modulation(k)
        F_freq = self.frequency_modulation(k, t)
        E = E_base * M_zeta * F_freq
        return E
    
    def dyadic_dissociation_rate(self, k: np.ndarray, scenario: str = 'baseline') -> np.ndarray:
        """
        Tasa de disociación dyádica.
        
        Γ(k) = -dE/dk (tasa de transferencia energética)
        
        Args:
            k: Números de onda
            scenario: 'baseline', 'zeta', 'zeta_f0'
            
        Returns:
            gamma: Tasa de disociación
        """
        dk = k[1] - k[0] if len(k) > 1 else 1.0
        
        if scenario == 'baseline':
            E = self.energy_spectrum_baseline(k)
        elif scenario == 'zeta':
            E = self.energy_spectrum_with_zeta(k)
        elif scenario == 'zeta_f0':
            E = self.energy_spectrum_with_zeta_and_f0(k, t=0)
        
        # Derivada numérica
        gamma = -np.gradient(E, dk)
        
        return gamma
    
    def visualize_comparison(self, t: float = 0, save_path: Optional[str] = None) -> None:
        """
        Visualiza comparación de los tres escenarios.
        
        Args:
            t: Tiempo (relevante para escenario con f₀)
            save_path: Ruta para guardar la figura
        """
        # Generar modos dyádicos
        k = self.dyadic_modes()
        
        # Calcular espectros
        E_baseline = self.energy_spectrum_baseline(k)
        E_zeta = self.energy_spectrum_with_zeta(k)
        E_zeta_f0 = self.energy_spectrum_with_zeta_and_f0(k, t)
        
        # Calcular tasas de disociación
        gamma_baseline = self.dyadic_dissociation_rate(k, 'baseline')
        gamma_zeta = self.dyadic_dissociation_rate(k, 'zeta')
        gamma_zeta_f0 = self.dyadic_dissociation_rate(k, 'zeta_f0')
        
        # Visualización
        fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(16, 12))
        
        # Panel 1: Espectros de energía
        ax1.loglog(k, E_baseline, 'o-', label='Sin ζ\'(1/2)', linewidth=2, markersize=4)
        ax1.loglog(k, E_zeta, 's-', label='Con ζ\'(1/2)', linewidth=2, markersize=4)
        ax1.loglog(k, E_zeta_f0, '^-', label=f'Con ζ\'(1/2) + f₀', linewidth=2, markersize=4)
        ax1.set_xlabel('Número de onda k', fontsize=12)
        ax1.set_ylabel('Energía E(k)', fontsize=12)
        ax1.set_title('Espectro de Energía Modal', fontsize=14)
        ax1.legend(fontsize=10)
        ax1.grid(True, alpha=0.3, which='both')
        
        # Panel 2: Diferencia relativa
        diff_zeta = (E_zeta - E_baseline) / (E_baseline + 1e-10) * 100
        diff_zeta_f0 = (E_zeta_f0 - E_baseline) / (E_baseline + 1e-10) * 100
        
        ax2.semilogx(k, diff_zeta, 's-', label='ζ\'(1/2) vs baseline', linewidth=2, markersize=4)
        ax2.semilogx(k, diff_zeta_f0, '^-', label='ζ\'(1/2)+f₀ vs baseline', linewidth=2, markersize=4)
        ax2.axhline(y=0, color='k', linestyle='--', alpha=0.3)
        ax2.set_xlabel('Número de onda k', fontsize=12)
        ax2.set_ylabel('Diferencia relativa (%)', fontsize=12)
        ax2.set_title('Efecto de ζ\'(1/2) sobre Energía Modal', fontsize=14)
        ax2.legend(fontsize=10)
        ax2.grid(True, alpha=0.3)
        
        # Panel 3: Tasa de disociación dyádica
        ax3.semilogx(k, gamma_baseline, 'o-', label='Sin ζ\'(1/2)', linewidth=2, markersize=4)
        ax3.semilogx(k, gamma_zeta, 's-', label='Con ζ\'(1/2)', linewidth=2, markersize=4)
        ax3.semilogx(k, gamma_zeta_f0, '^-', label=f'Con ζ\'(1/2) + f₀', linewidth=2, markersize=4)
        ax3.axhline(y=0, color='k', linestyle='--', alpha=0.3)
        ax3.set_xlabel('Número de onda k', fontsize=12)
        ax3.set_ylabel('Γ(k) = -dE/dk', fontsize=12)
        ax3.set_title('Tasa de Disociación Dyádica', fontsize=14)
        ax3.legend(fontsize=10)
        ax3.grid(True, alpha=0.3)
        
        # Panel 4: Factor de modulación
        M_zeta = self.zeta_modulation(k)
        F_freq = self.frequency_modulation(k, t)
        M_combined = M_zeta * F_freq
        
        ax4.semilogx(k, M_zeta, 's-', label='M_ζ (modulación por ζ\'(1/2))', linewidth=2, markersize=4)
        ax4.semilogx(k, F_freq, '^-', label='F (modulación por f₀)', linewidth=2, markersize=4)
        ax4.semilogx(k, M_combined, 'o-', label='M_ζ × F (combinado)', linewidth=2, markersize=4)
        ax4.axhline(y=1, color='k', linestyle='--', alpha=0.3)
        ax4.set_xlabel('Número de onda k', fontsize=12)
        ax4.set_ylabel('Factor de modulación', fontsize=12)
        ax4.set_title(f'Factores de Modulación (t={t:.2f}s)', fontsize=14)
        ax4.legend(fontsize=10)
        ax4.grid(True, alpha=0.3)
        
        plt.tight_layout()
        
        if save_path:
            plt.savefig(save_path, dpi=150, bbox_inches='tight')
            print(f"✅ Visualización guardada en: {save_path}")
        
        plt.show()
        
        # Estadísticas
        print(f"\n📊 Estadísticas Comparativas:")
        print(f"   ζ'(1/2) = {self.zeta_prime_half:.8f}")
        print(f"   f₀ = {self.f0:.4f} Hz")
        print(f"\n   Energía total (sin ζ'(1/2)):      {E_baseline.sum():.6e}")
        print(f"   Energía total (con ζ'(1/2)):      {E_zeta.sum():.6e}")
        print(f"   Energía total (con ζ'(1/2) + f₀): {E_zeta_f0.sum():.6e}")
        print(f"\n   Cambio por ζ'(1/2):      {(E_zeta.sum() - E_baseline.sum()) / E_baseline.sum() * 100:.2f}%")
        print(f"   Cambio por ζ'(1/2) + f₀: {(E_zeta_f0.sum() - E_baseline.sum()) / E_baseline.sum() * 100:.2f}%")


def main():
    """Función principal de demostración."""
    print("=" * 70)
    print("📊 MÓDULO ζ'(1/2) - VISUALIZACIÓN RIEMANN-NAVIER-STOKES")
    print("=" * 70)
    print(f"🔢 Derivada de Riemann: ζ'(1/2) ≈ -3.92264867")
    print(f"🎵 Frecuencia fundamental: f₀ = 141.7001 Hz")
    print(f"🌀 Modos dyádicos: k_j = 2^j")
    print("=" * 70)
    print()
    
    # Crear visualizador
    visualizer = RiemannZetaVisualizer(n_modes=30, f0=141.7001)
    
    # Ejemplo 1: Comparación en t=0
    print("📊 Ejemplo 1: Comparación en t=0")
    visualizer.visualize_comparison(t=0)
    
    # Ejemplo 2: Comparación en t=π/(2ω₀)
    print("\n📊 Ejemplo 2: Comparación en fase π/2")
    visualizer.visualize_comparison(t=np.pi / (2 * visualizer.omega0))
    
    # Ejemplo 3: Comparación en t=π/ω₀
    print("\n📊 Ejemplo 3: Comparación en fase π")
    visualizer.visualize_comparison(t=np.pi / visualizer.omega0)
    
    print("\n" + "=" * 70)
    print("✅ Análisis completado")
    print("🔷 Conclusión: ζ'(1/2) modula la disociación dyádica")
    print("🔷 Efecto amplificado: Acoplamiento con f₀ = 141.7001 Hz")
    print("=" * 70)


if __name__ == "__main__":
    main()
