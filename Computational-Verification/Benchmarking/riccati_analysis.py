"""
Análisis del coeficiente de Riccati para control de vorticidad
"""

import numpy as np
import matplotlib.pyplot as plt
from typing import Dict, List, Tuple
import sys
import os

sys.path.append(os.path.join(os.path.dirname(__file__), '..', 'DNS-Solver'))
from dual_limit_scaling import compute_riccati_coefficient, analyze_blow_up_criterion


class RiccatiAnalyzer:
    """Analizador para la ecuación de Riccati de vorticidad"""
    
    def __init__(self, C_BKM: float = 1.0, c_B: float = 0.8):
        """
        Inicializar analizador
        
        Args:
            C_BKM: Constante del criterio BKM
            c_B: Parámetro de disipación
        """
        self.C_BKM = C_BKM
        self.c_B = c_B
    
    def solve_riccati_ode(self, delta_t: np.ndarray, nu: float, 
                         omega₀: float, time: np.ndarray) -> np.ndarray:
        """
        Resolver ecuación de Riccati para ‖omega‖²
        
        d/dt(‖omega‖²) ≤ alpha*(t)‖omega‖² - nuc_B‖nablaomega‖²
        
        Args:
            delta_t: Defecto de desalineamiento delta(t)
            nu: Viscosidad
            omega₀: Valor inicial de ‖omega‖
            time: Array de tiempos
            
        Returns:
            Evolución de ‖omega‖²
        """
        dt = time[1] - time[0] if len(time) > 1 else 0.01
        omega_sq = np.zeros_like(time)
        omega_sq[0] = omega₀**2
        
        for i in range(len(time) - 1):
            alpha_star = self.C_BKM * (1 - delta_t[i]) - nu * self.c_B
            
            # Aproximación simple: ‖nablaomega‖² ~ ‖omega‖²/L²
            L = 1.0  # Escala característica
            
            domega_sq = alpha_star * omega_sq[i] - nu * self.c_B * omega_sq[i] / L**2
            omega_sq[i + 1] = omega_sq[i] + dt * domega_sq
            
            # Asegurar no negatividad
            omega_sq[i + 1] = max(0, omega_sq[i + 1])
        
        return omega_sq
    
    def critical_delta(self, nu: float) -> float:
        """
        Calcular delta crítico para alpha* = 0
        
        Args:
            nu: Viscosidad
            
        Returns:
            delta_crit tal que alpha*(delta_crit) = 0
        """
        return nu * self.c_B / self.C_BKM
    
    def stability_analysis(self, delta_values: np.ndarray, nu: float) -> Dict:
        """
        Analizar estabilidad del sistema
        
        Args:
            delta_values: Array de valores de delta
            nu: Viscosidad
            
        Returns:
            Análisis de estabilidad
        """
        alpha_star_values = np.array([
            compute_riccati_coefficient(delta, self.C_BKM, nu, self.c_B)
            for delta in delta_values
        ])
        
        delta_crit = self.critical_delta(nu)
        
        analysis = {
            'alpha_star': alpha_star_values,
            'delta_critical': delta_crit,
            'stable': np.all(alpha_star_values < 0),
            'max_alpha_star': np.max(alpha_star_values),
            'min_alpha_star': np.min(alpha_star_values),
            'safety_margin': -np.max(alpha_star_values) if np.max(alpha_star_values) < 0 else 0
        }
        
        return analysis
    
    def estimate_blow_up_time(self, delta_t: np.ndarray, nu: float, 
                             omega₀: float, time: np.ndarray,
                             threshold: float = 1e6) -> float:
        """
        Estimar tiempo de blow-up si ocurre
        
        Args:
            delta_t: Defecto de desalineamiento delta(t)
            nu: Viscosidad
            omega₀: Valor inicial
            time: Array de tiempos
            threshold: Umbral para blow-up
            
        Returns:
            Tiempo de blow-up (inf si no ocurre)
        """
        omega_sq = self.solve_riccati_ode(delta_t, nu, omega₀, time)
        
        blow_up_idx = np.where(omega_sq > threshold**2)[0]
        
        if len(blow_up_idx) > 0:
            return time[blow_up_idx[0]]
        else:
            return np.inf
    
    def parameter_sensitivity_analysis(self, delta_star: float, nu_range: np.ndarray) -> Dict:
        """
        Analizar sensibilidad con respecto a viscosidad
        
        Args:
            delta_star: Valor de delta*
            nu_range: Rango de viscosidades
            
        Returns:
            Análisis de sensibilidad
        """
        alpha_star_values = []
        delta_crit_values = []
        stable = []
        
        for nu in nu_range:
            alpha_star = compute_riccati_coefficient(delta_star, self.C_BKM, nu, self.c_B)
            delta_crit = self.critical_delta(nu)
            
            alpha_star_values.append(alpha_star)
            delta_crit_values.append(delta_crit)
            stable.append(alpha_star < 0)
        
        return {
            'nu_range': nu_range,
            'alpha_star': np.array(alpha_star_values),
            'delta_critical': np.array(delta_crit_values),
            'stable': np.array(stable)
        }


def analyze_riccati_dynamics(results: Dict, nu: float = 0.001):
    """
    Analizar dinámica de Riccati para resultados de simulación
    
    Args:
        results: Resultados de simulación
        nu: Viscosidad
    """
    print("=" * 70)
    print("ANÁLISIS DE COEFICIENTE DE RICCATI")
    print("=" * 70)
    
    analyzer = RiccatiAnalyzer(C_BKM=1.0, c_B=0.8)
    
    f0_values = sorted(results.keys())
    
    print(f"\nViscosidad: nu = {nu}")
    print(f"Constantes: C_BKM = {analyzer.C_BKM}, c_B = {analyzer.c_B}")
    print(f"delta crítico: {analyzer.critical_delta(nu):.6f}")
    print("\n" + "-" * 70)
    print(f"{'f0 (Hz)':<12} {'delta*':<12} {'alpha*':<12} {'Estable':<12}")
    print("-" * 70)
    
    for f0 in f0_values:
        delta_star = results[f0]['delta_star']
        alpha_star = compute_riccati_coefficient(delta_star, analyzer.C_BKM, nu, analyzer.c_B)
        stable = "✓" if alpha_star < 0 else "✗"
        
        print(f"{f0:<12.1f} {delta_star:<12.6f} {alpha_star:<12.6f} {stable:<12}")
    
    # Análisis de estabilidad
    delta_star_values = np.array([results[f0]['delta_star'] for f0 in f0_values])
    stability = analyzer.stability_analysis(delta_star_values, nu)
    
    print("\n" + "=" * 70)
    print("ANÁLISIS DE ESTABILIDAD")
    print("=" * 70)
    print(f"Sistema estable: {stability['stable']}")
    print(f"Rango de alpha*: [{stability['min_alpha_star']:.6f}, {stability['max_alpha_star']:.6f}]")
    print(f"Margen de seguridad: {stability['safety_margin']:.6f}")
    
    # Análisis de sensibilidad
    print("\n" + "=" * 70)
    print("ANÁLISIS DE SENSIBILIDAD")
    print("=" * 70)
    
    delta_star_avg = np.mean(delta_star_values)
    nu_range = np.logspace(-4, -2, 20)
    sensitivity = analyzer.parameter_sensitivity_analysis(delta_star_avg, nu_range)
    
    # Encontrar viscosidad crítica
    nu_crit_idx = np.where(sensitivity['stable'])[0]
    if len(nu_crit_idx) > 0:
        nu_crit = nu_range[nu_crit_idx[0]]
        print(f"Viscosidad crítica mínima: nu_crit ≈ {nu_crit:.6f}")
    else:
        print("No se encontró viscosidad crítica en el rango analizado")
    
    # Visualización
    fig, axes = plt.subplots(1, 2, figsize=(14, 5))
    
    # alpha* vs f0
    axes[0].semilogx(f0_values, stability['alpha_star'], 'mo-', linewidth=2, markersize=8)
    axes[0].axhline(0, color='k', linestyle='--', linewidth=1.5, label='alpha* = 0')
    axes[0].fill_between(f0_values, -1, 0, alpha=0.2, color='green', 
                        label='Región estable')
    axes[0].set_xlabel('Frecuencia f0 (Hz)', fontsize=12)
    axes[0].set_ylabel('alpha*', fontsize=12)
    axes[0].set_title('Coeficiente de Riccati vs Frecuencia', fontsize=13, fontweight='bold')
    axes[0].legend(fontsize=11)
    axes[0].grid(True, alpha=0.3)
    
    # Sensibilidad con respecto a nu
    axes[1].loglog(sensitivity['nu_range'], -sensitivity['alpha_star'], 'b-', 
                  linewidth=2, label=f'delta* = {delta_star_avg:.4f}')
    axes[1].axhline(0, color='k', linestyle='--', linewidth=1.5)
    axes[1].set_xlabel('Viscosidad nu', fontsize=12)
    axes[1].set_ylabel('-alpha*', fontsize=12)
    axes[1].set_title('Sensibilidad con Respecto a Viscosidad', fontsize=13, fontweight='bold')
    axes[1].legend(fontsize=11)
    axes[1].grid(True, alpha=0.3)
    
    plt.tight_layout()
    
    # Guardar figura
    results_dir = "../../Results/Figures"
    os.makedirs(results_dir, exist_ok=True)
    plt.savefig(os.path.join(results_dir, 'riccati_analysis.png'), 
               dpi=300, bbox_inches='tight')
    plt.close()
    
    print("\n✓ Análisis de Riccati completado")
    print(f"  Figura guardada en {results_dir}/riccati_analysis.png")
    
    return stability, sensitivity


if __name__ == "__main__":
    # Ejemplo de uso con datos sintéticos
    print("Generando datos de ejemplo para análisis de Riccati...")
    
    f0_values = [100, 200, 500, 1000, 2000]
    results = {
        f0: {
            'delta_star': 0.025 + 0.01/f0,
            'omega_inf': np.ones(50)
        }
        for f0 in f0_values
    }
    
    analyze_riccati_dynamics(results, nu=0.001)
