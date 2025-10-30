"""
Herramientas de visualización para resultados de simulaciones Ψ-NS
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib import cm
from mpl_toolkits.mplot3d import Axes3D
from typing import Dict, Optional, List
import os


class PsiNSVisualizer:
    """Clase para visualización de resultados"""
    
    def __init__(self, results_dir: str = "../../Results/Figures"):
        """
        Inicializar visualizador
        
        Args:
            results_dir: Directorio para guardar figuras
        """
        self.results_dir = results_dir
        os.makedirs(results_dir, exist_ok=True)
        
        # Configuración de estilo
        plt.style.use('seaborn-v0_8-darkgrid' if 'seaborn-v0_8-darkgrid' in plt.style.available 
                     else 'default')
        
    def plot_convergence(self, results: Dict, delta_theoretical: float, 
                        save_name: Optional[str] = None):
        """
        Graficar convergencia de delta* vs f0
        
        Args:
            results: Diccionario con resultados {f0: {'delta_star': ...}}
            delta_theoretical: Valor teórico de delta*
            save_name: Nombre del archivo (opcional)
        """
        f0_values = sorted(results.keys())
        delta_star_computed = [results[f0]['delta_star'] for f0 in f0_values]
        
        fig, ax = plt.subplots(figsize=(10, 6))
        
        ax.loglog(f0_values, delta_star_computed, 'bo-', linewidth=2, 
                 markersize=8, label='Computado')
        ax.axhline(delta_theoretical, color='r', linestyle='--', linewidth=2,
                  label=f'Teórico: {delta_theoretical:.6f}')
        
        ax.set_xlabel('Frecuencia f0 (Hz)', fontsize=12)
        ax.set_ylabel('delta*', fontsize=12)
        ax.set_title('Convergencia de delta* en el Límite Dual', fontsize=14, fontweight='bold')
        ax.legend(fontsize=11)
        ax.grid(True, alpha=0.3)
        
        plt.tight_layout()
        
        if save_name:
            plt.savefig(os.path.join(self.results_dir, save_name), dpi=300, bbox_inches='tight')
        else:
            plt.savefig(os.path.join(self.results_dir, 'delta_star_convergence.png'), 
                       dpi=300, bbox_inches='tight')
        plt.close()
    
    def plot_forcing_decay(self, f0_values: List[float], forcing_magnitude: List[float],
                          save_name: Optional[str] = None):
        """
        Graficar decaimiento de fuerza oscilatoria
        
        Args:
            f0_values: Lista de frecuencias
            forcing_magnitude: Magnitudes de fuerza
            save_name: Nombre del archivo
        """
        fig, ax = plt.subplots(figsize=(10, 6))
        
        ax.loglog(f0_values, forcing_magnitude, 'go-', linewidth=2, markersize=8)
        
        ax.set_xlabel('Frecuencia f0 (Hz)', fontsize=12)
        ax.set_ylabel('||epsilonnablaPhi||', fontsize=12)
        ax.set_title('Decaimiento de Fuerza Oscilatoria', fontsize=14, fontweight='bold')
        ax.grid(True, alpha=0.3)
        
        plt.tight_layout()
        
        if save_name:
            plt.savefig(os.path.join(self.results_dir, save_name), dpi=300, bbox_inches='tight')
        else:
            plt.savefig(os.path.join(self.results_dir, 'forcing_decay.png'), 
                       dpi=300, bbox_inches='tight')
        plt.close()
    
    def plot_vorticity_evolution(self, results: Dict, 
                                save_name: Optional[str] = None):
        """
        Graficar evolución de vorticidad L∞
        
        Args:
            results: Diccionario con resultados
            save_name: Nombre del archivo
        """
        fig, ax = plt.subplots(figsize=(12, 6))
        
        f0_values = sorted(results.keys())
        colors = cm.viridis(np.linspace(0, 1, len(f0_values)))
        
        for idx, f0 in enumerate(f0_values[::max(1, len(f0_values)//5)]):  # Submuestreo
            omega_inf = results[f0]['omega_inf']
            time = np.arange(len(omega_inf)) * 0.1  # Asumiendo dt=0.01, guardado cada 10 pasos
            ax.semilogy(time, omega_inf, color=colors[idx], 
                       label=f'f0 = {f0:.0f} Hz', linewidth=2)
        
        ax.set_xlabel('Tiempo', fontsize=12)
        ax.set_ylabel('||omega||_∞', fontsize=12)
        ax.set_title('Control de Vorticidad L∞', fontsize=14, fontweight='bold')
        ax.legend(fontsize=10, loc='best')
        ax.grid(True, alpha=0.3)
        
        plt.tight_layout()
        
        if save_name:
            plt.savefig(os.path.join(self.results_dir, save_name), dpi=300, bbox_inches='tight')
        else:
            plt.savefig(os.path.join(self.results_dir, 'vorticity_evolution.png'), 
                       dpi=300, bbox_inches='tight')
        plt.close()
    
    def plot_riccati_coefficient(self, f0_values: List[float], 
                                 alpha_star_values: List[float],
                                 save_name: Optional[str] = None):
        """
        Graficar coeficiente de Riccati alpha*
        
        Args:
            f0_values: Lista de frecuencias
            alpha_star_values: Valores de alpha*
            save_name: Nombre del archivo
        """
        fig, ax = plt.subplots(figsize=(10, 6))
        
        ax.semilogx(f0_values, alpha_star_values, 'mo-', linewidth=2, markersize=8)
        ax.axhline(0, color='k', linestyle='--', linewidth=1.5, label='alpha* = 0 (crítico)')
        
        # Sombrear región de regularización
        ax.fill_between(f0_values, -1, 0, alpha=0.2, color='green', 
                       label='Región de regularización (alpha* < 0)')
        
        ax.set_xlabel('Frecuencia f0 (Hz)', fontsize=12)
        ax.set_ylabel('alpha*', fontsize=12)
        ax.set_title('Coeficiente de Riccati alpha*', fontsize=14, fontweight='bold')
        ax.legend(fontsize=11)
        ax.grid(True, alpha=0.3)
        
        plt.tight_layout()
        
        if save_name:
            plt.savefig(os.path.join(self.results_dir, save_name), dpi=300, bbox_inches='tight')
        else:
            plt.savefig(os.path.join(self.results_dir, 'riccati_coefficient.png'), 
                       dpi=300, bbox_inches='tight')
        plt.close()
    
    def plot_misalignment_temporal(self, results: Dict, f0_selected: List[float],
                                  save_name: Optional[str] = None):
        """
        Graficar evolución temporal de delta(t)
        
        Args:
            results: Diccionario con resultados
            f0_selected: Frecuencias seleccionadas para graficar
            save_name: Nombre del archivo
        """
        fig, ax = plt.subplots(figsize=(12, 6))
        
        colors = cm.plasma(np.linspace(0, 1, len(f0_selected)))
        
        for idx, f0 in enumerate(f0_selected):
            if f0 in results:
                delta_history = results[f0]['delta']
                time = np.arange(len(delta_history)) * 0.1
                ax.plot(time, delta_history, color=colors[idx], 
                       label=f'f0 = {f0:.0f} Hz', linewidth=2)
        
        ax.set_xlabel('Tiempo', fontsize=12)
        ax.set_ylabel('delta(t)', fontsize=12)
        ax.set_title('Evolución Temporal del Defecto de Desalineamiento', 
                    fontsize=14, fontweight='bold')
        ax.legend(fontsize=11)
        ax.grid(True, alpha=0.3)
        
        plt.tight_layout()
        
        if save_name:
            plt.savefig(os.path.join(self.results_dir, save_name), dpi=300, bbox_inches='tight')
        else:
            plt.savefig(os.path.join(self.results_dir, 'misalignment_temporal.png'), 
                       dpi=300, bbox_inches='tight')
        plt.close()
    
    def create_comprehensive_dashboard(self, results: Dict, 
                                      delta_theoretical: float,
                                      forcing_magnitude: List[float],
                                      alpha_star_values: List[float],
                                      save_name: Optional[str] = None):
        """
        Crear dashboard completo con todos los análisis
        
        Args:
            results: Diccionario con resultados
            delta_theoretical: Valor teórico de delta*
            forcing_magnitude: Magnitudes de fuerza
            alpha_star_values: Valores de alpha*
            save_name: Nombre del archivo
        """
        f0_values = sorted(results.keys())
        delta_star_computed = [results[f0]['delta_star'] for f0 in f0_values]
        
        fig, axes = plt.subplots(2, 2, figsize=(16, 12))
        
        # delta* vs f0
        axes[0, 0].loglog(f0_values, delta_star_computed, 'bo-', linewidth=2, markersize=8, 
                         label='Computado')
        axes[0, 0].axhline(delta_theoretical, color='r', linestyle='--', linewidth=2,
                          label=f'Teórico: {delta_theoretical:.6f}')
        axes[0, 0].set_xlabel('Frecuencia f0 (Hz)', fontsize=11)
        axes[0, 0].set_ylabel('delta*', fontsize=11)
        axes[0, 0].set_title('Convergencia de delta*', fontsize=12, fontweight='bold')
        axes[0, 0].legend(fontsize=10)
        axes[0, 0].grid(True, alpha=0.3)
        
        # Magnitud de fuerza
        axes[0, 1].loglog(f0_values, forcing_magnitude, 'go-', linewidth=2, markersize=8)
        axes[0, 1].set_xlabel('Frecuencia f0 (Hz)', fontsize=11)
        axes[0, 1].set_ylabel('||epsilonnablaPhi||', fontsize=11)
        axes[0, 1].set_title('Decaimiento de Fuerza Oscilatoria', fontsize=12, fontweight='bold')
        axes[0, 1].grid(True, alpha=0.3)
        
        # Vorticidad L∞
        colors = cm.viridis(np.linspace(0, 1, len(f0_values)))
        for idx, f0 in enumerate(f0_values[::max(1, len(f0_values)//4)]):
            omega_inf = results[f0]['omega_inf']
            time = np.arange(len(omega_inf)) * 0.1
            axes[1, 0].semilogy(time, omega_inf, color=colors[idx], 
                              label=f'f0 = {f0:.0f} Hz', linewidth=2)
        axes[1, 0].set_xlabel('Tiempo', fontsize=11)
        axes[1, 0].set_ylabel('||omega||_∞', fontsize=11)
        axes[1, 0].set_title('Control de Vorticidad L∞', fontsize=12, fontweight='bold')
        axes[1, 0].legend(fontsize=9)
        axes[1, 0].grid(True, alpha=0.3)
        
        # Coeficiente de Riccati
        axes[1, 1].semilogx(f0_values, alpha_star_values, 'mo-', linewidth=2, markersize=8)
        axes[1, 1].axhline(0, color='k', linestyle='--', linewidth=1.5)
        axes[1, 1].fill_between(f0_values, -1, 0, alpha=0.2, color='green')
        axes[1, 1].set_xlabel('Frecuencia f0 (Hz)', fontsize=11)
        axes[1, 1].set_ylabel('alpha*', fontsize=11)
        axes[1, 1].set_title('Coeficiente de Riccati alpha*', fontsize=12, fontweight='bold')
        axes[1, 1].grid(True, alpha=0.3)
        
        plt.suptitle('Dashboard Completo: Análisis de Convergencia en Límite Dual', 
                    fontsize=16, fontweight='bold', y=0.995)
        plt.tight_layout()
        
        if save_name:
            plt.savefig(os.path.join(self.results_dir, save_name), dpi=300, bbox_inches='tight')
        else:
            plt.savefig(os.path.join(self.results_dir, 'dual_limit_convergence.png'), 
                       dpi=300, bbox_inches='tight')
        plt.close()
        
        print(f"Dashboard guardado en {self.results_dir}")


if __name__ == "__main__":
    # Ejemplo de uso
    visualizer = PsiNSVisualizer()
    
    # Datos de ejemplo
    f0_values = [100, 200, 500, 1000]
    results = {
        f0: {
            'delta_star': 0.025 + 0.01/f0,
            'omega_inf': np.exp(-np.linspace(0, 5, 50)/10) * np.random.rand(50),
            'delta': 0.025 + 0.01/f0 + 0.005*np.sin(np.linspace(0, 10, 50))
        }
        for f0 in f0_values
    }
    
    delta_theoretical = 0.0253
    forcing = [1.0 * f0**(1-2.0) for f0 in f0_values]
    alpha_star = [-0.01 - 0.001*f0 for f0 in f0_values]
    
    visualizer.create_comprehensive_dashboard(results, delta_theoretical, forcing, alpha_star)
    print("Visualización de ejemplo completada")
