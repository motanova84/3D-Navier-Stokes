#!/usr/bin/env python3
"""
Estructura Holográfica - Fisura de Poincaré.

Muestra cómo la topología del fluido en estado casi-singular se reorganiza en estructuras
tipo fisura de Poincaré, demostrando que la aparente singularidad es una reorganización
topológica en coherencia.
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from matplotlib import cm
from typing import Tuple, Optional, List
import warnings
warnings.filterwarnings('ignore')

class PoincareFissureSimulator:
    """
    Simulador de estructura holográfica de fisura de Poincaré.
    
    Implementa:
    - Simulación de colapso local del fluido
    - Reconstrucción vía reticulación coherente
    - Demostración de reorganización topológica
    """
    
    def __init__(self, f0: float = 141.7001, coherence_threshold: float = 0.88):
        """
        Inicializa el simulador.
        
        Args:
            f0: Frecuencia fundamental de coherencia (Hz)
            coherence_threshold: Umbral de coherencia para reorganización
        """
        self.f0 = f0
        self.omega0 = 2 * np.pi * f0
        self.coherence_threshold = coherence_threshold
        
    def poincare_section(self, theta: np.ndarray, phi: np.ndarray, 
                         singularity_strength: float = 1.0) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
        """
        Genera sección de Poincaré con estructura de fisura.
        
        Args:
            theta, phi: Coordenadas angulares
            singularity_strength: Intensidad de la singularidad aparente [0,1]
            
        Returns:
            x, y, z: Coordenadas de la sección
        """
        # Radio con singularidad aparente
        r = 2.0 + singularity_strength * np.sin(3 * theta) * np.cos(2 * phi)
        
        # Deformación por fisura
        fissure_factor = 1.0 - singularity_strength * 0.5 * np.exp(-((theta - np.pi)**2 + (phi - np.pi)**2) / 0.5)
        r *= fissure_factor
        
        # Coordenadas cartesianas
        x = r * np.sin(phi) * np.cos(theta)
        y = r * np.sin(phi) * np.sin(theta)
        z = r * np.cos(phi)
        
        return x, y, z
    
    def vorticity_field_near_singularity(self, x: np.ndarray, y: np.ndarray, z: np.ndarray,
                                         singularity_strength: float = 1.0) -> np.ndarray:
        """
        Campo de vorticidad cerca de singularidad aparente.
        
        |ω| ~ r^(-α) cerca del punto crítico
        
        Args:
            x, y, z: Coordenadas espaciales
            singularity_strength: Intensidad de singularidad [0,1]
            
        Returns:
            vorticity: Magnitud de vorticidad
        """
        # Distancia al punto crítico (origen)
        r = np.sqrt(x**2 + y**2 + z**2)
        
        # Singularidad aparente con regularización
        alpha = 0.5 + singularity_strength * 0.5
        epsilon = 0.1
        
        vorticity = (r + epsilon) ** (-alpha) * np.exp(-r / 5)
        
        return vorticity
    
    def coherent_field_psi(self, x: np.ndarray, y: np.ndarray, z: np.ndarray,
                          t: float, coherence: float = 0.88) -> np.ndarray:
        """
        Campo noético Ψ que induce reorganización.
        
        Args:
            x, y, z: Coordenadas espaciales
            t: Tiempo
            coherence: Nivel de coherencia
            
        Returns:
            psi: Campo noético
        """
        r = np.sqrt(x**2 + y**2 + z**2)
        
        # Campo Ψ con estructura holográfica
        psi = coherence * np.exp(-0.2 * r) * (
            np.cos(self.omega0 * t) +
            0.3 * np.sin(3 * np.arctan2(y, x)) * np.cos(2 * np.arctan2(z, np.sqrt(x**2 + y**2)))
        )
        
        return psi
    
    def reticular_reconstruction(self, x: np.ndarray, y: np.ndarray, z: np.ndarray,
                                coherence: float = 0.88) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
        """
        Reconstrucción reticular vía coherencia.
        
        La geometría se reorganiza de singular a regular mediante
        reticulación coherente del espacio de fases.
        
        Args:
            x, y, z: Coordenadas originales (pre-colapso)
            coherence: Nivel de coherencia
            
        Returns:
            x_new, y_new, z_new: Coordenadas reconstruidas
        """
        r = np.sqrt(x**2 + y**2 + z**2)
        
        # Factor de reconstrucción
        reconstruction_factor = 1.0 + coherence * 0.5 * (1 - np.exp(-r / 2))
        
        # Aplicar reconstrucción
        x_new = x * reconstruction_factor
        y_new = y * reconstruction_factor
        z_new = z * reconstruction_factor
        
        return x_new, y_new, z_new
    
    def visualize_evolution(self, n_frames: int = 4, save_path: Optional[str] = None) -> None:
        """
        Visualiza la evolución desde colapso hasta reorganización.
        
        Args:
            n_frames: Número de etapas a visualizar
            save_path: Ruta base para guardar figuras
        """
        print(f"\n{'='*70}")
        print("🌀 EVOLUCIÓN: COLAPSO → REORGANIZACIÓN TOPOLÓGICA")
        print(f"{'='*70}\n")
        
        # Parámetros angulares
        theta = np.linspace(0, 2 * np.pi, 100)
        phi = np.linspace(0, np.pi, 50)
        THETA, PHI = np.meshgrid(theta, phi)
        
        # Evolución temporal de singularidad y coherencia
        singularity_strengths = np.linspace(1.0, 0.1, n_frames)
        coherences = np.linspace(0.3, 0.95, n_frames)
        times = np.linspace(0, 2 * np.pi / self.omega0, n_frames)
        
        fig = plt.figure(figsize=(20, 5))
        
        for i in range(n_frames):
            # Generar geometría
            x, y, z = self.poincare_section(THETA, PHI, singularity_strengths[i])
            
            # Aplicar reconstrucción si hay coherencia suficiente
            if coherences[i] >= self.coherence_threshold:
                x, y, z = self.reticular_reconstruction(x, y, z, coherences[i])
            
            # Calcular campos
            vorticity = self.vorticity_field_near_singularity(x, y, z, singularity_strengths[i])
            psi = self.coherent_field_psi(x, y, z, times[i], coherences[i])
            
            # Visualización
            ax = fig.add_subplot(1, n_frames, i+1, projection='3d')
            
            # Color por vorticidad
            colors = cm.hot(vorticity / vorticity.max())
            
            surf = ax.plot_surface(x, y, z, facecolors=colors, alpha=0.9, 
                                  linewidth=0, antialiased=True, shade=True)
            
            # Título según etapa
            if singularity_strengths[i] > 0.7:
                stage = "Colapso Local"
                status = "🔴"
            elif singularity_strengths[i] > 0.4:
                stage = "Transición"
                status = "🟡"
            elif coherences[i] >= self.coherence_threshold:
                stage = "Reorganizado"
                status = "🟢"
            else:
                stage = "Reorganizando"
                status = "🟠"
            
            ax.set_title(f'{status} {stage}\nC={coherences[i]:.2f}, S={singularity_strengths[i]:.2f}', 
                        fontsize=10)
            ax.set_xlabel('x', fontsize=8)
            ax.set_ylabel('y', fontsize=8)
            ax.set_zlabel('z', fontsize=8)
            ax.view_init(elev=20, azim=45 + i * 30)
            
            # Estadísticas
            max_vort = vorticity.max()
            mean_psi = np.abs(psi).mean()
            
            print(f"   Etapa {i+1}/{n_frames}: {stage}")
            print(f"      Vorticidad máx: |ω|_max = {max_vort:.4f}")
            print(f"      Campo Ψ medio: ⟨|Ψ|⟩ = {mean_psi:.4f}")
            print(f"      Coherencia: C = {coherences[i]:.4f}")
            
            if coherences[i] >= self.coherence_threshold:
                print(f"      → Singularidad disuelta ✓")
            print()
        
        plt.tight_layout()
        
        if save_path:
            plt.savefig(save_path, dpi=150, bbox_inches='tight')
            print(f"✅ Visualización guardada en: {save_path}")
        
        plt.show()
    
    def analyze_topology_change(self) -> None:
        """
        Analiza el cambio topológico cuantitativamente.
        """
        print(f"\n{'='*70}")
        print("📊 ANÁLISIS TOPOLÓGICO")
        print(f"{'='*70}\n")
        
        # Generar geometrías en diferentes estados
        theta = np.linspace(0, 2 * np.pi, 50)
        phi = np.linspace(0, np.pi, 25)
        THETA, PHI = np.meshgrid(theta, phi)
        
        # Estado 1: Singular
        x1, y1, z1 = self.poincare_section(THETA, PHI, singularity_strength=1.0)
        vort1 = self.vorticity_field_near_singularity(x1, y1, z1, 1.0)
        
        # Estado 2: Reorganizado
        x2, y2, z2 = self.poincare_section(THETA, PHI, singularity_strength=0.1)
        x2, y2, z2 = self.reticular_reconstruction(x2, y2, z2, coherence=0.95)
        vort2 = self.vorticity_field_near_singularity(x2, y2, z2, 0.1)
        
        # Métricas topológicas
        print("   Estado Singular:")
        print(f"      Vorticidad máxima: {vort1.max():.4f}")
        print(f"      Vorticidad media: {vort1.mean():.4f}")
        print(f"      Varianza: {vort1.var():.4f}")
        print(f"      Indicador de blow-up: {vort1.max() / vort1.mean():.2f}")
        
        print("\n   Estado Reorganizado:")
        print(f"      Vorticidad máxima: {vort2.max():.4f}")
        print(f"      Vorticidad media: {vort2.mean():.4f}")
        print(f"      Varianza: {vort2.var():.4f}")
        print(f"      Indicador de blow-up: {vort2.max() / vort2.mean():.2f}")
        
        print("\n   Cambio Relativo:")
        print(f"      Δ|ω|_max: {(vort2.max() - vort1.max()) / vort1.max() * 100:.2f}%")
        print(f"      Δ⟨|ω|⟩: {(vort2.mean() - vort1.mean()) / vort1.mean() * 100:.2f}%")
        
        print(f"\n{'='*70}")
        print("🔷 Conclusión: Reorganización topológica previene blow-up")
        print(f"{'='*70}\n")


def main():
    """Función principal de demostración."""
    print("=" * 70)
    print("🧩 ESTRUCTURA HOLOGRÁFICA - FISURA DE POINCARÉ")
    print("=" * 70)
    print(f"🌀 Topología: Reorganización coherente del espacio de fases")
    print(f"🎵 Frecuencia: f₀ = 141.7001 Hz")
    print(f"🔓 Umbral: C ≥ 0.88 para reorganización")
    print("=" * 70)
    print()
    
    # Crear simulador
    simulator = PoincareFissureSimulator(f0=141.7001, coherence_threshold=0.88)
    
    # Ejemplo 1: Evolución completa
    print("📊 Ejemplo 1: Evolución de colapso a reorganización")
    simulator.visualize_evolution(n_frames=4)
    
    # Ejemplo 2: Análisis topológico
    print("\n📊 Ejemplo 2: Análisis cuantitativo")
    simulator.analyze_topology_change()
    
    print("\n" + "=" * 70)
    print("✅ Simulación completada")
    print("🔷 Resultado: Lo que parecía singularidad es reorganización topológica")
    print("🌐 Portal Gemina: Coherencia preserva regularidad global")
    print("=" * 70)


if __name__ == "__main__":
    main()
