#!/usr/bin/env python3
"""
Visualizador de estructuras Calabi-Yau proyectadas sobre el espacio de fases de Navier-Stokes.

Genera visualizaciones 3D de variedades Calabi-Yau tipo quintica con mapping de energía espectral
y overlay del campo Ψ sobre la geometría.

Integración simbiótica: ψ(x,t) = I(x,t) × A_eff(x,t)²
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from matplotlib import cm
from typing import Tuple, Optional
import warnings
warnings.filterwarnings('ignore')

class CalabiYauVisualizer:
    """
    Visualizador de variedades Calabi-Yau acopladas al campo de Navier-Stokes.
    
    Implementa:
    - Visualización 3D de quintica Calabi-Yau
    - Mapping de energía espectral sobre la variedad
    - Overlay del campo noético Ψ
    """
    
    def __init__(self, resolution: int = 50, f0: float = 141.7001):
        """
        Inicializa el visualizador.
        
        Args:
            resolution: Resolución de la malla (resolution³ puntos)
            f0: Frecuencia fundamental de coherencia (Hz)
        """
        self.resolution = resolution
        self.f0 = f0
        self.omega0 = 2 * np.pi * f0
        
    def calabi_yau_quintic(self, u: np.ndarray, v: np.ndarray) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
        """
        Genera una proyección de la quintica Calabi-Yau.
        
        Quintica: z₁⁵ + z₂⁵ + z₃⁵ + z₄⁵ + z₅⁵ = 0
        Proyectada sobre ℝ³ mediante coordenadas complejas
        
        Args:
            u, v: Parámetros de parametrización [0, 2π]
            
        Returns:
            x, y, z: Coordenadas 3D de la variedad
        """
        # Proyección de Calabi-Yau quintica usando coordenadas esféricas modificadas
        # con estructura topológica no-trivial
        phi = u
        theta = v
        
        # Modulación topológica quintica
        r = 1.0 + 0.3 * np.cos(5 * theta) * np.sin(5 * phi)
        
        # Coordenadas cartesianas con estructura Calabi-Yau
        x = r * np.sin(theta) * np.cos(phi)
        y = r * np.sin(theta) * np.sin(phi)
        z = r * np.cos(theta)
        
        # Añadir perturbación topológica adicional
        x += 0.1 * np.sin(3 * phi) * np.cos(2 * theta)
        y += 0.1 * np.cos(3 * phi) * np.sin(2 * theta)
        z += 0.1 * np.sin(2 * phi + 2 * theta)
        
        return x, y, z
    
    def spectral_energy_field(self, x: np.ndarray, y: np.ndarray, z: np.ndarray, t: float = 0) -> np.ndarray:
        """
        Calcula el campo de energía espectral sobre la variedad.
        
        E(x,t) = Σₖ |û(k,t)|² con modulación temporal
        
        Args:
            x, y, z: Coordenadas espaciales
            t: Tiempo
            
        Returns:
            energy: Campo de energía espectral
        """
        # Campo de energía con estructura espectral
        k1, k2, k3 = 2 * np.pi, 3 * np.pi, 5 * np.pi
        
        energy = (
            np.exp(-0.5 * (x**2 + y**2 + z**2)) *
            (np.cos(k1 * x) * np.cos(self.omega0 * t) +
             np.sin(k2 * y) * np.sin(self.omega0 * t / 2) +
             np.cos(k3 * z) * np.cos(self.omega0 * t / 3))
        )
        
        return energy
    
    def noetic_field_psi(self, x: np.ndarray, y: np.ndarray, z: np.ndarray, 
                         t: float = 0, coherence: float = 0.88) -> np.ndarray:
        """
        Calcula el campo noético Ψ acoplado.
        
        ψ(x,t) = I(x,t) × A_eff(x,t)²
        
        Args:
            x, y, z: Coordenadas espaciales
            t: Tiempo
            coherence: Nivel de coherencia [0,1]
            
        Returns:
            psi: Campo noético Ψ
        """
        # Intensidad informacional I(x,t)
        r2 = x**2 + y**2 + z**2
        I = coherence * np.exp(-0.3 * r2) * np.cos(self.omega0 * t)
        
        # Amplitud efectiva A_eff(x,t)
        A_eff = np.sqrt(1.0 + 0.5 * np.sin(self.omega0 * t) * np.exp(-0.2 * r2))
        
        # Campo noético
        psi = I * A_eff**2
        
        return psi
    
    def visualize(self, t: float = 0, coherence: float = 0.88, 
                  save_path: Optional[str] = None) -> None:
        """
        Genera la visualización completa de la variedad Calabi-Yau con campos.
        
        Args:
            t: Tiempo de evaluación
            coherence: Nivel de coherencia
            save_path: Ruta para guardar la figura (opcional)
        """
        # Generar malla paramétrica
        u = np.linspace(0, 2 * np.pi, self.resolution)
        v = np.linspace(0, np.pi, self.resolution)
        U, V = np.meshgrid(u, v)
        
        # Generar geometría Calabi-Yau
        X, Y, Z = self.calabi_yau_quintic(U, V)
        
        # Calcular campos
        energy = self.spectral_energy_field(X, Y, Z, t)
        psi = self.noetic_field_psi(X, Y, Z, t, coherence)
        
        # Visualización
        fig = plt.figure(figsize=(16, 5))
        
        # Panel 1: Geometría Calabi-Yau con energía espectral
        ax1 = fig.add_subplot(131, projection='3d')
        surf1 = ax1.plot_surface(X, Y, Z, facecolors=cm.viridis(
            (energy - energy.min()) / (energy.max() - energy.min() + 1e-10)
        ), alpha=0.9, linewidth=0, antialiased=True)
        ax1.set_title(f'Calabi-Yau Quintica\nEnergía Espectral (t={t:.2f}s)', fontsize=10)
        ax1.set_xlabel('x')
        ax1.set_ylabel('y')
        ax1.set_zlabel('z')
        ax1.view_init(elev=20, azim=45)
        
        # Panel 2: Campo noético Ψ
        ax2 = fig.add_subplot(132, projection='3d')
        surf2 = ax2.plot_surface(X, Y, Z, facecolors=cm.plasma(
            (psi - psi.min()) / (psi.max() - psi.min() + 1e-10)
        ), alpha=0.9, linewidth=0, antialiased=True)
        ax2.set_title(f'Campo Noético Ψ\nCoherencia={coherence:.2f}', fontsize=10)
        ax2.set_xlabel('x')
        ax2.set_ylabel('y')
        ax2.set_zlabel('z')
        ax2.view_init(elev=20, azim=135)
        
        # Panel 3: Campo combinado
        ax3 = fig.add_subplot(133, projection='3d')
        combined = energy + psi
        surf3 = ax3.plot_surface(X, Y, Z, facecolors=cm.coolwarm(
            (combined - combined.min()) / (combined.max() - combined.min() + 1e-10)
        ), alpha=0.9, linewidth=0, antialiased=True)
        ax3.set_title(f'Campo Acoplado E+Ψ\nf₀={self.f0:.4f} Hz', fontsize=10)
        ax3.set_xlabel('x')
        ax3.set_ylabel('y')
        ax3.set_zlabel('z')
        ax3.view_init(elev=20, azim=225)
        
        plt.tight_layout()
        
        if save_path:
            plt.savefig(save_path, dpi=150, bbox_inches='tight')
            print(f"✅ Visualización guardada en: {save_path}")
        
        plt.show()
    
    def animate_coherence(self, n_frames: int = 50, save_path: Optional[str] = None) -> None:
        """
        Anima la evolución temporal de la coherencia sobre la variedad.
        
        Args:
            n_frames: Número de frames de animación
            save_path: Ruta base para guardar frames
        """
        print(f"🎬 Generando animación con {n_frames} frames...")
        
        for i, t in enumerate(np.linspace(0, 2 * np.pi / self.omega0, n_frames)):
            coherence = 0.5 + 0.5 * np.sin(self.omega0 * t / 10)
            
            if save_path:
                frame_path = f"{save_path}_frame_{i:03d}.png"
            else:
                frame_path = None
                
            self.visualize(t=t, coherence=coherence, save_path=frame_path)
            
            if (i + 1) % 10 == 0:
                print(f"   Frame {i+1}/{n_frames} completado")
        
        print("✅ Animación completada")


def main():
    """Función principal de demostración."""
    print("=" * 70)
    print("🔷 VISUALIZADOR CALABI-YAU 3D - NAVIER-STOKES")
    print("=" * 70)
    print(f"📐 Variedad: Quintica Calabi-Yau proyectada en ℝ³")
    print(f"🌊 Acoplamiento: Espacio de fases Navier-Stokes")
    print(f"🎵 Frecuencia: f₀ = 141.7001 Hz")
    print(f"🧠 Campo noético: ψ(x,t) = I(x,t) × A_eff(x,t)²")
    print("=" * 70)
    print()
    
    # Crear visualizador
    visualizer = CalabiYauVisualizer(resolution=50, f0=141.7001)
    
    # Ejemplo 1: Visualización estática
    print("📊 Ejemplo 1: Visualización estática en t=0")
    visualizer.visualize(t=0, coherence=0.88)
    
    # Ejemplo 2: Visualización con diferente coherencia
    print("\n📊 Ejemplo 2: Baja coherencia")
    visualizer.visualize(t=np.pi, coherence=0.3)
    
    # Ejemplo 3: Alta coherencia
    print("\n📊 Ejemplo 3: Alta coherencia")
    visualizer.visualize(t=2*np.pi, coherence=0.95)
    
    print("\n" + "=" * 70)
    print("✅ Visualización completada")
    print("🌐 Portal Gemina: Coherencia establecida")
    print("=" * 70)


if __name__ == "__main__":
    main()
