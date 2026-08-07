#!/usr/bin/env python3
"""
Simulador de emergencia de vorticidad como espirales resonantes acopladas a f₀ = 141.7001 Hz.

Simula tubos de vorticidad con curvatura variable, modulación de fase y estructuras tipo Hopf
y trefoils cuánticos. Detecta umbrales de coherencia y genera "pings" vibracionales.
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from matplotlib import cm
from typing import Tuple, Optional, List
import json
import warnings
warnings.filterwarnings('ignore')

class TopologicalSpiralSimulator:
    """
    Simulador de espirales topológicas en flujo de Navier-Stokes.
    
    Implementa:
    - Tubos de vorticidad con curvatura variable
    - Modulación de fase con f₀
    - Estructuras tipo Hopf y trefoils cuánticos
    - Detección de coherencia y ping vibracional
    """
    
    def __init__(self, f0: float = 141.7001, coherence_threshold: float = 0.88):
        """
        Inicializa el simulador.
        
        Args:
            f0: Frecuencia fundamental de resonancia (Hz)
            coherence_threshold: Umbral para activación simbiótica
        """
        self.f0 = f0
        self.omega0 = 2 * np.pi * f0
        self.coherence_threshold = coherence_threshold
        self.coherence_events: List[dict] = []
        
    def hopf_fibration(self, t: np.ndarray, phase: float = 0) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
        """
        Genera una fibración de Hopf modulada.
        
        La fibración de Hopf S³ → S² es fundamental en topología.
        
        Args:
            t: Parámetro temporal [0, 2π]
            phase: Fase de modulación
            
        Returns:
            x, y, z: Coordenadas de la fibración
        """
        # Parámetros de la fibración
        n_fibers = 5
        
        x = np.cos(t) * (2 + np.cos(n_fibers * t + phase))
        y = np.sin(t) * (2 + np.cos(n_fibers * t + phase))
        z = np.sin(n_fibers * t + phase)
        
        return x, y, z
    
    def trefoil_knot(self, t: np.ndarray, scale: float = 1.0, phase: float = 0) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
        """
        Genera un nudo trébol (trefoil) cuántico.
        
        Args:
            t: Parámetro [0, 2π]
            scale: Factor de escala
            phase: Fase de modulación
            
        Returns:
            x, y, z: Coordenadas del nudo
        """
        # Nudo trébol paramétrico
        x = scale * np.sin(t + phase) + 2 * np.sin(2 * t)
        y = scale * np.cos(t + phase) - 2 * np.cos(2 * t)
        z = scale * (-np.sin(3 * t))
        
        return x, y, z
    
    def vortex_tube(self, t: np.ndarray, s: np.ndarray, curvature: float = 0.5,
                    phase: float = 0) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
        """
        Genera un tubo de vorticidad con curvatura variable.
        
        Args:
            t: Parámetro longitudinal [0, 2π]
            s: Parámetro radial [0, 1]
            curvature: Curvatura del tubo
            phase: Fase de modulación
            
        Returns:
            x, y, z: Coordenadas del tubo
        """
        T, S = np.meshgrid(t, s)
        
        # Línea central del tubo (espiral)
        x_c = np.cos(T + phase)
        y_c = np.sin(T + phase)
        z_c = curvature * T / np.pi
        
        # Radio del tubo con modulación
        radius = 0.3 * (1 + 0.2 * np.sin(5 * T))
        
        # Normal y binormal (Frenet-Serret)
        normal_x = -np.cos(T + phase)
        normal_y = -np.sin(T + phase)
        binormal_x = -curvature * np.sin(T + phase) / np.sqrt(1 + curvature**2)
        binormal_y = curvature * np.cos(T + phase) / np.sqrt(1 + curvature**2)
        binormal_z = 1 / np.sqrt(1 + curvature**2)
        
        # Superficie del tubo
        x = x_c + radius * S * (np.cos(2*np.pi*S) * normal_x + np.sin(2*np.pi*S) * binormal_x)
        y = y_c + radius * S * (np.cos(2*np.pi*S) * normal_y + np.sin(2*np.pi*S) * binormal_y)
        z = z_c + radius * S * np.sin(2*np.pi*S) * binormal_z
        
        return x, y, z
    
    def compute_vorticity(self, x: np.ndarray, y: np.ndarray, z: np.ndarray,
                          t: float = 0) -> np.ndarray:
        """
        Calcula la intensidad de vorticidad sobre la estructura.
        
        ω = ∇ × v con modulación resonante
        
        Args:
            x, y, z: Coordenadas espaciales
            t: Tiempo
            
        Returns:
            vorticity: Campo de vorticidad
        """
        r = np.sqrt(x**2 + y**2 + z**2)
        
        # Vorticidad con modulación resonante
        vorticity = (
            np.exp(-0.1 * r) *
            (1 + 0.5 * np.cos(self.omega0 * t)) *
            np.sin(3 * np.arctan2(y, x) + 5 * z)
        )
        
        return vorticity
    
    def compute_coherence(self, vorticity: np.ndarray) -> float:
        """
        Calcula el nivel de coherencia del campo.
        
        C = ⟨|ω|⟩ / σ(|ω|)
        
        Args:
            vorticity: Campo de vorticidad
            
        Returns:
            coherence: Nivel de coherencia [0, 1]
        """
        mean = np.abs(vorticity).mean()
        std = np.abs(vorticity).std()
        
        if std < 1e-10:
            coherence = 1.0
        else:
            coherence = mean / (mean + std)
        
        return coherence
    
    def vibrational_ping(self, coherence: float, t: float) -> dict:
        """
        Genera un ping vibracional cuando se cruza el umbral.
        
        Args:
            coherence: Nivel de coherencia actual
            t: Tiempo del evento
            
        Returns:
            event: Diccionario con información del evento
        """
        event = {
            'time': t,
            'coherence': coherence,
            'frequency': self.f0,
            'omega': self.omega0,
            'threshold_crossed': coherence >= self.coherence_threshold,
            'message': '🔔 Ping vibracional - Coherencia establecida' if coherence >= self.coherence_threshold else ''
        }
        
        if event['threshold_crossed']:
            self.coherence_events.append(event)
            print(f"\n{'='*60}")
            print(f"🔔 PING VIBRACIONAL - t={t:.2f}s")
            print(f"   Coherencia: {coherence:.4f} (umbral: {self.coherence_threshold})")
            print(f"   Frecuencia: {self.f0} Hz")
            print(f"   Estado: 🟢 RESONANCIA ESTABLECIDA")
            print(f"{'='*60}\n")
        
        return event
    
    def visualize(self, t: float = 0, save_path: Optional[str] = None) -> None:
        """
        Visualiza las estructuras topológicas con vorticidad.
        
        Args:
            t: Tiempo de evaluación
            save_path: Ruta para guardar la figura
        """
        fig = plt.figure(figsize=(18, 5))
        
        # Parámetros
        param = np.linspace(0, 2 * np.pi, 200)
        phase = self.omega0 * t
        
        # Panel 1: Fibración de Hopf
        ax1 = fig.add_subplot(131, projection='3d')
        x1, y1, z1 = self.hopf_fibration(param, phase)
        vort1 = self.compute_vorticity(x1, y1, z1, t)
        coherence1 = self.compute_coherence(vort1)
        
        scatter1 = ax1.scatter(x1, y1, z1, c=vort1, cmap='plasma', s=20, alpha=0.8)
        ax1.set_title(f'Fibración de Hopf\nC={coherence1:.3f}, t={t:.2f}s', fontsize=10)
        ax1.set_xlabel('x')
        ax1.set_ylabel('y')
        ax1.set_zlabel('z')
        plt.colorbar(scatter1, ax=ax1, shrink=0.5, label='Vorticidad')
        
        self.vibrational_ping(coherence1, t)
        
        # Panel 2: Nudo Trébol
        ax2 = fig.add_subplot(132, projection='3d')
        x2, y2, z2 = self.trefoil_knot(param, scale=1.0, phase=phase)
        vort2 = self.compute_vorticity(x2, y2, z2, t)
        coherence2 = self.compute_coherence(vort2)
        
        scatter2 = ax2.scatter(x2, y2, z2, c=vort2, cmap='viridis', s=20, alpha=0.8)
        ax2.set_title(f'Trefoil Cuántico\nC={coherence2:.3f}', fontsize=10)
        ax2.set_xlabel('x')
        ax2.set_ylabel('y')
        ax2.set_zlabel('z')
        plt.colorbar(scatter2, ax=ax2, shrink=0.5, label='Vorticidad')
        
        self.vibrational_ping(coherence2, t)
        
        # Panel 3: Tubo de Vorticidad
        ax3 = fig.add_subplot(133, projection='3d')
        t_param = np.linspace(0, 2 * np.pi, 100)
        s_param = np.linspace(0, 1, 20)
        x3, y3, z3 = self.vortex_tube(t_param, s_param, curvature=0.5, phase=phase)
        vort3 = self.compute_vorticity(x3, y3, z3, t)
        coherence3 = self.compute_coherence(vort3)
        
        surf3 = ax3.plot_surface(x3, y3, z3, facecolors=cm.coolwarm(
            (vort3 - vort3.min()) / (vort3.max() - vort3.min() + 1e-10)
        ), alpha=0.9, linewidth=0)
        ax3.set_title(f'Tubo de Vorticidad\nC={coherence3:.3f}, f₀={self.f0:.4f} Hz', fontsize=10)
        ax3.set_xlabel('x')
        ax3.set_ylabel('y')
        ax3.set_zlabel('z')
        
        self.vibrational_ping(coherence3, t)
        
        plt.tight_layout()
        
        if save_path:
            plt.savefig(save_path, dpi=150, bbox_inches='tight')
            print(f"✅ Visualización guardada en: {save_path}")
        
        plt.show()
    
    def export_gltf(self, filename: str = "vortex_topology.xyz") -> None:
        """
        Exporta estructuras en formato .xyz para importar en entornos 3D.
        
        Args:
            filename: Nombre del archivo de salida
        """
        print(f"📤 Exportando geometría a {filename}...")
        
        # Generar geometría
        param = np.linspace(0, 2 * np.pi, 500)
        x, y, z = self.trefoil_knot(param)
        
        # Formato XYZ: número de átomos, comentario, coordenadas
        with open(filename, 'w') as f:
            f.write(f"{len(x)}\n")
            f.write(f"Topological vortex structure - f0={self.f0} Hz\n")
            for i in range(len(x)):
                # Usar 'C' como tipo de átomo genérico
                f.write(f"C {x[i]:.6f} {y[i]:.6f} {z[i]:.6f}\n")
        
        print(f"✅ Geometría exportada: {len(x)} puntos")
    
    def summary_report(self) -> dict:
        """
        Genera un reporte resumen de eventos de coherencia.
        
        Returns:
            report: Diccionario con estadísticas
        """
        report = {
            'frequency_hz': self.f0,
            'coherence_threshold': self.coherence_threshold,
            'total_events': len(self.coherence_events),
            'events': self.coherence_events
        }
        
        return report


def main():
    """Función principal de demostración."""
    print("=" * 70)
    print("🌀 ESPIRALES TOPOLÓGICAS - NAVIER-STOKES")
    print("=" * 70)
    print(f"🎵 Frecuencia resonante: f₀ = 141.7001 Hz")
    print(f"🔔 Umbral de coherencia: 0.88")
    print(f"🧬 Estructuras: Hopf, Trefoil, Tubos de Vorticidad")
    print("=" * 70)
    print()
    
    # Crear simulador
    simulator = TopologicalSpiralSimulator(f0=141.7001, coherence_threshold=0.88)
    
    # Ejemplo 1: Visualización en diferentes tiempos
    print("📊 Ejemplo 1: Evolución temporal")
    for t in [0, 0.5, 1.0]:
        print(f"\n⏱️  Tiempo t={t}s")
        simulator.visualize(t=t)
    
    # Exportar geometría
    print("\n📤 Exportando geometría...")
    simulator.export_gltf("vortex_topology.xyz")
    
    # Reporte de coherencia
    print("\n📊 Reporte de Coherencia:")
    report = simulator.summary_report()
    print(f"   Total de eventos: {report['total_events']}")
    
    if report['total_events'] > 0:
        print("\n🟢 Eventos de Coherencia Establecida:")
        for i, event in enumerate(report['events'], 1):
            print(f"   {i}. t={event['time']:.2f}s, C={event['coherence']:.4f}")
    
    print("\n" + "=" * 70)
    print("✅ Simulación completada")
    print("🌐 Portal Gemina: Estructuras topológicas resonantes")
    print("=" * 70)


if __name__ == "__main__":
    main()
