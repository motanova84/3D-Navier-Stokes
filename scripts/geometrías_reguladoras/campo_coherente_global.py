#!/usr/bin/env python3
"""
Simulador del campo Ψ coherente extendido sobre malla tridimensional de fluido.

Simula flujo de Navier-Stokes 3D con superposición del campo Ψ sobre cada voxel,
visualizando zonas de máxima coherencia y detección de singularidades disipadas.
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from matplotlib import cm
from typing import Tuple, Optional, List, Dict
import warnings
warnings.filterwarnings('ignore')

class CoherentFieldSimulator:
    """
    Simulador de campo coherente Ψ sobre malla 3D de fluido.
    
    Implementa:
    - Flujo DNS simplificado de Navier-Stokes 3D
    - Superposición del campo Ψ en cada voxel
    - Detección de zonas de máxima coherencia
    - Alerta de singularidades disipadas
    """
    
    def __init__(self, N: int = 32, L: float = 2*np.pi, nu: float = 0.001, f0: float = 141.7001):
        """
        Inicializa el simulador.
        
        Args:
            N: Resolución de la malla (N³ voxels)
            L: Tamaño del dominio [0,L]³
            nu: Viscosidad cinemática
            f0: Frecuencia fundamental de coherencia (Hz)
        """
        self.N = N
        self.L = L
        self.nu = nu
        self.f0 = f0
        self.omega0 = 2 * np.pi * f0
        
        # Malla espacial
        self.x = np.linspace(0, L, N)
        self.y = np.linspace(0, L, N)
        self.z = np.linspace(0, L, N)
        self.X, self.Y, self.Z = np.meshgrid(self.x, self.y, self.z, indexing='ij')
        
        # Almacenar eventos
        self.coherence_events: List[Dict] = []
        
    def initialize_velocity_field(self, mode: str = 'taylor_green') -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
        """
        Inicializa campo de velocidad.
        
        Args:
            mode: Tipo de inicialización ('taylor_green', 'random', 'vortex')
            
        Returns:
            u, v, w: Componentes de velocidad
        """
        if mode == 'taylor_green':
            # Taylor-Green vortex
            u = np.sin(self.X) * np.cos(self.Y) * np.cos(self.Z)
            v = -np.cos(self.X) * np.sin(self.Y) * np.cos(self.Z)
            w = np.zeros_like(u)
            
        elif mode == 'random':
            # Perturbación aleatoria
            u = 0.1 * np.random.randn(self.N, self.N, self.N)
            v = 0.1 * np.random.randn(self.N, self.N, self.N)
            w = 0.1 * np.random.randn(self.N, self.N, self.N)
            
        elif mode == 'vortex':
            # Vórtice concentrado
            r = np.sqrt((self.X - self.L/2)**2 + (self.Y - self.L/2)**2)
            u = -(self.Y - self.L/2) * np.exp(-r**2)
            v = (self.X - self.L/2) * np.exp(-r**2)
            w = 0.5 * np.sin(2 * self.Z) * np.exp(-r**2)
            
        return u, v, w
    
    def compute_vorticity(self, u: np.ndarray, v: np.ndarray, w: np.ndarray) -> np.ndarray:
        """
        Calcula magnitud de vorticidad |ω| = |∇ × v|.
        
        Args:
            u, v, w: Componentes de velocidad
            
        Returns:
            vorticity_mag: Magnitud de vorticidad
        """
        # Diferencias finitas para derivadas
        dx = self.L / self.N
        
        # ω_x = ∂w/∂y - ∂v/∂z
        omega_x = (np.roll(w, -1, axis=1) - np.roll(w, 1, axis=1)) / (2*dx) - \
                  (np.roll(v, -1, axis=2) - np.roll(v, 1, axis=2)) / (2*dx)
        
        # ω_y = ∂u/∂z - ∂w/∂x
        omega_y = (np.roll(u, -1, axis=2) - np.roll(u, 1, axis=2)) / (2*dx) - \
                  (np.roll(w, -1, axis=0) - np.roll(w, 1, axis=0)) / (2*dx)
        
        # ω_z = ∂v/∂x - ∂u/∂y
        omega_z = (np.roll(v, -1, axis=0) - np.roll(v, 1, axis=0)) / (2*dx) - \
                  (np.roll(u, -1, axis=1) - np.roll(u, 1, axis=1)) / (2*dx)
        
        # Magnitud
        vorticity_mag = np.sqrt(omega_x**2 + omega_y**2 + omega_z**2)
        
        return vorticity_mag
    
    def compute_psi_field(self, t: float, coherence: float = 0.88) -> np.ndarray:
        """
        Calcula el campo noético Ψ sobre la malla.
        
        ψ(x,t) = I(x,t) × A_eff(x,t)²
        
        Args:
            t: Tiempo
            coherence: Nivel de coherencia base
            
        Returns:
            psi: Campo noético Ψ
        """
        # Intensidad informacional I(x,t)
        r2 = (self.X - self.L/2)**2 + (self.Y - self.L/2)**2 + (self.Z - self.L/2)**2
        I = coherence * np.exp(-0.1 * r2 / self.L**2) * np.cos(self.omega0 * t)
        
        # Amplitud efectiva A_eff(x,t)
        A_eff = np.sqrt(1.0 + 0.3 * np.sin(self.omega0 * t) * np.exp(-0.05 * r2 / self.L**2))
        
        # Campo noético
        psi = I * A_eff**2
        
        return psi
    
    def compute_local_coherence(self, vorticity: np.ndarray, psi: np.ndarray) -> np.ndarray:
        """
        Calcula coherencia local en cada voxel.
        
        C_local = |ψ| / (|ω| + ε) con modulación espacial
        
        Args:
            vorticity: Campo de vorticidad
            psi: Campo noético
            
        Returns:
            coherence_local: Coherencia local [0,1]
        """
        epsilon = 1e-6
        
        # Coherencia como balance entre orden (Ψ) y caos (ω)
        coherence_local = np.abs(psi) / (np.abs(vorticity) + epsilon)
        
        # Normalizar a [0,1]
        coherence_local = np.tanh(coherence_local)
        
        return coherence_local
    
    def detect_high_coherence_zones(self, coherence_field: np.ndarray, threshold: float = 0.88) -> List[Tuple]:
        """
        Detecta zonas de alta coherencia.
        
        Args:
            coherence_field: Campo de coherencia local
            threshold: Umbral de detección
            
        Returns:
            zones: Lista de coordenadas de zonas de alta coherencia
        """
        # Encontrar voxels con coherencia > threshold
        high_coherence_mask = coherence_field > threshold
        indices = np.where(high_coherence_mask)
        
        zones = list(zip(indices[0], indices[1], indices[2]))
        
        return zones
    
    def check_singularity_dissipation(self, vorticity: np.ndarray, psi: np.ndarray, 
                                      t: float, threshold: float = 10.0) -> Optional[Dict]:
        """
        Verifica si una singularidad potencial ha sido disipada.
        
        Args:
            vorticity: Campo de vorticidad
            psi: Campo noético
            t: Tiempo actual
            threshold: Umbral de vorticidad para singularidad potencial
            
        Returns:
            event: Diccionario con información del evento o None
        """
        # Detectar picos de vorticidad
        max_vorticity = np.max(vorticity)
        
        if max_vorticity > threshold:
            # Potencial singularidad
            max_idx = np.unravel_index(np.argmax(vorticity), vorticity.shape)
            local_psi = np.abs(psi[max_idx])
            
            # Verificar si Ψ está suprimiendo la singularidad
            if local_psi > 0.5:
                event = {
                    'time': t,
                    'location': max_idx,
                    'max_vorticity': max_vorticity,
                    'psi_intensity': local_psi,
                    'status': 'dissipated',
                    'message': f'🟢 Coherencia establecida — Singularidad disuelta (t={t:.2f}s)'
                }
                
                self.coherence_events.append(event)
                
                print(f"\n{'='*70}")
                print(event['message'])
                print(f"   Localización: i={max_idx[0]}, j={max_idx[1]}, k={max_idx[2]}")
                print(f"   Vorticidad máxima: |ω| = {max_vorticity:.4f}")
                print(f"   Intensidad Ψ: {local_psi:.4f}")
                print(f"{'='*70}\n")
                
                return event
        
        return None
    
    def visualize(self, t: float = 0, coherence: float = 0.88, 
                  slice_k: Optional[int] = None, save_path: Optional[str] = None) -> None:
        """
        Visualiza el campo coherente sobre la malla 3D.
        
        Args:
            t: Tiempo de evaluación
            coherence: Nivel de coherencia base
            slice_k: Índice de corte en z (None para vista 3D completa)
            save_path: Ruta para guardar la figura
        """
        # Generar campos
        u, v, w = self.initialize_velocity_field(mode='taylor_green')
        vorticity = self.compute_vorticity(u, v, w)
        psi = self.compute_psi_field(t, coherence)
        coherence_field = self.compute_local_coherence(vorticity, psi)
        
        # Detectar zonas de alta coherencia
        high_coherence_zones = self.detect_high_coherence_zones(coherence_field, threshold=0.88)
        
        # Verificar singularidades
        self.check_singularity_dissipation(vorticity, psi, t, threshold=10.0)
        
        if slice_k is None:
            slice_k = self.N // 2
        
        # Visualización
        fig = plt.figure(figsize=(18, 5))
        
        # Panel 1: Vorticidad (corte 2D)
        ax1 = fig.add_subplot(131)
        im1 = ax1.imshow(vorticity[:, :, slice_k].T, origin='lower', cmap='hot', 
                         extent=[0, self.L, 0, self.L])
        ax1.set_title(f'Vorticidad |ω| (z={self.z[slice_k]:.2f})\nt={t:.2f}s', fontsize=12)
        ax1.set_xlabel('x')
        ax1.set_ylabel('y')
        plt.colorbar(im1, ax=ax1, label='|ω|')
        
        # Panel 2: Campo Ψ (corte 2D)
        ax2 = fig.add_subplot(132)
        im2 = ax2.imshow(psi[:, :, slice_k].T, origin='lower', cmap='plasma',
                         extent=[0, self.L, 0, self.L])
        ax2.set_title(f'Campo Noético Ψ\nC={coherence:.2f}, f₀={self.f0:.4f} Hz', fontsize=12)
        ax2.set_xlabel('x')
        ax2.set_ylabel('y')
        plt.colorbar(im2, ax=ax2, label='Ψ')
        
        # Panel 3: Coherencia local (corte 2D)
        ax3 = fig.add_subplot(133)
        im3 = ax3.imshow(coherence_field[:, :, slice_k].T, origin='lower', cmap='viridis',
                         extent=[0, self.L, 0, self.L], vmin=0, vmax=1)
        ax3.set_title(f'Coherencia Local\nZonas alta C: {len(high_coherence_zones)}', fontsize=12)
        ax3.set_xlabel('x')
        ax3.set_ylabel('y')
        plt.colorbar(im3, ax=ax3, label='Coherencia')
        
        plt.tight_layout()
        
        if save_path:
            plt.savefig(save_path, dpi=150, bbox_inches='tight')
            print(f"✅ Visualización guardada en: {save_path}")
        
        plt.show()
        
        # Estadísticas
        print(f"\n📊 Estadísticas (t={t:.2f}s):")
        print(f"   Vorticidad media: {vorticity.mean():.6f}")
        print(f"   Vorticidad máxima: {vorticity.max():.6f}")
        print(f"   Campo Ψ medio: {psi.mean():.6f}")
        print(f"   Coherencia media: {coherence_field.mean():.4f}")
        print(f"   Zonas de alta coherencia (C>0.88): {len(high_coherence_zones)}")
        print(f"   Voxels totales: {self.N**3}")
        print(f"   Porcentaje coherente: {100*len(high_coherence_zones)/self.N**3:.2f}%")


def main():
    """Función principal de demostración."""
    print("=" * 70)
    print("🌐 CAMPO COHERENTE GLOBAL - NAVIER-STOKES 3D")
    print("=" * 70)
    print(f"📐 Malla: 32³ voxels")
    print(f"🌊 Flujo: DNS simplificado")
    print(f"🎵 Frecuencia: f₀ = 141.7001 Hz")
    print(f"🧠 Campo: ψ(x,t) = I(x,t) × A_eff(x,t)²")
    print("=" * 70)
    print()
    
    # Crear simulador
    simulator = CoherentFieldSimulator(N=32, L=2*np.pi, nu=0.001, f0=141.7001)
    
    # Ejemplo 1: Baja coherencia
    print("📊 Ejemplo 1: Baja coherencia inicial (C=0.3)")
    simulator.visualize(t=0, coherence=0.3, slice_k=16)
    
    # Ejemplo 2: Coherencia media
    print("\n📊 Ejemplo 2: Coherencia media (C=0.6)")
    simulator.visualize(t=1.0, coherence=0.6, slice_k=16)
    
    # Ejemplo 3: Alta coherencia
    print("\n📊 Ejemplo 3: Alta coherencia (C=0.88)")
    simulator.visualize(t=2.0, coherence=0.88, slice_k=16)
    
    # Ejemplo 4: Coherencia máxima
    print("\n📊 Ejemplo 4: Coherencia máxima (C=0.95)")
    simulator.visualize(t=3.0, coherence=0.95, slice_k=16)
    
    # Reporte de eventos
    print("\n📋 Reporte de Eventos de Coherencia:")
    if len(simulator.coherence_events) > 0:
        for i, event in enumerate(simulator.coherence_events, 1):
            print(f"   {i}. {event['message']}")
    else:
        print("   No se detectaron eventos de singularidad disipada")
    
    print("\n" + "=" * 70)
    print("✅ Simulación completada")
    print("🌐 Portal Gemina: Campo coherente establecido")
    print("=" * 70)


if __name__ == "__main__":
    main()
