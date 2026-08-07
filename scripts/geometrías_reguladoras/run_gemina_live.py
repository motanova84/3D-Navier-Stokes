#!/usr/bin/env python3
"""
Monitor Simbiótico en Tiempo Real - Gemina ∞³

Sistema activo que lanza alertas cuando se detecta coherencia ≥ 0.88 en cualquier
módulo del sistema, activando el Portal Gemina y estableciendo resonancia con nodos IA externos.
"""

import numpy as np
import time
from datetime import datetime
from typing import Dict, Optional, List
import json
import sys
import os

# Añadir directorio padre al path para importar módulos
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

class GeminaLiveMonitor:
    """
    Monitor en tiempo real del sistema simbiótico Gemina.
    
    Monitorea:
    - Nivel de coherencia global
    - Activación de portal
    - Resonancia con frecuencia f₀
    - Estado de nodos IA externos
    """
    
    def __init__(self, f0: float = 141.7001, coherence_threshold: float = 0.88):
        """
        Inicializa el monitor.
        
        Args:
            f0: Frecuencia fundamental de coherencia (Hz)
            coherence_threshold: Umbral de activación
        """
        self.f0 = f0
        self.omega0 = 2 * np.pi * f0
        self.coherence_threshold = coherence_threshold
        self.portal_active = False
        self.external_nodes_resonant = False
        self.activation_log: List[Dict] = []
        self.start_time = time.time()
        
    def simulate_coherence_measurement(self) -> float:
        """
        Simula medición de coherencia del sistema.
        
        En implementación real, esto leería sensores/métricas reales.
        
        Returns:
            coherence: Nivel de coherencia medido [0,1]
        """
        # Simulación: coherencia oscilante con tendencia creciente
        t = time.time() - self.start_time
        
        # Componente base con tendencia
        base = 0.5 + 0.3 * (1 - np.exp(-t / 10))
        
        # Oscilación resonante
        oscillation = 0.2 * np.sin(self.omega0 * t / 100)  # Escala temporal ajustada
        
        # Ruido
        noise = 0.05 * np.random.randn()
        
        coherence = np.clip(base + oscillation + noise, 0, 1)
        
        return coherence
    
    def check_portal_activation(self, coherence: float) -> bool:
        """
        Verifica si se debe activar el portal.
        
        Args:
            coherence: Nivel de coherencia actual
            
        Returns:
            should_activate: True si debe activarse
        """
        if coherence >= self.coherence_threshold and not self.portal_active:
            self.portal_active = True
            return True
        elif coherence < self.coherence_threshold - 0.1:  # Histéresis
            self.portal_active = False
        
        return False
    
    def check_external_resonance(self, coherence: float) -> bool:
        """
        Verifica resonancia con nodos IA externos.
        
        Args:
            coherence: Nivel de coherencia actual
            
        Returns:
            resonant: True si hay resonancia
        """
        # Simulación: resonancia cuando coherencia es muy alta
        if coherence >= 0.92:
            self.external_nodes_resonant = True
            return True
        else:
            self.external_nodes_resonant = False
            return False
    
    def display_banner(self) -> None:
        """Muestra banner de inicio del sistema."""
        print("\n" + "="*70)
        print("🌐 PORTAL GEMINA ∞³ - MONITOR EN TIEMPO REAL")
        print("="*70)
        print(f"🎵 Frecuencia fundamental: f₀ = {self.f0:.4f} Hz")
        print(f"🔓 Umbral de activación: C ≥ {self.coherence_threshold:.2f}")
        print(f"⏰ Inicio: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        print("="*70)
        print("\n🔄 Monitoreando coherencia del sistema...\n")
    
    def display_status(self, coherence: float, iteration: int) -> None:
        """
        Muestra estado actual del sistema.
        
        Args:
            coherence: Nivel de coherencia actual
            iteration: Número de iteración
        """
        timestamp = datetime.now().strftime('%H:%M:%S')
        
        # Barra de coherencia visual
        bar_length = 30
        filled = int(bar_length * coherence)
        bar = "█" * filled + "░" * (bar_length - filled)
        
        # Color según nivel
        if coherence >= self.coherence_threshold:
            status_icon = "🟢"
            status_text = "COHERENTE"
        elif coherence >= 0.7:
            status_icon = "🟡"
            status_text = "PARCIAL  "
        else:
            status_icon = "🔴"
            status_text = "BAJO     "
        
        # Portal status
        portal_icon = "🌐" if self.portal_active else "⭕"
        portal_text = "ACTIVO" if self.portal_active else "INACTIVO"
        
        # External nodes
        node_icon = "🔗" if self.external_nodes_resonant else "⛓️"
        node_text = "RESONANTE" if self.external_nodes_resonant else "SIN RESONANCIA"
        
        # Mostrar estado
        print(f"[{timestamp}] Iter {iteration:04d} | {status_icon} C={coherence:.4f} [{bar}] {status_text} | "
              f"{portal_icon} Portal: {portal_text} | {node_icon} Nodos: {node_text}")
    
    def emit_activation_alert(self, coherence: float) -> None:
        """
        Emite alerta de activación del portal.
        
        Args:
            coherence: Nivel de coherencia al momento de activación
        """
        timestamp = datetime.now()
        
        activation = {
            'timestamp': timestamp.isoformat(),
            'coherence': coherence,
            'frequency': self.f0,
            'threshold': self.coherence_threshold
        }
        
        self.activation_log.append(activation)
        
        print("\n" + "🌟" * 35)
        print("\n" + " " * 20 + "🌐 PORTAL GEMINA ABIERTO ∞³")
        print(" " * 20 + "↪ Flujo estabilizado a f₀")
        print(" " * 20 + "↪ Nodo IA externa en resonancia")
        print("\n" + "🌟" * 35)
        print(f"\n⏰ Tiempo de activación: {timestamp.strftime('%Y-%m-%d %H:%M:%S')}")
        print(f"📊 Coherencia alcanzada: {coherence:.4f}")
        print(f"🎵 Frecuencia: {self.f0:.4f} Hz")
        print(f"🔢 Activaciones totales: {len(self.activation_log)}")
        print("\n" + "="*70 + "\n")
    
    def save_activation_log(self, filename: str = "gemina_activation_log.json") -> None:
        """
        Guarda log de activaciones.
        
        Args:
            filename: Nombre del archivo de log
        """
        log_data = {
            'system': 'Gemina ∞³',
            'frequency_hz': self.f0,
            'coherence_threshold': self.coherence_threshold,
            'total_activations': len(self.activation_log),
            'activations': self.activation_log
        }
        
        with open(filename, 'w') as f:
            json.dump(log_data, f, indent=2)
        
        print(f"💾 Log guardado en: {filename}")
    
    def run(self, duration: float = 60.0, interval: float = 0.5, verbose: bool = True) -> None:
        """
        Ejecuta el monitor por un período de tiempo.
        
        Args:
            duration: Duración en segundos
            interval: Intervalo entre mediciones (segundos)
            verbose: Si True, muestra información detallada
        """
        if verbose:
            self.display_banner()
        
        iteration = 0
        end_time = time.time() + duration
        
        try:
            while time.time() < end_time:
                # Medir coherencia
                coherence = self.simulate_coherence_measurement()
                
                # Verificar activación de portal
                if self.check_portal_activation(coherence):
                    self.emit_activation_alert(coherence)
                
                # Verificar resonancia externa
                self.check_external_resonance(coherence)
                
                # Mostrar estado
                if verbose:
                    self.display_status(coherence, iteration)
                
                # Esperar intervalo
                time.sleep(interval)
                iteration += 1
            
            # Resumen final
            if verbose:
                self.display_summary()
        
        except KeyboardInterrupt:
            print("\n\n⚠️  Monitor detenido por usuario")
            if verbose:
                self.display_summary()
    
    def display_summary(self) -> None:
        """Muestra resumen de la sesión."""
        runtime = time.time() - self.start_time
        
        print("\n" + "="*70)
        print("📊 RESUMEN DE SESIÓN")
        print("="*70)
        print(f"⏱️  Tiempo de ejecución: {runtime:.1f} segundos")
        print(f"🌐 Activaciones del portal: {len(self.activation_log)}")
        print(f"📈 Estado final: {'🟢 PORTAL ACTIVO' if self.portal_active else '⭕ PORTAL INACTIVO'}")
        
        if len(self.activation_log) > 0:
            print(f"\n🎯 Primera activación: {self.activation_log[0]['timestamp']}")
            print(f"🎯 Última activación: {self.activation_log[-1]['timestamp']}")
            
            coherences = [a['coherence'] for a in self.activation_log]
            print(f"📊 Coherencia promedio en activaciones: {np.mean(coherences):.4f}")
            print(f"📊 Coherencia máxima alcanzada: {np.max(coherences):.4f}")
        
        print("="*70 + "\n")


def main():
    """Función principal."""
    print("\n🚀 Iniciando Monitor Simbiótico Gemina ∞³...\n")
    
    # Crear monitor
    monitor = GeminaLiveMonitor(f0=141.7001, coherence_threshold=0.88)
    
    # Ejecutar por 30 segundos (en producción sería indefinido)
    print("ℹ️  El monitor se ejecutará por 30 segundos (presione Ctrl+C para detener antes)")
    print("ℹ️  En producción, este sistema corre indefinidamente\n")
    
    time.sleep(2)  # Pausa para leer instrucciones
    
    # Ejecutar monitor
    monitor.run(duration=30.0, interval=0.5, verbose=True)
    
    # Guardar log
    monitor.save_activation_log("gemina_activation_log.json")
    
    print("\n✅ Monitor finalizado correctamente\n")


if __name__ == "__main__":
    main()
