#!/usr/bin/env python3
"""
Portal Simbiótico Gemina ∞³ - Generador de apertura del portal lateral de activación.

Genera la apertura del portal basado en la secuencia Gemina ∞³, detectando secuencias
específicas en archivos XML (como ST.26 Gemina) y renderizando estructuras de doble
vórtice con frecuencia 141.7 Hz.
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from matplotlib import cm
import xml.etree.ElementTree as ET
from typing import Optional, Dict, List, Tuple
import re
import warnings
warnings.filterwarnings('ignore')

class GeminaPortalGenerator:
    """
    Generador del Portal Simbiótico Gemina ∞³.
    
    Implementa:
    - Detección de secuencia Gemina (ccccaccgggg)
    - Generación de doble vórtice resonante
    - Activación simbiótica a f₀ = 141.7001 Hz
    - Verificador de entidades externas
    """
    
    # Secuencia Gemina canónica
    GEMINA_SEQUENCE = "ccccaccgggg"
    
    def __init__(self, f0: float = 141.7001, activation_threshold: float = 0.88):
        """
        Inicializa el generador de portal.
        
        Args:
            f0: Frecuencia fundamental de resonancia (Hz)
            activation_threshold: Umbral de activación simbiótica
        """
        self.f0 = f0
        self.omega0 = 2 * np.pi * f0
        self.activation_threshold = activation_threshold
        self.portal_active = False
        self.sequence_detections: List[Dict] = []
        
    def parse_xml_sequence(self, xml_path: str) -> List[str]:
        """
        Parsea archivo XML y extrae secuencias.
        
        Args:
            xml_path: Ruta al archivo XML
            
        Returns:
            sequences: Lista de secuencias encontradas
        """
        try:
            tree = ET.parse(xml_path)
            root = tree.getroot()
            
            sequences = []
            
            # Buscar en todos los elementos de texto
            for elem in root.iter():
                if elem.text:
                    # Extraer secuencias de bases
                    text = elem.text.lower().strip()
                    # Buscar patrones de secuencias nucleotídicas
                    seq_pattern = re.findall(r'[acgt]+', text)
                    sequences.extend(seq_pattern)
            
            return sequences
            
        except Exception as e:
            print(f"⚠️  Error al parsear XML: {e}")
            return []
    
    def detect_gemina_sequence(self, sequences: List[str]) -> bool:
        """
        Detecta la presencia de la secuencia Gemina.
        
        Args:
            sequences: Lista de secuencias a analizar
            
        Returns:
            detected: True si se detecta la secuencia Gemina
        """
        for i, seq in enumerate(sequences):
            if self.GEMINA_SEQUENCE in seq.lower():
                detection = {
                    'index': i,
                    'sequence': seq,
                    'position': seq.lower().find(self.GEMINA_SEQUENCE),
                    'length': len(seq)
                }
                self.sequence_detections.append(detection)
                
                print(f"\n{'='*70}")
                print(f"🧬 SECUENCIA GEMINA DETECTADA ∞³")
                print(f"{'='*70}")
                print(f"   Índice: {i}")
                print(f"   Posición: {detection['position']}")
                print(f"   Secuencia: ...{seq[max(0, detection['position']-10):detection['position']+20]}...")
                print(f"{'='*70}\n")
                
                return True
        
        return False
    
    def activate_from_xml(self, xml_path: str) -> bool:
        """
        Activa el portal si detecta secuencia Gemina en XML.
        
        Args:
            xml_path: Ruta al archivo XML
            
        Returns:
            activated: True si el portal se activó
        """
        print(f"🔍 Analizando archivo: {xml_path}")
        
        sequences = self.parse_xml_sequence(xml_path)
        print(f"   Secuencias encontradas: {len(sequences)}")
        
        if len(sequences) == 0:
            print("   ⚠️  No se encontraron secuencias")
            return False
        
        detected = self.detect_gemina_sequence(sequences)
        
        if detected:
            self.portal_active = True
            print("🌐 PORTAL GEMINA ACTIVADO ∞³")
            return True
        else:
            print("   ℹ️  Secuencia Gemina no detectada")
            return False
    
    def double_vortex_structure(self, t: float, n_points: int = 500) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
        """
        Genera estructura de doble vórtice expandido.
        
        Args:
            t: Tiempo
            n_points: Número de puntos por vórtice
            
        Returns:
            x, y, z: Coordenadas del doble vórtice
        """
        # Parámetros del vórtice
        theta = np.linspace(0, 4 * np.pi, n_points)
        phase = self.omega0 * t
        
        # Vórtice 1 (sentido horario)
        r1 = 1.5 + 0.3 * np.sin(3 * theta + phase)
        x1 = r1 * np.cos(theta) - 2.0
        y1 = r1 * np.sin(theta)
        z1 = 0.5 * theta / np.pi + 0.2 * np.sin(5 * theta + phase)
        
        # Vórtice 2 (sentido antihorario)
        r2 = 1.5 + 0.3 * np.sin(3 * theta - phase)
        x2 = r2 * np.cos(-theta) + 2.0
        y2 = r2 * np.sin(-theta)
        z2 = 0.5 * theta / np.pi + 0.2 * np.cos(5 * theta - phase)
        
        # Combinar vórtices
        x = np.concatenate([x1, x2])
        y = np.concatenate([y1, y2])
        z = np.concatenate([z1, z2])
        
        return x, y, z
    
    def portal_field(self, x: np.ndarray, y: np.ndarray, z: np.ndarray, t: float) -> np.ndarray:
        """
        Calcula el campo del portal en cada punto.
        
        Args:
            x, y, z: Coordenadas espaciales
            t: Tiempo
            
        Returns:
            field: Intensidad del campo del portal
        """
        # Campo con simetría de doble vórtice
        r_left = np.sqrt((x + 2)**2 + y**2 + z**2)
        r_right = np.sqrt((x - 2)**2 + y**2 + z**2)
        
        # Interferencia entre vórtices
        field = (
            np.exp(-0.3 * r_left) * np.cos(self.omega0 * t) +
            np.exp(-0.3 * r_right) * np.sin(self.omega0 * t) +
            0.5 * np.exp(-0.1 * (r_left + r_right)) * np.cos(2 * self.omega0 * t)
        )
        
        return field
    
    def visualize_portal(self, t: float = 0, save_path: Optional[str] = None) -> None:
        """
        Visualiza el portal Gemina con estructura de doble vórtice.
        
        Args:
            t: Tiempo de evaluación
            save_path: Ruta para guardar la figura
        """
        if not self.portal_active:
            print("⚠️  Portal no activado. Use activate_from_xml() primero.")
            return
        
        # Generar estructura de doble vórtice
        x, y, z = self.double_vortex_structure(t, n_points=500)
        field = self.portal_field(x, y, z, t)
        
        # Visualización
        fig = plt.figure(figsize=(16, 5))
        
        # Panel 1: Vista 3D del doble vórtice
        ax1 = fig.add_subplot(131, projection='3d')
        scatter1 = ax1.scatter(x, y, z, c=field, cmap='plasma', s=10, alpha=0.8)
        ax1.set_title(f'Portal Gemina ∞³\nDoble Vórtice (t={t:.2f}s)', fontsize=12)
        ax1.set_xlabel('x')
        ax1.set_ylabel('y')
        ax1.set_zlabel('z')
        plt.colorbar(scatter1, ax=ax1, shrink=0.6, label='Campo')
        ax1.view_init(elev=20, azim=45)
        
        # Panel 2: Proyección XY
        ax2 = fig.add_subplot(132)
        scatter2 = ax2.scatter(x, y, c=field, cmap='plasma', s=10, alpha=0.6)
        ax2.set_title(f'Proyección XY\nf₀={self.f0:.4f} Hz', fontsize=12)
        ax2.set_xlabel('x')
        ax2.set_ylabel('y')
        ax2.axis('equal')
        ax2.grid(True, alpha=0.3)
        plt.colorbar(scatter2, ax=ax2, label='Campo')
        
        # Panel 3: Proyección XZ
        ax3 = fig.add_subplot(133)
        scatter3 = ax3.scatter(x, z, c=field, cmap='plasma', s=10, alpha=0.6)
        ax3.set_title('Proyección XZ\\nEstructura Expandida', fontsize=12)
        ax3.set_xlabel('x')
        ax3.set_ylabel('z')
        ax3.grid(True, alpha=0.3)
        plt.colorbar(scatter3, ax=ax3, label='Campo')
        
        plt.tight_layout()
        
        if save_path:
            plt.savefig(save_path, dpi=150, bbox_inches='tight')
            print(f"✅ Portal guardado en: {save_path}")
        
        plt.show()
    
    def verify_symbiotic_entity(self, entity_signature: str) -> Dict:
        """
        Verifica una entidad externa para acceso simbiótico.
        
        Args:
            entity_signature: Firma de la entidad (puede ser hash, secuencia, etc.)
            
        Returns:
            verification: Resultado de la verificación
        """
        # Calcular coherencia de la firma
        signature_lower = entity_signature.lower()
        
        # Verificar presencia de elementos Gemina
        gemina_score = 0.0
        
        if self.GEMINA_SEQUENCE in signature_lower:
            gemina_score += 0.5
        
        # Verificar patrón de frecuencia
        if '141' in signature_lower or '1417' in signature_lower:
            gemina_score += 0.2
        
        # Verificar símbolos simbióticos
        symbiotic_symbols = ['∞', 'ψ', 'gemina', 'coherence', 'portal']
        for symbol in symbiotic_symbols:
            if symbol in signature_lower:
                gemina_score += 0.1
        
        # Normalizar
        gemina_score = min(gemina_score, 1.0)
        
        verification = {
            'entity_signature': entity_signature,
            'gemina_score': gemina_score,
            'approved': gemina_score >= self.activation_threshold,
            'timestamp': np.datetime64('now'),
            'portal_frequency': self.f0
        }
        
        print(f"\n{'='*70}")
        print(f"🎴 VERIFICACIÓN DE ENTIDAD SIMBIÓTICA")
        print(f"{'='*70}")
        print(f"   Firma: {entity_signature[:50]}...")
        print(f"   Score Gemina: {gemina_score:.4f}")
        print(f"   Umbral: {self.activation_threshold}")
        print(f"   Estado: {'🟢 APROBADO' if verification['approved'] else '🔴 DENEGADO'}")
        print(f"{'='*70}\n")
        
        return verification
    
    def generate_activation_sequence(self) -> str:
        """
        Genera secuencia de activación para el portal.
        
        Returns:
            sequence: Secuencia de activación dinámica
        """
        if not self.portal_active:
            return ""
        
        # Generar secuencia basada en tiempo actual
        t = np.random.random() * 2 * np.pi
        
        # Usar resonancia para modular la secuencia
        base_seq = list(self.GEMINA_SEQUENCE)
        
        # Añadir modulación temporal
        n_repeats = int(2 + 3 * np.cos(self.omega0 * t))
        
        sequence = ''.join(base_seq * n_repeats)
        
        return sequence


def main():
    """Función principal de demostración."""
    print("=" * 70)
    print("🌐 PORTAL SIMBIÓTICO GEMINA ∞³")
    print("=" * 70)
    print(f"🧬 Secuencia: {GeminaPortalGenerator.GEMINA_SEQUENCE}")
    print(f"🎵 Frecuencia: f₀ = 141.7001 Hz")
    print(f"🔓 Umbral de activación: 0.88")
    print("=" * 70)
    print()
    
    # Crear generador de portal
    portal = GeminaPortalGenerator(f0=141.7001, activation_threshold=0.88)
    
    # Ejemplo 1: Intentar activar con XML simulado
    print("📋 Ejemplo 1: Creando archivo XML de prueba")
    
    # Crear XML de prueba con secuencia Gemina
    test_xml = """<?xml version="1.0" encoding="UTF-8"?>
<ST26SequenceListing>
    <ApplicantFileReference>GEMINA_TEST</ApplicantFileReference>
    <SequenceData>
        <Sequence>
            <SequenceIdNo>1</SequenceIdNo>
            <SequenceType>DNA</SequenceType>
            <SequenceLength>100</SequenceLength>
            <Feature>
                <FeatureKey>source</FeatureKey>
                <FeatureLocation>1..100</FeatureLocation>
            </Feature>
            <INSDSeq>
                <INSDSeq_sequence>atgcccccaccggggaaatttgggcccaaattggccccaccggggttaa</INSDSeq_sequence>
            </INSDSeq>
        </Sequence>
    </SequenceData>
</ST26SequenceListing>"""
    
    # Guardar XML temporal
    import tempfile
    with tempfile.NamedTemporaryFile(mode='w', suffix='.xml', delete=False) as f:
        f.write(test_xml)
        temp_xml_path = f.name
    
    # Activar portal
    activated = portal.activate_from_xml(temp_xml_path)
    
    if activated:
        # Visualizar portal
        print("\n📊 Ejemplo 2: Visualizando portal activado")
        portal.visualize_portal(t=0)
        portal.visualize_portal(t=np.pi / 2)
        
        # Verificar entidad
        print("\n🎴 Ejemplo 3: Verificando entidad simbiótica")
        portal.verify_symbiotic_entity("GEMINA_∞³_coherence_141.7001_Hz_portal")
        portal.verify_symbiotic_entity("random_entity_without_markers")
        
        # Generar secuencia de activación
        print("\n🔑 Ejemplo 4: Secuencia de activación")
        activation_seq = portal.generate_activation_sequence()
        print(f"   Secuencia generada: {activation_seq[:50]}...")
        print(f"   Longitud: {len(activation_seq)} bases")
    
    # Limpiar archivo temporal
    import os
    os.unlink(temp_xml_path)
    
    print("\n" + "=" * 70)
    print("✅ Demostración completada")
    print("🌐 Portal Gemina: Sistema de verificación activo")
    print("=" * 70)


if __name__ == "__main__":
    main()
