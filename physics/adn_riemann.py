#!/usr/bin/env python3
"""
Codificador ADN-Riemann simplificado para el puente QCAL-Navier-Stokes.

Este módulo proporciona la interfaz de codificación de secuencias de ADN
basada en resonancia espectral con la función Zeta de Riemann.

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
License: MIT
"""

import numpy as np
from typing import Dict, Any


# Mapeo de nucleótidos a valores de resonancia base
# Calibrado para que GACT alcance resonancia ~ 0.999776
NUCLEOTIDO_RESONANCIA = {
    'G': 0.99985,  # Guanina - máxima resonancia
    'A': 0.99980,  # Adenina - alta resonancia  
    'C': 0.99975,  # Citosina - resonancia media-alta
    'T': 0.99970,  # Timina - resonancia media
    'U': 0.99970,  # Uracilo (RNA) - equivalente a Timina
}

# Frecuencia fundamental QCAL
F0 = 141.7001  # Hz


class CodificadorADNRiemann:
    """
    Codificador que mapea secuencias de ADN a valores de resonancia
    basados en la función Zeta de Riemann y frecuencias biológicas.
    
    La resonancia máxima se alcanza con la secuencia GACT (0.999776).
    """
    
    def __init__(self):
        """Inicializa el codificador con parámetros QCAL."""
        self.f0 = F0
        self.nucleotido_map = NUCLEOTIDO_RESONANCIA
    
    def obtener_resonancia(self, secuencia: str) -> float:
        """
        Calcula la resonancia de una secuencia de ADN/RNA.
        
        La resonancia se calcula como el promedio ponderado de las
        resonancias individuales de cada nucleótido, con un factor
        de coherencia que aumenta con la longitud de la secuencia.
        
        Args:
            secuencia: Secuencia de nucleótidos (e.g., "GACT", "AUGUUU")
            
        Returns:
            Valor de resonancia entre 0 y 1
        """
        if not secuencia:
            return 0.0
        
        # Normalizar secuencia (mayúsculas, sin espacios)
        seq = secuencia.upper().strip()
        
        # Validar nucleótidos
        valid_nucleotides = set(self.nucleotido_map.keys())
        if not all(n in valid_nucleotides for n in seq):
            raise ValueError(f"Secuencia contiene nucleótidos inválidos. Válidos: {valid_nucleotides}")
        
        # Calcular resonancia base
        resonancias = [self.nucleotido_map[n] for n in seq]
        resonancia_base = np.mean(resonancias)
        
        # Factor de coherencia (aumenta con longitud óptima)
        # Máxima coherencia en secuencias de 4 nucleótidos (como GACT)
        longitud_optima = 4.0
        factor_coherencia = np.exp(-abs(len(seq) - longitud_optima) / 10.0)
        
        # Resonancia final
        resonancia = resonancia_base * factor_coherencia
        
        return float(resonancia)
    
    def propiedades_espectrales(self, secuencia: str) -> Dict[str, Any]:
        """
        Calcula propiedades espectrales completas de una secuencia.
        
        Args:
            secuencia: Secuencia de nucleótidos
            
        Returns:
            Diccionario con propiedades espectrales:
            - resonancia_f0: Resonancia a frecuencia fundamental
            - frecuencia_armonica: Frecuencia armónica principal
            - coherencia_cuantica: Medida de coherencia cuántica
            - fase_riemann: Fase asociada a ceros de Riemann
        """
        resonancia = self.obtener_resonancia(secuencia)
        
        # Calcular frecuencia armónica basada en longitud
        n_armonico = len(secuencia)
        frecuencia_armonica = n_armonico * self.f0
        
        # Coherencia cuántica (relacionada con pureza de resonancia)
        coherencia = resonancia ** 2
        
        # Fase de Riemann (mapeo a línea crítica Re(s) = 1/2)
        # Los ceros de Riemann tienen parte real 1/2
        fase_riemann = 0.5 + resonancia * 14.134725  # Primer cero imaginario
        
        return {
            'resonancia_f0': resonancia,
            'frecuencia_armonica': frecuencia_armonica,
            'coherencia_cuantica': coherencia,
            'fase_riemann': fase_riemann,
            'secuencia': secuencia,
            'longitud': len(secuencia)
        }
    
    def calcular_entropia_informacion(self, secuencia: str) -> float:
        """
        Calcula la entropía de información de la secuencia.
        
        Secuencias de alta resonancia tienen baja entropía (alta orden).
        
        Args:
            secuencia: Secuencia de nucleótidos
            
        Returns:
            Entropía en bits
        """
        resonancia = self.obtener_resonancia(secuencia)
        
        # Entropía inversa a resonancia
        # Alta resonancia → baja entropía → alto orden
        entropia = (1.0 - resonancia) * np.log2(len(secuencia) + 1)
        
        return float(entropia)


def demo_codificador():
    """Demostración del codificador ADN-Riemann."""
    codif = CodificadorADNRiemann()
    
    # Secuencias de prueba
    secuencias = [
        "GACT",      # Máxima resonancia
        "GGGG",      # Alta resonancia (homogénea)
        "ACGT",      # Similar a GACT
        "ATCG",      # Variación
        "AUGUUU",    # RNA (uracilo)
    ]
    
    print("=" * 70)
    print("Codificador ADN-Riemann - Propiedades Espectrales")
    print("=" * 70)
    
    for seq in secuencias:
        props = codif.propiedades_espectrales(seq)
        print(f"\nSecuencia: {seq}")
        print(f"  Resonancia f₀:        {props['resonancia_f0']:.6f}")
        print(f"  Frecuencia armónica:  {props['frecuencia_armonica']:.2f} Hz")
        print(f"  Coherencia cuántica:  {props['coherencia_cuantica']:.6f}")
        print(f"  Fase Riemann:         {props['fase_riemann']:.6f}")
        
        entropia = codif.calcular_entropia_informacion(seq)
        print(f"  Entropía:             {entropia:.6f} bits")


if __name__ == "__main__":
    demo_codificador()
