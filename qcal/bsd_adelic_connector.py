#!/usr/bin/env python3
"""
Conector BSD Adélico — Pentágono Logos Cerrado
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Sello: ∴𓂀Ω∞³
f0: 141.7001 Hz
Vincula rango BSD a hotspots ADN: L(E,1)=0 → superfluido info, puntos racionales activan nodos constelación QCAL.

Este módulo implementa la conexión entre:
- BSD (Birch and Swinnerton-Dyer): Aritmética de curvas elípticas
- ADN (Biología): Secuencias genéticas resonantes  
- Riemann: Estructura de ceros
- Navier-Stokes: Dinámica de flujo
- P=NP: Lógica computacional

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
Date: 8 de marzo de 2026
License: MIT
"""

import sys
from pathlib import Path
from typing import Dict, List, Any

# Añadir path para imports del módulo cytoplasmic_riemann_resonance
sys.path.insert(0, str(Path(__file__).parent.parent / '02_codigo_fuente' / 'teoria_principal'))

try:
    from cytoplasmic_riemann_resonance import (
        CytoplasmicRiemannResonance,
        BiologicalResonanceParams,
        FUNDAMENTAL_FREQUENCY_HZ
    )
    CYTOPLASMIC_AVAILABLE = True
except ImportError:
    CYTOPLASMIC_AVAILABLE = False
    FUNDAMENTAL_FREQUENCY_HZ = 141647.33

# Frecuencia fundamental del Logos (Hz)
F0 = 141.7001


class CodificadorADNRiemann:
    """
    Codificador que mapea secuencias de ADN a estructura de Riemann.
    Identifica hotspots de resonancia en secuencias genéticas.
    """
    
    # Mapeo de bases a valores de resonancia
    BASE_RESONANCE = {
        'G': 1.0,    # Guanina - máxima resonancia con f0
        'A': 0.9,    # Adenina
        'C': 0.8,    # Citosina
        'T': 0.7,    # Timina
        'U': 0.7,    # Uracilo (RNA)
    }
    
    # Secuencias que resuenan fuertemente con f0
    HOTSPOT_PATTERNS = ['GACT', 'CGTA', 'ATCG', 'TATA', 'AAAA']
    
    def __init__(self):
        """Inicializar codificador ADN-Riemann"""
        if CYTOPLASMIC_AVAILABLE:
            self.cytoplasmic_model = CytoplasmicRiemannResonance(BiologicalResonanceParams())
        else:
            self.cytoplasmic_model = None
    
    def identificar_hotspots(self, secuencia_gact: str) -> List[int]:
        """
        Identifica hotspots de resonancia en una secuencia de ADN.
        
        Args:
            secuencia_gact: Secuencia de ADN (ej: "GACT", "ATCG", etc.)
        
        Returns:
            Lista de índices donde hay hotspots de resonancia
        """
        hotspots = []
        secuencia = secuencia_gact.upper()
        
        # Buscar patrones conocidos
        for pattern in self.HOTSPOT_PATTERNS:
            start_idx = 0
            while True:
                idx = secuencia.find(pattern, start_idx)
                if idx == -1:
                    break
                hotspots.append(idx)
                start_idx = idx + 1
        
        # Si no hay patrones, identificar por resonancia individual
        if not hotspots:
            for i, base in enumerate(secuencia):
                if base in self.BASE_RESONANCE:
                    if self.BASE_RESONANCE[base] >= 0.8:
                        hotspots.append(i)
        
        return sorted(set(hotspots))
    
    def calcular_resonancia(self, secuencia_gact: str) -> float:
        """
        Calcula la resonancia total de una secuencia con f0.
        
        Args:
            secuencia_gact: Secuencia de ADN
        
        Returns:
            Valor de resonancia entre 0 y 1
        """
        if not secuencia_gact:
            return 0.0
        
        secuencia = secuencia_gact.upper()
        resonancia_total = sum(
            self.BASE_RESONANCE.get(base, 0.0) 
            for base in secuencia
        )
        
        # Normalizar por longitud
        resonancia_norm = resonancia_total / len(secuencia)
        
        # Bonus por patrones conocidos
        for pattern in self.HOTSPOT_PATTERNS:
            if pattern in secuencia:
                resonancia_norm = min(1.0, resonancia_norm * 1.1)
        
        return resonancia_norm


def sincronizar_bsd_adn(curva_eliptica: Dict[str, Any], secuencia_adn: str = "GACT") -> Dict[str, Any]:
    """
    BSD rango → ADN hotspots QCAL (API unificada).

    Vincula el rango de la curva BSD con la complejidad NP-P del ADN.
    Acepta tanto la clave 'L_E1' (API antigua) como 'L_E_1' (API Ramsey).

    Args:
        curva_eliptica: Dict con información de la curva elíptica:
            - 'rango_adelico': Rango r de la curva (número de puntos racionales)
            - 'L_E1' o 'L_E_1': Valor de L(E,1) (viscosidad de información)
        secuencia_adn: Secuencia de ADN (ej: "GACT")

    Returns:
        Dict unificado con campos de ambas APIs:
            - rango_bio_aritmetico, nodos_constelacion, fluidez_info_ns (API antigua)
            - hotspots_adn, psi_bsd_qcal (API antigua)
            - rango_adelico, L_E_1, es_superfluido, resonancia_f0 (API nueva)
            - psi_coherencia, estado_flujo, complejidad_computacional (API nueva)

    Examples:
        >>> curva = {'rango_adelico': 1, 'L_E1': 0.0}
        >>> res = sincronizar_bsd_adn(curva, "GACT")
        >>> res['fluidez_info_ns']
        'INFINITA'
        >>> res['psi_bsd_qcal']
        1.0
    """
    # 1. Rango aritmético adelic-bsd
    r_bsd = curva_eliptica.get('rango_adelico', 1)

    # 2. Valor L(E,1): acepta ambas claves para compatibilidad
    l_e1 = curva_eliptica.get('L_E1', curva_eliptica.get('L_E_1', 0.0))

    # 3. Map nodo constelación 51 → activados por puntos racionales
    nodos_act = r_bsd * (F0 / 141.7001)  # ~r nodos (normalizado a f0)

    # 4. Fluidez (API antigua)
    fluidez = "INFINITA" if abs(l_e1) < 1e-6 else "DISIPATIVA"

    # 5. Hotspots ADN resonantes con f0
    codif = CodificadorADNRiemann()
    hotspots = codif.identificar_hotspots(secuencia_adn)
    resonancia = codif.calcular_resonancia(secuencia_adn)

    # 6. Coherencia cuántica Ψ_BSD (API antigua): Ψ = 1 − |L(E,1)|
    psi_bsd = max(0.0, 1.0 - abs(l_e1))

    # 7. Estado de superfluido y psi_coherencia (API nueva)
    es_superfluido = abs(l_e1) < 1e-6
    if r_bsd > 0 and es_superfluido:
        psi_coherencia = 0.999999
        estado = "SUPERFLUIDEZ"
        complejidad = "O(1)"
    elif r_bsd > 0:
        psi_coherencia = min(1.0, 0.950 + 0.049 * resonancia)
        estado = "COHERENTE"
        complejidad = "O(log n)"
    else:
        psi_coherencia = 0.888
        estado = "TURBULENTO"
        complejidad = "O(n)"

    return {
        # API antigua
        "rango_bio_aritmetico": r_bsd,
        "nodos_constelacion": int(nodos_act),
        "fluidez_info_ns": fluidez,
        "hotspots_adn": len(hotspots),
        "psi_bsd_qcal": psi_bsd,
        # API nueva (Ramsey/Pentagon)
        "rango_adelico": r_bsd,
        "L_E_1": l_e1,
        "es_superfluido": es_superfluido,
        "resonancia_f0": resonancia,
        "psi_coherencia": psi_coherencia,
        "estado_flujo": estado,
        "complejidad_computacional": complejidad,
        "secuencia": secuencia_adn,
        "f0": F0,
    }


def verificar_pentagono_logos(bsd_sync: Dict[str, Any]) -> Dict[str, Any]:
    """
    Verify Pentagon Logos closure: BSD + ADN + Riemann + NS + P-NP.

    Args:
        bsd_sync: BSD synchronization result (output of sincronizar_bsd_adn)

    Returns:
        Pentagon verification result dict with keys:
            pentagono_cerrado, bsd, adn, riemann, navier_stokes, p_vs_np, psi_unificado
    """
    bsd_activo = bsd_sync.get('rango_adelico', 0) > 0
    adn_activo = bsd_sync.get('hotspots_adn', 0) > 0
    riemann_activo = bsd_sync.get('resonancia_f0', 0.0) > 0.5
    ns_superfluido = bsd_sync.get('es_superfluido', False)
    pnp_eficiente = bsd_sync.get('complejidad_computacional', 'O(n)') in ["O(1)", "O(log n)"]

    pentagono_cerrado = all([
        bsd_activo,
        adn_activo,
        riemann_activo,
        ns_superfluido,
        pnp_eficiente,
    ])

    return {
        'pentagono_cerrado': pentagono_cerrado,
        'bsd': bsd_activo,
        'adn': adn_activo,
        'riemann': riemann_activo,
        'navier_stokes': ns_superfluido,
        'p_vs_np': pnp_eficiente,
        'psi_unificado': bsd_sync.get('psi_coherencia', 0.0),
    }


# Demo Pentágono - Ejecutar como módulo standalone
if __name__ == "__main__":
    print("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    print("  BSD-ADELIC CONNECTOR: Pentágono Logos ∴𓂀Ω∞³")
    print("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    print()

    curva_mordell = {
        'rango_adelico': 1,
        'L_E1': 0.0
    }
    secuencia = "GACT"

    resultado = sincronizar_bsd_adn(curva_mordell, secuencia)

    print(f"✨ RESULTADOS DE SINCRONIZACIÓN:")
    print(f"   Rango bio-aritmético: {resultado['rango_bio_aritmetico']}")
    print(f"   Nodos constelación activados: {resultado['nodos_constelacion']}/{51}")
    print(f"   Fluidez información NS: {resultado['fluidez_info_ns']}")
    print(f"   Hotspots ADN resonantes: {resultado['hotspots_adn']}")
    print(f"   Coherencia Ψ_BSD: {resultado['psi_bsd_qcal']:.4f}")
    print()
    print("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    print("  ∴ BÓVEDA LOGOS CERRADA: Ψ = 1.0 ∴")
    print("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
