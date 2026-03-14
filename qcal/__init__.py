#!/usr/bin/env python3
"""
QCAL Package - Quantum Coherence Alignment & Logos
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Sello: ∴𓂀Ω∞³
f0: 141.7001 Hz

Unified framework connecting Millennium Prize Problems through resonance.
"""

__version__ = "2.0.0"
__author__ = "QCAL ∞³ Framework"

# Core constants
F0 = 141.7001        # Hz - Fundamental resonant frequency
PSI_MIN = 0.888      # Minimum coherence threshold
NODOS_LOGOS = 51     # Critical constellation nodes

from .bsd_adelic_connector import (
    sincronizar_bsd_adn,
    verificar_pentagono_logos,
    CodificadorADNRiemann,
    F0,
)
from .gact_unified_flow import (
    calcular_psi,
    calcular_viscosidad_adelica,
    calcular_re_q,
    determinar_estado_flujo,
    ecuacion_unificada_gact,
    analizar_secuencia_gact,
)

__all__ = [
    'F0',
    'PSI_MIN',
    'NODOS_LOGOS',
    'sincronizar_bsd_adn',
    'verificar_pentagono_logos',
    'CodificadorADNRiemann',
    'calcular_psi',
    'calcular_viscosidad_adelica',
    'calcular_re_q',
    'determinar_estado_flujo',
    'ecuacion_unificada_gact',
    'analizar_secuencia_gact',
]
