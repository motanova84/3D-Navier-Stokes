#!/usr/bin/env python3
"""
QCAL Package - Quantum Coherence Alignment & Logos
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Sello: ∴𓂀Ω∞³
f0: 141.7001 Hz

Módulo unificado que conecta los Problemas del Milenio a través de la
coherencia cuántica y la resonancia adélica.

Componentes:
- bsd_adelic_connector: Conecta BSD con ADN-Riemann-NS-PNP
- ramsey_logos_attractor: Orden inevitable vía teorema Ramsey
- adn_riemann: Codificador ADN-Riemann
- spectral_operator: QCALSpectralOperator (Berry-Keating refinado)

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
License: MIT
Sello: ∴𓂀Ω∞³
"""

__version__ = "2.0.0"
__author__ = "José Manuel Mota Burruezo"

# Core constants
F0 = 141.7001  # Hz - Fundamental resonant frequency
PSI_MIN = 0.888  # Minimum coherence threshold
NODOS_LOGOS = 51  # Critical constellation nodes

from .bsd_adelic_connector import sincronizar_bsd_adn
from .spectral_operator import QCALSpectralOperator

__all__ = [
    'F0',
    'PSI_MIN',
    'NODOS_LOGOS',
    'sincronizar_bsd_adn',
    'QCALSpectralOperator',
]
