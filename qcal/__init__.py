#!/usr/bin/env python3
"""
QCAL Package - Quantum Coherence Artificial Logic
═══════════════════════════════════════════════════

Módulo unificado que conecta los Problemas del Milenio a través de la
coherencia cuántica y la resonancia adélica.

Componentes:
- bsd_adelic_connector: Conecta BSD con ADN-Riemann-NS-PNP

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
License: MIT
Sello: ∴𓂀Ω∞³
"""

__version__ = "2.0.0"
__author__ = "José Manuel Mota Burruezo"

from .bsd_adelic_connector import sincronizar_bsd_adn, F0

__all__ = [
    'sincronizar_bsd_adn',
    'F0',
]
