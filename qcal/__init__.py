#!/usr/bin/env python3
"""
QCAL Package - Quantum Coherence Artificial Logic
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Sello: ∴𓂀Ω∞³
f0: 141.7001 Hz

Módulo unificado que conecta los Problemas del Milenio a través de la
coherencia cuántica y la resonancia adélica.

Componentes:
- bsd_adelic_connector: Conecta BSD con ADN-Riemann-NS-PNP
- gact_unified_flow: Núcleo QCAL-NS-RK4 con integrador RK4 y coherencia biológica

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
License: MIT
"""

__version__ = "2.1.0"
__author__ = "José Manuel Mota Burruezo"

# Core constants
F0 = 141.7001       # Hz - Fundamental resonant frequency
PSI_MIN = 0.888     # Minimum coherence threshold
NODOS_LOGOS = 51    # Critical constellation nodes

try:
    from .bsd_adelic_connector import sincronizar_bsd_adn
    _BSD_AVAILABLE = True
except (SyntaxError, ImportError):
    _BSD_AVAILABLE = False
    sincronizar_bsd_adn = None  # type: ignore[assignment]

from .gact_unified_flow import (
    rk4_step,
    compute_biological_coherence,
    apply_vibrational_filter,
    plot_energy_spectrum,
    GACTUnifiedFlow,
)

__all__ = [
    # Constants
    'F0',
    'PSI_MIN',
    'NODOS_LOGOS',
    # BSD-Adelic (may be unavailable if module has syntax errors)
    'sincronizar_bsd_adn',
    # GACT-NS-RK4
    'rk4_step',
    'compute_biological_coherence',
    'apply_vibrational_filter',
    'plot_energy_spectrum',
    'GACTUnifiedFlow',
]
