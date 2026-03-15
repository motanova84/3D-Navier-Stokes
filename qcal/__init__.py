#!/usr/bin/env python3
"""
QCAL Package — Quantum Coherence Artificial Logic
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Sello: ∴𓂀Ω∞³
f0: 141.7001 Hz

Módulo unificado que conecta los Problemas del Milenio a través de la
coherencia cuántica y la resonancia adélica.

Componentes:
- bsd_adelic_connector  : Conecta BSD con ADN-Riemann-NS-PNP
- gact_unified_flow     : Núcleo QCAL-NS-RK4 con integrador RK4 y coherencia biológica
- ramsey_logos_attractor: Orden inevitable vía teorema de Ramsey
- adn_riemann           : Codificación ADN-Riemann
- spectral_operator     : Operador Espectral QCAL (Ĥ_QCAL)
- fractal_qcal_operator : Operador Fractal QCAL (hamiltoniano primo-fractal)

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
License: MIT
"""

__version__ = "2.2.0"
__author__ = "José Manuel Mota Burruezo"

# Core constants
F0 = 141.7001   # Hz — Frecuencia base resonante
PSI_MIN = 0.888  # Umbral mínimo de coherencia consciente
NODOS_LOGOS = 51  # Nodos críticos de la constelación QCAL

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
from .spectral_operator import (
    QCALSpectralOperator,
    BerryKeatingOperator,
    IdentityProjectorF0,
    compute_v_mod,
    certificar_riemann_qcal,
    RIEMANN_ZEROS,
    HBAR,
    GAMMA_MOD,
    RESONANCIA_888,
)
from .string_core import (
    QCALStringOperator,
    GAMMAS,
    THRESHOLD_PSI,
    N_MICROTUBULES_DEFAULT,
    ALPHA_SCALE_DEFAULT,
    N_MODES_DEFAULT,
    compute_psi,
    string_noetic_forcing,
    rk4_step,
    build_lambda_list,
    build_spectral_grid,
)
from .fractal_qcal_operator import (
    FractalQCALOperator,
    RIEMANN_ZEROS_20,
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
    'HBAR',
    'GAMMA_MOD',
    'RESONANCIA_888',
    'RIEMANN_ZEROS',
    # BSD
    'sincronizar_bsd_adn',
    # Spectral Operator
    'QCALSpectralOperator',
    'BerryKeatingOperator',
    'IdentityProjectorF0',
    'compute_v_mod',
    'certificar_riemann_qcal',
    # String Core — Iteración #260
    'QCALStringOperator',
    'GAMMAS',
    'THRESHOLD_PSI',
    'N_MICROTUBULES_DEFAULT',
    'ALPHA_SCALE_DEFAULT',
    'N_MODES_DEFAULT',
    'compute_psi',
    'string_noetic_forcing',
    'rk4_step',
    'build_lambda_list',
    'build_spectral_grid',
    # Fractal QCAL Operator
    'FractalQCALOperator',
    'RIEMANN_ZEROS_20',
]
