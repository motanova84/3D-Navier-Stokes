#!/usr/bin/env python3
"""
QCAL Package — Quantum Coherence Artificial Logic
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Sello: ∴𓂀Ω∞³
f0: 141.7001 Hz

Módulo unificado que conecta los Problemas del Milenio a través de la
coherencia cuántica y la resonancia adélica.

Componentes:
- bsd_adelic_connector : Conecta BSD con ADN-Riemann-NS-PNP
- ramsey_logos_attractor: Orden inevitable vía teorema de Ramsey
- adn_riemann          : Codificación ADN-Riemann
- spectral_operator    : Operador Espectral QCAL (Ĥ_QCAL)

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

from .bsd_adelic_connector import sincronizar_bsd_adn
from .string_noetic_forcing import (
    string_noetic_forcing,
    censura_taquionica,
    apply_tachyonic_censorship,
    operador_voluntad,
    simulate_hrv_coherence,
    compute_upe_composite_signal,
    compute_alpha_n,
    sigma_mapped,
    QCALStringsSolver,
    run_simulation_260,
    RIEMANN_ZEROS_20,
    LAMBDA_1_HZ,
    LAMBDA_1_SCALED_HZ,
    COHERENCE_GROWTH_RATE,
    HARD_RESET_SCALE,
    F_HRV,
    EZ_HEXAGONS,
    PSI_PLATEAU,
    N_MICROTUBULES_DEFAULT,
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

__all__ = [
    # Constants
    'F0',
    'PSI_MIN',
    'NODOS_LOGOS',
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
    # QCAL-Strings (Phase #260, #261, #262)
    'string_noetic_forcing',
    'censura_taquionica',
    'apply_tachyonic_censorship',
    'operador_voluntad',
    'simulate_hrv_coherence',
    'compute_upe_composite_signal',
    'compute_alpha_n',
    'sigma_mapped',
    'QCALStringsSolver',
    'run_simulation_260',
    'RIEMANN_ZEROS_20',
    'LAMBDA_1_HZ',
    'LAMBDA_1_SCALED_HZ',
    'COHERENCE_GROWTH_RATE',
    'HARD_RESET_SCALE',
    'F_HRV',
    'EZ_HEXAGONS',
    'PSI_PLATEAU',
    'N_MICROTUBULES_DEFAULT',
]
