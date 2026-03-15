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
- riemann_sparse        : Recuperación espectral de Riemann sparse (Fases #261–#264)

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

try:
    from .gact_unified_flow import (
        rk4_step,
        compute_biological_coherence,
        apply_vibrational_filter,
        plot_energy_spectrum,
        GACTUnifiedFlow,
    )
    _GACT_AVAILABLE = True
except (SyntaxError, ImportError):
    _GACT_AVAILABLE = False
    rk4_step = None  # type: ignore[assignment]
    compute_biological_coherence = None  # type: ignore[assignment]
    apply_vibrational_filter = None  # type: ignore[assignment]
    plot_energy_spectrum = None  # type: ignore[assignment]
    GACTUnifiedFlow = None  # type: ignore[assignment]

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
    build_lambda_list,
    build_spectral_grid,
)
if _GACT_AVAILABLE:
    from .string_core import rk4_step  # noqa: F811 — prefer string_core alias

from .riemann_sparse import (
    RiemannSparseRecovery,
    build_bk_sparse,
    build_vmod_sparse,
    sigma_sweep,
    certificar_fase264,
    SIGMA_C,
    N_PRIMES_DEFAULT,
    N_GRID_DEFAULT,
)

__all__ = [
    # Constants
    'F0',
    'PSI_MIN',
    'NODOS_LOGOS',
    # BSD-Adelic
    'sincronizar_bsd_adn',
    # GACT-NS-RK4
    'rk4_step',
    'compute_biological_coherence',
    'apply_vibrational_filter',
    'plot_energy_spectrum',
    'GACTUnifiedFlow',
    # Spectral operator constants
    'HBAR',
    'GAMMA_MOD',
    'RESONANCIA_888',
    'RIEMANN_ZEROS',
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
    'build_lambda_list',
    'build_spectral_grid',
    # Riemann Sparse Recovery — Fases #261–#264
    'RiemannSparseRecovery',
    'build_bk_sparse',
    'build_vmod_sparse',
    'sigma_sweep',
    'certificar_fase264',
    'SIGMA_C',
    'N_PRIMES_DEFAULT',
    'N_GRID_DEFAULT',
]
