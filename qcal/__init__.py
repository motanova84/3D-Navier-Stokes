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
- gact_unified_flow    : Núcleo QCAL-NS-RK4 con integrador RK4 y coherencia biológica
- ramsey_logos_attractor: Orden inevitable vía teorema de Ramsey
- adn_riemann          : Codificación ADN-Riemann
- spectral_operator    : Operador Espectral QCAL (Ĥ_QCAL)
- kss_holographic_fluid: Límite KSS y Fluido Holográfico Perfecto del citoplasma

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
    build_lambda_list,
    build_spectral_grid,
)
from .kss_holographic_fluid import (
    KSSHolographicFluid,
    KSSResult,
    compute_kss_bound,
    compute_viscosity_from_rotor_decay,
    compute_entropy_density_from_upe,
    KSS_BOUND,
    F_UPE_HZ,
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
    # Spectral Operator
    'HBAR',
    'GAMMA_MOD',
    'RESONANCIA_888',
    'RIEMANN_ZEROS',
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
    # KSS Holographic Fluid
    'KSSHolographicFluid',
    'KSSResult',
    'compute_kss_bound',
    'compute_viscosity_from_rotor_decay',
    'compute_entropy_density_from_upe',
    'KSS_BOUND',
    'F_UPE_HZ',
]
