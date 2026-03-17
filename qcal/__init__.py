#!/usr/bin/env python3
"""
QCAL Package - Quantum Coherence Alignment & Logos
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Sello: ∴𓂀Ω∞³
f0: 141.7001 Hz
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
- sparse_riemann        : Hamiltoniano Sparse GUE para recuperación del espectro Riemann (Fase #264)
- ramsey_logos_attractor: Orden inevitable vía teorema de Ramsey
- adn_riemann           : Codificación ADN-Riemann
- spectral_operator     : Operador Espectral QCAL (Ĥ_QCAL)
- riemann_sparse        : Recuperación espectral de Riemann sparse (Fases #261–#264)
- bsd_adelic_connector    : Conecta BSD con ADN-Riemann-NS-PNP
- gact_unified_flow       : Núcleo QCAL-NS-RK4 con integrador RK4 y coherencia biológica
- ramsey_logos_attractor  : Orden inevitable vía teorema de Ramsey
- adn_riemann             : Codificación ADN-Riemann
- spectral_operator       : Operador Espectral QCAL (Ĥ_QCAL)
- riemann_sparse_recovery : Recuperación espectral de Riemann (Fases #261–#264)
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
from .bsd_adelic_connector import sincronizar_bsd_adn
from .riemann_sparse_recovery import (
    RiemannSparseRecovery,
    sieve_primes,
    build_bk_sparse,
    build_v_mod_sparse,
    build_v_corrections,
    sigma_sweep,
    find_critical_sigma,
    SIGMA_CRITICAL,
    N_PRIMES_DEFAULT,
    N_GRID_DEFAULT,
    RIEMANN_ZEROS_50,
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
from .convergence_proof import (
    TachyonCensor,
    RegularizedQCALHamiltonian,
    compute_ns_hamiltonian,
    epsilon_boundary_sweep,
    prove_convergence_limit,
    SIGMA_CRITICAL,
    EPSILON_DEFAULT,
    EPSILON_DIRAC_THRESHOLD,
    NU_GACT,
    H1_FINITE_BOUND,
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
from .sparse_riemann import (
    FractalQCAL_GUE,
    build_sparse_hamiltonian,
    compute_riemann_spectral_error,
    RIEMANN_ZEROS_20,
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
    'sincronizar_bsd_adn',
    'verificar_pentagono_logos',
    'CodificadorADNRiemann',
    'calcular_psi',
    'calcular_viscosidad_adelica',
    'calcular_re_q',
    'determinar_estado_flujo',
    'ecuacion_unificada_gact',
    'analizar_secuencia_gact',
    # BSD-Adelic
    'sincronizar_bsd_adn',
    # Riemann Sparse Recovery — Fases #261–#264
    'RiemannSparseRecovery',
    'sieve_primes',
    'build_bk_sparse',
    'build_v_mod_sparse',
    'build_v_corrections',
    'sigma_sweep',
    'find_critical_sigma',
    'SIGMA_CRITICAL',
    'N_PRIMES_DEFAULT',
    'N_GRID_DEFAULT',
    'RIEMANN_ZEROS_50',
    'HBAR',
    'GAMMA_MOD',
    'RESONANCIA_888',
    'RIEMANN_ZEROS',
    # Convergence proof constants
    'SIGMA_CRITICAL',
    'EPSILON_DEFAULT',
    'EPSILON_DIRAC_THRESHOLD',
    'NU_GACT',
    'H1_FINITE_BOUND',
    # BSD
    'sincronizar_bsd_adn',
    # Spectral Operator
    # GACT-NS-RK4
    'rk4_step',
    'compute_biological_coherence',
    'apply_vibrational_filter',
    'plot_energy_spectrum',
    'GACTUnifiedFlow',
    # Spectral operator constants
    # Spectral Operator
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
    # Convergence Proof
    'TachyonCensor',
    'RegularizedQCALHamiltonian',
    'compute_ns_hamiltonian',
    'epsilon_boundary_sweep',
    'prove_convergence_limit',
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
    # Sparse Riemann — Fase #264
    'FractalQCAL_GUE',
    'build_sparse_hamiltonian',
    'compute_riemann_spectral_error',
    'RIEMANN_ZEROS_20',
    # Riemann Sparse Recovery — Fases #261–#264
    'RiemannSparseRecovery',
    'build_bk_sparse',
    'build_vmod_sparse',
    'sigma_sweep',
    'certificar_fase264',
    'SIGMA_C',
    'N_PRIMES_DEFAULT',
    'N_GRID_DEFAULT',
    # KSS Holographic Fluid
    'KSSHolographicFluid',
    'KSSResult',
    'compute_kss_bound',
    'compute_viscosity_from_rotor_decay',
    'compute_entropy_density_from_upe',
    'KSS_BOUND',
    'F_UPE_HZ',
]
