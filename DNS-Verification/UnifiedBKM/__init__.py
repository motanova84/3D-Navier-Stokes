"""
Unified BKM-CZ-Besov Framework

This package implements the unified framework for 3D Navier-Stokes
global regularity via three convergent routes:
- Route A: Riccati-Besov direct closure
- Route B: Volterra-Besov integral equations  
- Route C: Energy bootstrap with H^m estimates
"""

from .riccati_besov_closure import (
    BesovConstants,
    compute_delta_star,
    riccati_besov_damping,
    riccati_besov_closure,
    optimize_amplitude,
    check_parameter_requirements,
    analyze_gap
)

from .volterra_besov import (
    volterra_kernel,
    volterra_inequality,
    besov_volterra_integral,
    verify_volterra_contraction,
    lemma_7_1_improved
)

from .energy_bootstrap import (
    energy_bootstrap_ode,
    energy_bootstrap,
    analyze_bootstrap_stability,
    bootstrap_parameter_sweep
)

from .unified_validation import (
    simulate_dns_dual_scaling,
    estimate_constants_from_data,
    calculate_damping_from_data,
    unified_validation,
    quick_test
)

__all__ = [
    # Route A - Riccati-Besov
    'BesovConstants',
    'compute_delta_star',
    'riccati_besov_damping',
    'riccati_besov_closure',
    'optimize_amplitude',
    'check_parameter_requirements',
    'analyze_gap',
    # Route B - Volterra-Besov
    'volterra_kernel',
    'volterra_inequality',
    'besov_volterra_integral',
    'verify_volterra_contraction',
    'lemma_7_1_improved',
    # Route C - Energy Bootstrap
    'energy_bootstrap_ode',
    'energy_bootstrap',
    'analyze_bootstrap_stability',
    'bootstrap_parameter_sweep',
    # Unified Validation
    'simulate_dns_dual_scaling',
    'estimate_constants_from_data',
    'calculate_damping_from_data',
    'unified_validation',
    'quick_test'
]
