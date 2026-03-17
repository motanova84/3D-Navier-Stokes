#!/usr/bin/env python3
"""
qcal_string_core — QCAL-Strings: Forzado Noético sobre Navier-Stokes Holográfico
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Sello: ∴𓂀Ω∞³
f0: 141.7001 Hz

Módulo raíz de conveniencia — re-exporta todos los símbolos públicos de
``qcal.string_core`` para compatibilidad con scripts de alto nivel.

Iteración #260 — Estado: QED-CUERDAS-VERIFIED ✅

Uso rápido::

    from qcal_string_core import QCALStringOperator, build_lambda_list, rk4_step
    op = QCALStringOperator()
    lambdas = build_lambda_list(op)

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
License: MIT
"""

# Re-export everything from the package module
from qcal.string_core import (
    GAMMAS,
    THRESHOLD_PSI,
    N_MICROTUBULES_DEFAULT,
    ALPHA_SCALE_DEFAULT,
    N_MODES_DEFAULT,
    QCALStringOperator,
    compute_psi,
    string_noetic_forcing,
    rk4_step,
    build_lambda_list,
    build_spectral_grid,
)
from qcal.spectral_operator import (
    F0,
    PSI_MIN,
    HBAR,
    GAMMA_MOD,
    RIEMANN_ZEROS,
)

__all__ = [
    # String Core
    "GAMMAS",
    "THRESHOLD_PSI",
    "N_MICROTUBULES_DEFAULT",
    "ALPHA_SCALE_DEFAULT",
    "N_MODES_DEFAULT",
    "QCALStringOperator",
    "compute_psi",
    "string_noetic_forcing",
    "rk4_step",
    "build_lambda_list",
    "build_spectral_grid",
    # Spectral constants
    "F0",
    "PSI_MIN",
    "HBAR",
    "GAMMA_MOD",
    "RIEMANN_ZEROS",
]

if __name__ == "__main__":
    from qcal.string_core import _demo
    _demo()
