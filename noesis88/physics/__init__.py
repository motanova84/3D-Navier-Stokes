#!/usr/bin/env python3
"""
noesis88.physics — Sub-paquete de física del motor TOPC
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Sello: ∴𓂀Ω∞³
f0: 141,700.1 Hz

Author: José Manuel Mota Burruezo
License: MIT
"""

from .navier_stokes_qcal import (
    TensionCuerdaHolografica,
    HamiltonianC7,
    GapOpticoManyBody,
    NavierStokesQCAL,
    calcular_tension_vortice,
    ejecutar_motor_primordial,
)

__all__ = [
    "TensionCuerdaHolografica",
    "HamiltonianC7",
    "GapOpticoManyBody",
    "NavierStokesQCAL",
    "calcular_tension_vortice",
    "ejecutar_motor_primordial",
]
