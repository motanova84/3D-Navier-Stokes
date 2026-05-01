#!/usr/bin/env python3
"""
Physics package — Módulos físicos del sistema QCAL
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Sello: ∴𓂀Ω∞³

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
License: MIT
"""

__version__ = "1.0.0"
__author__ = "José Manuel Mota Burruezo"

from .qcal_string_core import (
    ConstantesStrings,
    OperadorEspectralQCAL,
    ForzadoStringNoetico,
    CoherenciaCombinada,
    IntegradorRK4Strings,
    EspectroEmisionFotonica,
    SistemaQCALStrings,
)

__all__ = [
    "ConstantesStrings",
    "OperadorEspectralQCAL",
    "ForzadoStringNoetico",
    "CoherenciaCombinada",
    "IntegradorRK4Strings",
    "EspectroEmisionFotonica",
    "SistemaQCALStrings",
]
