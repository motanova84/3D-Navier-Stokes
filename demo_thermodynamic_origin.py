#!/usr/bin/env python3
"""
Demonstration of Thermodynamic Origin Framework
================================================

Showcases the thermodynamic origin framework that anchors Navier-Stokes
stability to the cascade from Planck scale to QCAL frequency.

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
Date: March 27, 2026
"""

import sys
import os

# Direct import to avoid __init__.py issues
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'qcal'))
from thermodynamic_origin import demostrar_termodinamica_origen

if __name__ == "__main__":
    demostrar_termodinamica_origen()
