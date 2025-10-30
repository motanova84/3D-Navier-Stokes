"""
3D Navier-Stokes Global Regularity Verification Framework (UNCONDITIONAL)

This package provides computational verification of unconditional global regularity
for 3D Navier-Stokes equations via universal constants (Route 1: CZ absoluto + coercividad parabólica).
"""

__version__ = "2.0.0"
__author__ = "3D-Navier-Stokes Research Team"

from .final_proof import FinalProof
from .constants_verification import verify_critical_constants
from .universal_constants import UniversalConstants

__all__ = ['FinalProof', 'verify_critical_constants', 'UniversalConstants']
