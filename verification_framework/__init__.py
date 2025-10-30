"""
3D Navier-Stokes Global Regularity Verification Framework

This package provides computational verification of global regularity
for 3D Navier-Stokes equations via critical closure in Lₜ∞Lₓ³.
"""

__version__ = "1.0.0"
__author__ = "3D-Navier-Stokes Research Team"

from .final_proof import FinalProof
from .constants_verification import verify_critical_constants

__all__ = ['FinalProof', 'verify_critical_constants']
