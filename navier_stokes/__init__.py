"""
Navier-Stokes Unified Framework
===============================

This package provides unified constants and utilities for the Ψ-Navier-Stokes
quantum-coherent framework, including medium-specific parameter calibrations
and fundamental QCAL constants.

Main Components:
---------------
- constants: Unified constants module with medium-specific parameters
- F0: Fundamental QCAL coherence frequency (141.7001 Hz)
- calcular_a: Function to get calibrated amplitude parameter for different media
- verificar_regularidad: Verify global regularity conditions

Quick Start:
-----------
    >>> from navier_stokes.constants import calcular_a, F0
    >>> 
    >>> # Get parameter a for water
    >>> a = calcular_a('agua')
    >>> print(f"Water: a = {a}")
    Water: a = 7.0
    >>> 
    >>> # Get QCAL frequency
    >>> print(f"F0 = {F0} Hz")
    F0 = 141.7001 Hz

For detailed documentation, see navier_stokes/README.md
"""

from .constants import (
    # Main API
    calcular_a,
    obtener_delta_star,
    verificar_regularidad,
    get_all_media_parameters,
    get_qcal_constants,
    
    # Constants
    F0,
    OMEGA0,
    A_VACIO,
    A_AGUA,
    A_AIRE,
    C0_DEFAULT,
    
    # QFT coupling coefficients
    ALPHA_QFT,
    BETA_QFT,
    GAMMA_QFT,
    
    # Parabolic coercivity constants
    C_STAR,
    C_STR,
    
    # Riccati-Besov constants
    C_B,
    C_CZ,
    C_STAR_BESOV,
)

__version__ = '1.0.0'
__author__ = 'QCAL Framework'

__all__ = [
    # Main API functions
    'calcular_a',
    'obtener_delta_star',
    'verificar_regularidad',
    'get_all_media_parameters',
    'get_qcal_constants',
    
    # Fundamental constants
    'F0',
    'OMEGA0',
    
    # Medium-specific parameters
    'A_VACIO',
    'A_AGUA',
    'A_AIRE',
    'C0_DEFAULT',
    
    # QFT coefficients
    'ALPHA_QFT',
    'BETA_QFT',
    'GAMMA_QFT',
    
    # Parabolic constants
    'C_STAR',
    'C_STR',
    
    # Riccati-Besov constants
    'C_B',
    'C_CZ',
    'C_STAR_BESOV',
]
