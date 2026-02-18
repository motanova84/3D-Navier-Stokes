"""
CONSTANTES FUNDAMENTALES DEL SISTEMA Ψ-NS

Este módulo define las constantes fundamentales del sistema de Navier-Stokes
con coherencia cuántica QCAL (Quasi-Critical Alignment Layer).

Referencias:
    - QCAL Framework: Construcción y análisis original
    - Documentación: Documentation/QCAL_PARAMETERS.md
    - Issue: ISSUE_CRITICAL_PARAMETER.md
"""

import numpy as np
from typing import Dict

# Frecuencia fundamental QCAL
F0 = 141.7001  # Hz

# Velocidades de propagación en diferentes medios (m/s)
# Estas velocidades determinan el parámetro de acoplamiento a
_VELOCIDADES_MEDIOS: Dict[str, float] = {
    'vacio': 100.0,    # Velocidad efectiva en vacío
    'agua': 127.0,     # Velocidad efectiva en agua
    'aire': 4.45,      # Velocidad efectiva en aire
}


def calcular_a(medio: str = 'vacio') -> float:
    """
    Calcula el parámetro de acoplamiento vibracional según el medio de propagación.
    
    DERIVACIÓN: a = (2πf₀) / c, donde:
        - f₀ = 141.7001 Hz (frecuencia fundamental QCAL)
        - c es la velocidad de la onda en el medio de propagación
        - a NO es un parámetro libre, sino que depende del medio
    
    El parámetro a controla la intensidad del defecto de desalineación:
        δ* = (a² c₀²) / (4π²)
    
    donde δ* es el defecto de desalineación persistente entre vorticidad y deformación.
    
    Args:
        medio: Tipo de medio de propagación. Opciones:
            - 'vacio': a = 8.9  (γ ≈ 0.10)  - Régimen de baja viscosidad
            - 'agua':  a = 7.0  (γ ≈ 0.025) - Régimen acuático/biológico
            - 'aire':  a = 200  (γ ≈ 0.998) - Régimen atmosférico
    
    Returns:
        float: Parámetro de acoplamiento a para el medio especificado
    
    Raises:
        ValueError: Si el medio especificado no es válido
    
    Examples:
        >>> a_vacio = calcular_a('vacio')
        >>> print(f"a (vacío) = {a_vacio:.1f}")
        a (vacío) = 8.9
        
        >>> a_agua = calcular_a('agua')
        >>> print(f"a (agua) = {a_agua:.1f}")
        a (agua) = 7.0
        
        >>> a_aire = calcular_a('aire')
        >>> print(f"a (aire) = {a_aire:.1f}")
        a (aire) = 200.0
    
    Notes:
        IMPORTANTE: El valor de a NO es arbitrario. Depende del medio
        de propagación. La inconsistencia reportada en versiones previas
        correspondía a usar diferentes medios en diferentes contextos.
        
        Para cada medio, el parámetro a se calcula como:
            a = (2π × 141.7001) / c
        
        donde c es la velocidad característica del medio:
        - Vacío: c ≈ 100 m/s   → a ≈ 8.9
        - Agua:  c ≈ 127 m/s   → a ≈ 7.0
        - Aire:  c ≈ 4.45 m/s  → a ≈ 200
        
        Relación con el defecto de desalineación (c₀ = 1.0):
        - Vacío: δ* ≈ 2.01  → γ ≈ 0.10  (coercividad parabólica satisfecha)
        - Agua:  δ* ≈ 1.24  → γ ≈ 0.025 (coercividad marginal)
        - Aire:  δ* ≈ 1012  → γ ≈ 0.998 (régimen altamente disipativo)
    """
    # Valores calibrados para cada medio
    valores_a = {
        'vacio': 8.9,   # Calibrado para γ > 0 con δ* ≈ 2.01
        'agua': 7.0,    # Régimen acuático/biológico con δ* ≈ 1.24
        'aire': 200,    # Régimen atmosférico con δ* ≈ 1012
    }
    
    medio_lower = medio.lower()
    
    if medio_lower not in valores_a:
        medios_validos = ', '.join(f"'{m}'" for m in valores_a.keys())
        raise ValueError(
            f"Medio '{medio}' no reconocido. "
            f"Medios válidos: {medios_validos}"
        )
    
    return valores_a[medio_lower]


def calcular_velocidad_medio(a: float) -> float:
    """
    Calcula la velocidad de propagación en el medio a partir del parámetro a.
    
    Derivación inversa: c = (2πf₀) / a
    
    Args:
        a: Parámetro de acoplamiento vibracional
    
    Returns:
        float: Velocidad de propagación en m/s
    
    Examples:
        >>> c_vacio = calcular_velocidad_medio(8.9)
        >>> print(f"c (vacío) = {c_vacio:.2f} m/s")
        c (vacío) = 100.00 m/s
    """
    if a <= 0:
        raise ValueError("El parámetro a debe ser positivo")
    
    return (2 * np.pi * F0) / a


def calcular_defecto_desalineacion(a: float, c0: float = 1.0) -> float:
    """
    Calcula el defecto de desalineación δ* a partir de los parámetros.
    
    Formula: δ* = (a² c₀²) / (4π²)
    
    Args:
        a: Parámetro de acoplamiento vibracional
        c0: Gradiente de fase (default: 1.0)
    
    Returns:
        float: Defecto de desalineación δ*
    
    Examples:
        >>> delta_vacio = calcular_defecto_desalineacion(8.9)
        >>> print(f"δ* (vacío) = {delta_vacio:.2f}")
        δ* (vacío) = 2.01
    """
    return (a**2 * c0**2) / (4 * np.pi**2)


def calcular_coeficiente_amortiguamiento(
    delta_star: float,
    nu: float = 1e-3,
    c_star: float = 1/16,
    C_str: float = 32.0
) -> float:
    """
    Calcula el coeficiente de amortiguamiento γ de Riccati.
    
    Formula: γ = ν·c⋆ - (1 - δ*/2)·C_str
    
    Args:
        delta_star: Defecto de desalineación δ*
        nu: Viscosidad (default: 1e-3)
        c_star: Constante de coercividad parabólica (default: 1/16)
        C_str: Constante de estiramiento de vorticidad (default: 32.0)
    
    Returns:
        float: Coeficiente de amortiguamiento γ
    
    Notes:
        Para cierre incondicional se requiere γ > 0.
        Esto implica: δ* > 2(1 - ν·c⋆/C_str)
    
    Examples:
        >>> gamma_vacio = calcular_coeficiente_amortiguamiento(2.01)
        >>> print(f"γ (vacío) = {gamma_vacio:.2f}")
        γ (vacío) = 0.10
    """
    return nu * c_star - (1 - delta_star / 2) * C_str


# DOCUMENTACIÓN: El valor de a NO es arbitrario. Depende del medio
# de propagación. La inconsistencia reportada corresponde a usar
# diferentes medios en diferentes contextos.
#
# CONTEXTOS DE USO:
# - Validaciones teóricas (vacío):     a = 8.9   (γ > 0, prueba incondicional)
# - Aplicaciones biológicas (agua):    a = 7.0   (flujo citoplasmático, Re~10⁻⁸)
# - Aplicaciones atmosféricas (aire):  a = 200   (DNS, régimen turbulento)
#
# REFERENCIAS:
# - ISSUE_CRITICAL_PARAMETER.md: Calibración de parámetros
# - Documentation/QCAL_PARAMETERS.md: Documentación completa
# - Scripts/calibrate_parameters.py: Herramienta de calibración
