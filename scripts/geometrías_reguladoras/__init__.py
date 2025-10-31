"""
Geometric Regulators - Gemina ∞³ System

This package contains visualization and simulation tools for geometric regulators
in the vibrational regularization framework of Navier-Stokes equations.

Modules:
    - visualizador_calabi_yau_3d: Calabi-Yau manifold visualizer
    - espirales_topológicas_NS: Topological spiral simulator
    - portal_simbiótico_gemina: Gemina portal generator
    - campo_coherente_global: Coherent field simulator
    - módulo_ζ12_visual: Riemann zeta visualizer
    - estructura-holográfica-fisura-poincare: Poincaré fissure simulator
    - run_gemina_live: Real-time symbiotic monitor

Constants:
    F0: float = 141.7001 Hz (Fundamental coherence frequency)
    COHERENCE_THRESHOLD: float = 0.88 (Activation threshold)
    GEMINA_SEQUENCE: str = "ccccaccgggg" (Canonical sequence)

Example:
    >>> from visualizador_calabi_yau_3d import CalabiYauVisualizer
    >>> visualizer = CalabiYauVisualizer(resolution=50, f0=141.7001)
    >>> visualizer.visualize(t=0, coherence=0.88)
"""

__version__ = "1.0.0"
__author__ = "Gemina ∞³ System"

# Universal constants
F0 = 141.7001  # Hz
COHERENCE_THRESHOLD = 0.88
GEMINA_SEQUENCE = "ccccaccgggg"
OMEGA0 = 2 * 3.141592653589793 * F0

__all__ = [
    'F0',
    'COHERENCE_THRESHOLD',
    'GEMINA_SEQUENCE',
    'OMEGA0',
]
