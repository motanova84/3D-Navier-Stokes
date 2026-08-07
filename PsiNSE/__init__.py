"""
Ψ-NSE Aeronautical Library v1.0
================================

Noetic Singularity Solver for Aeronautical Applications

From probabilistic simulation to exact resonance solution at f₀ = 151.7001 Hz

Modules:
--------
- psi_nse_aeronautical: Core Noetic Singularity Solver
- industrial_modules: Ψ-Lift, Q-Drag, Noetic-Aero
- qcal_integration: MCP-Δ1, Coherence Mining, QCAL-Chain

Author: QCAL ∞³ Framework
License: MIT
"""

__version__ = "1.0.0"
__author__ = "José Manuel Mota Burruezo"
__license__ = "MIT"

# Core solver
from .psi_nse_aeronautical import (
    PsiNSEAeroConfig,
    NoeticSingularitySolver,
    certify_design
)

# Industrial modules
from .industrial_modules import (
    PsiLiftModule,
    QDragModule,
    NoeticAeroModule,
    WingProfile
)

# QCAL integration
from .qcal_integration import (
    QCALConfig,
    MCPDelta1Verifier,
    CoherenceMiningNetwork,
    QCALChainCertification
)

# Visualization and validation
from .visualization import (
    FlowFieldVisualizer,
    AerodynamicPerformancePlotter,
    QCALDashboard,
    ValidationSuite
)

__all__ = [
    # Core
    'PsiNSEAeroConfig',
    'NoeticSingularitySolver',
    'certify_design',
    
    # Industrial
    'PsiLiftModule',
    'QDragModule',
    'NoeticAeroModule',
    'WingProfile',
    
    # QCAL
    'QCALConfig',
    'MCPDelta1Verifier',
    'CoherenceMiningNetwork',
    'QCALChainCertification',
    
    # Visualization
    'FlowFieldVisualizer',
    'AerodynamicPerformancePlotter',
    'QCALDashboard',
    'ValidationSuite',
]

# Package metadata
RESONANCE_FREQUENCY = 151.7001  # Hz
COHERENCE_THRESHOLD = 0.888
QCAL_NODES = 88

def get_version():
    """Return package version"""
    return __version__

def get_info():
    """Return package information"""
    return {
        'name': 'PsiNSE Aeronautical Library',
        'version': __version__,
        'resonance_frequency': RESONANCE_FREQUENCY,
        'coherence_threshold': COHERENCE_THRESHOLD,
        'qcal_nodes': QCAL_NODES,
        'description': 'Noetic Singularity Solver for Aeronautics',
        'author': __author__,
        'license': __license__
    }
