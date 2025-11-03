"""
AI Agent for Navier-Stokes Mathematical Document Analysis and Script Generation

This module provides an AI agent that can:
- Parse and extract equations from PDF documents
- Memorize and organize mathematical content
- Visualize equations and mathematical relationships
- Generate scripts based on the mathematical framework
"""

from .equation_parser import EquationParser
from .math_memory import MathematicalMemory
from .script_generator import ScriptGenerator
from .visualizer import EquationVisualizer
from .agent import NavierStokesAIAgent

__version__ = "1.0.0"
__all__ = [
    "EquationParser",
    "MathematicalMemory",
    "ScriptGenerator",
    "EquationVisualizer",
    "NavierStokesAIAgent",
]
