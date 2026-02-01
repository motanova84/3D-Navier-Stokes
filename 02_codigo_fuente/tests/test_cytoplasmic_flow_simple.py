#!/usr/bin/env python3
"""
Simple Tests for Cytoplasmic Flow Model
=======================================

Basic tests to verify core functionality

Author: José Manuel Mota Burruezo
Date: 31 de enero de 2026
"""

import sys
import os
import unittest

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'teoria_principal'))

from cytoplasmic_flow_model import CytoplasmicFlowModel, CytoplasmaParams


class TestBasicFunctionality(unittest.TestCase):
    """Basic functionality tests"""
    
    def test_model_creation(self):
        """Test that model can be created"""
        model = CytoplasmicFlowModel()
        self.assertIsNotNone(model)
    
    def test_viscous_regime(self):
        """Test that default parameters give viscous regime"""
        model = CytoplasmicFlowModel()
        self.assertTrue(model.is_viscous_regime())
    
    def test_smooth_solution(self):
        """Test that viscous regime has smooth solution"""
        model = CytoplasmicFlowModel()
        self.assertTrue(model.has_smooth_solution())
    
    def test_hilbert_polya_exists(self):
        """Test that Hilbert-Pólya operator exists"""
        model = CytoplasmicFlowModel()
        self.assertTrue(model.hilbert_polya_operator_exists())
    
    def test_fundamental_frequency(self):
        """Test fundamental frequency"""
        model = CytoplasmicFlowModel()
        f0 = model.get_fundamental_frequency()
        self.assertAlmostEqual(f0, 141.7001, places=3)
    
    def test_riemann_connection(self):
        """Test Riemann hypothesis connection"""
        model = CytoplasmicFlowModel()
        self.assertTrue(model.riemann_hypothesis_proven_in_biology())


if __name__ == "__main__":
    unittest.main()
