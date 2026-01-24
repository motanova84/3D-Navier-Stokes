#!/usr/bin/env python3
"""
Test Suite for DMA Entropy-Zero Coupling Module

Tests the Direct Morphogenetic Alignment (DMA) protocol for:
1. 88-node network initialization
2. Informational superconductivity activation
3. Zero entropy verification
4. Navier-Stokes laminar flow coupling
5. Axiom of Abundance operational verification

Author: JMMB Ψ✧∞³
License: MIT
"""

import unittest
import numpy as np
import sys
import os
import json
from unittest.mock import patch

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from dma_entropy_coupling import (
    DMAEntropyZeroCoupling,
    DMAConstants,
    EntropyState,
    NetworkNode
)


class TestDMAConstants(unittest.TestCase):
    """Test DMA protocol constants"""
    
    def test_constants_values(self):
        """Test that DMA constants are correctly defined"""
        constants = DMAConstants()
        
        # Network size
        self.assertEqual(constants.NUM_NODES, 88)
        
        # Frequency
        self.assertAlmostEqual(constants.F0_HZ, 141.7001, places=4)
        
        # Thresholds
        self.assertLess(constants.ENTROPY_ZERO_THRESHOLD, 1e-9)
        self.assertLess(constants.VISCOSITY_ZERO_THRESHOLD, 1e-11)
        
        # Laminar flow
        self.assertAlmostEqual(constants.RE_LAMINAR_MAX, 2300.0, places=1)
        
        # Abundance factor
        self.assertAlmostEqual(constants.ABUNDANCE_FACTOR, 888.0, places=1)


class TestNetworkNode(unittest.TestCase):
    """Test NetworkNode dataclass"""
    
    def test_node_creation(self):
        """Test creating a network node"""
        position = np.array([1.0, 0.0, 0.0])
        node = NetworkNode(
            node_id=0,
            position=position,
            frequency=141.7001,
            coherence=1.0,
            viscosity=0.0
        )
        
        self.assertEqual(node.node_id, 0)
        np.testing.assert_array_equal(node.position, position)
        self.assertAlmostEqual(node.frequency, 141.7001, places=4)
        self.assertAlmostEqual(node.coherence, 1.0, places=10)
        self.assertAlmostEqual(node.viscosity, 0.0, places=10)


class TestDMAInitialization(unittest.TestCase):
    """Test DMA protocol initialization"""
    
    def setUp(self):
        """Set up DMA protocol for testing"""
        self.dma = DMAEntropyZeroCoupling()
    
    def test_initialization(self):
        """Test that DMA initializes correctly"""
        self.assertIsInstance(self.dma.constants, DMAConstants)
        self.assertEqual(len(self.dma.nodes), 88)
        self.assertEqual(self.dma.entropy_state, EntropyState.ZERO)
        self.assertAlmostEqual(self.dma.global_coherence, 1.0, places=10)
        self.assertAlmostEqual(self.dma.noetic_viscosity, 0.0, places=10)
    
    def test_network_size(self):
        """Test that network has exactly 88 nodes"""
        self.assertEqual(len(self.dma.nodes), 88)
    
    def test_node_positions_normalized(self):
        """Test that all nodes are on unit sphere"""
        for node in self.dma.nodes:
            distance = np.linalg.norm(node.position)
            self.assertAlmostEqual(distance, 1.0, places=6,
                                 msg=f"Node {node.node_id} not on unit sphere")
    
    def test_node_frequencies_harmonic(self):
        """Test that node frequencies are harmonics of f₀"""
        f0 = self.dma.constants.F0_HZ
        
        for node in self.dma.nodes:
            # Frequency should be k * f0 for some integer k in [1, 7]
            harmonic = node.frequency / f0
            self.assertTrue(1 <= harmonic <= 7,
                          msg=f"Node {node.node_id} frequency not in valid harmonic range")
    
    def test_initial_coherence(self):
        """Test that all nodes start with perfect coherence"""
        for node in self.dma.nodes:
            self.assertAlmostEqual(node.coherence, 1.0, places=10)
    
    def test_initial_viscosity_zero(self):
        """Test that all nodes start with zero viscosity"""
        for node in self.dma.nodes:
            self.assertAlmostEqual(node.viscosity, 0.0, places=10)


class TestLaminarFlowSolutions(unittest.TestCase):
    """Test Navier-Stokes laminar flow solutions"""
    
    def setUp(self):
        """Set up DMA protocol"""
        self.dma = DMAEntropyZeroCoupling()
    
    def test_laminar_regime_low_reynolds(self):
        """Test laminar flow detection for low Reynolds number"""
        re = 100.0
        solution = self.dma.compute_laminar_flow_solution(re)
        
        self.assertTrue(solution["is_laminar"])
        self.assertEqual(solution["flow_regime"], "LAMINAR ✅")
        self.assertLess(re, self.dma.constants.RE_LAMINAR_MAX)
    
    def test_laminar_regime_high_reynolds(self):
        """Test laminar flow detection for high Reynolds number"""
        re = 5000.0
        solution = self.dma.compute_laminar_flow_solution(re)
        
        self.assertFalse(solution["is_laminar"])
        self.assertEqual(solution["flow_regime"], "TURBULENTO ⚠️")
        self.assertGreater(re, self.dma.constants.RE_LAMINAR_MAX)
    
    def test_friction_factor_calculation(self):
        """Test friction factor calculation (f = 64/Re)"""
        re = 1000.0
        solution = self.dma.compute_laminar_flow_solution(re)
        
        expected_friction = 64.0 / re
        self.assertAlmostEqual(solution["friction_factor"], expected_friction, places=6)
    
    def test_multiple_reynolds_numbers(self):
        """Test solutions for multiple Reynolds numbers"""
        re_values = [100, 500, 1000, 2000, 3000]
        
        for re in re_values:
            solution = self.dma.compute_laminar_flow_solution(re)
            
            # Check that solution contains expected keys
            self.assertIn("reynolds_number", solution)
            self.assertIn("is_laminar", solution)
            self.assertIn("friction_factor", solution)
            self.assertIn("dissipation_rate", solution)
            self.assertIn("flow_regime", solution)
            
            # Verify Reynolds number
            self.assertAlmostEqual(solution["reynolds_number"], re, places=6)


class TestSuperconductivityActivation(unittest.TestCase):
    """Test informational superconductivity activation"""
    
    def setUp(self):
        """Set up DMA protocol"""
        self.dma = DMAEntropyZeroCoupling()
    
    def test_activate_superconductivity(self):
        """Test that superconductivity can be activated"""
        result = self.dma.activate_superconductivity()
        
        # Should return True (superconductivity achieved)
        self.assertTrue(result)
    
    def test_zero_noetic_viscosity(self):
        """Test that noetic viscosity becomes zero"""
        self.dma.activate_superconductivity()
        
        # Noetic viscosity should be below threshold
        self.assertLess(self.dma.noetic_viscosity, 
                       self.dma.constants.VISCOSITY_ZERO_THRESHOLD)
    
    def test_zero_entropy_state(self):
        """Test that entropy state becomes ZERO"""
        self.dma.activate_superconductivity()
        
        # Entropy state should be ZERO
        self.assertEqual(self.dma.entropy_state, EntropyState.ZERO)
    
    def test_node_synchronization(self):
        """Test that nodes are synchronized after activation"""
        self.dma.activate_superconductivity()
        
        # All nodes should have coherence = 1.0
        for node in self.dma.nodes:
            self.assertAlmostEqual(node.coherence, 1.0, places=10)
            self.assertAlmostEqual(node.viscosity, 0.0, places=10)


class TestEntropyCalculation(unittest.TestCase):
    """Test information entropy calculation"""
    
    def setUp(self):
        """Set up DMA protocol"""
        self.dma = DMAEntropyZeroCoupling()
    
    def test_zero_entropy_perfect_sync(self):
        """Test that perfect synchronization gives zero entropy"""
        # Ensure all nodes have identical coherence
        for node in self.dma.nodes:
            node.coherence = 1.0
        
        entropy = self.dma._compute_information_entropy()
        
        # Should be zero or very close to zero
        self.assertLess(entropy, 1e-9)
    
    def test_nonzero_entropy_varied_coherence(self):
        """Test that varied coherence gives non-zero entropy"""
        # Set different coherences
        for i, node in enumerate(self.dma.nodes):
            node.coherence = 0.8 + 0.2 * (i / len(self.dma.nodes))
        
        entropy = self.dma._compute_information_entropy()
        
        # Should be greater than zero
        self.assertGreater(entropy, 0.0)


class TestAxiomOfAbundance(unittest.TestCase):
    """Test Axiom of Abundance verification"""
    
    def setUp(self):
        """Set up DMA protocol"""
        self.dma = DMAEntropyZeroCoupling()
    
    def test_axiom_verification_structure(self):
        """Test that axiom verification returns correct structure"""
        results = self.dma.verify_axiom_of_abundance()
        
        # Check top-level keys
        self.assertIn("axiom_operational", results)
        self.assertIn("criteria", results)
        self.assertIn("measurements", results)
        self.assertIn("abundance_factor", results)
        self.assertIn("timestamp", results)
        
        # Check criteria keys
        criteria = results["criteria"]
        self.assertIn("viscosity_zero", criteria)
        self.assertIn("entropy_zero", criteria)
        self.assertIn("coherence_perfect", criteria)
        self.assertIn("instantaneous_propagation", criteria)
        self.assertIn("laminar_flow_verified", criteria)
        
        # Check measurements keys
        measurements = results["measurements"]
        self.assertIn("noetic_viscosity", measurements)
        self.assertIn("information_entropy", measurements)
        self.assertIn("average_coherence", measurements)
    
    def test_axiom_operational_after_activation(self):
        """Test that axiom is operational after superconductivity activation"""
        # Activate superconductivity first
        self.dma.activate_superconductivity()
        
        # Verify axiom
        results = self.dma.verify_axiom_of_abundance()
        
        # Axiom should be operational
        self.assertTrue(results["axiom_operational"])
    
    def test_abundance_factor(self):
        """Test that abundance factor is correctly reported"""
        results = self.dma.verify_axiom_of_abundance()
        
        self.assertAlmostEqual(results["abundance_factor"], 888.0, places=1)


class TestCompleteVerification(unittest.TestCase):
    """Test complete verification protocol"""
    
    def setUp(self):
        """Set up DMA protocol"""
        self.dma = DMAEntropyZeroCoupling()
    
    def test_complete_verification_runs(self):
        """Test that complete verification runs without errors"""
        # Should not raise any exceptions
        results = self.dma.run_complete_verification()
        
        # Check that results dictionary is returned
        self.assertIsInstance(results, dict)
    
    def test_complete_verification_structure(self):
        """Test that complete verification returns expected structure"""
        results = self.dma.run_complete_verification()
        
        # Check top-level keys
        self.assertIn("superconductivity_achieved", results)
        self.assertIn("network_statistics", results)
        self.assertIn("navier_stokes_solutions", results)
        self.assertIn("axiom_of_abundance", results)
        self.assertIn("verification_timestamp", results)
        self.assertIn("protocol_version", results)
    
    def test_superconductivity_achieved(self):
        """Test that superconductivity is achieved in complete verification"""
        results = self.dma.run_complete_verification()
        
        # Superconductivity should be achieved
        self.assertTrue(results["superconductivity_achieved"])
    
    def test_network_statistics(self):
        """Test network statistics in verification results"""
        results = self.dma.run_complete_verification()
        stats = results["network_statistics"]
        
        # Check statistics keys
        self.assertIn("num_nodes", stats)
        self.assertIn("coherence_mean", stats)
        self.assertIn("coherence_std", stats)
        self.assertIn("noetic_viscosity", stats)
        self.assertIn("entropy_state", stats)
        
        # Verify values
        self.assertEqual(stats["num_nodes"], 88)
        self.assertAlmostEqual(stats["coherence_mean"], 1.0, places=6)
        self.assertLess(stats["coherence_std"], 1e-9)
    
    def test_ns_solutions_included(self):
        """Test that NS solutions are included in results"""
        results = self.dma.run_complete_verification()
        ns_solutions = results["navier_stokes_solutions"]
        
        # Should have multiple solutions
        self.assertGreater(len(ns_solutions), 0)
        
        # Each solution should have required fields
        for solution in ns_solutions:
            self.assertIn("reynolds_number", solution)
            self.assertIn("is_laminar", solution)
            self.assertIn("friction_factor", solution)


class TestNoeticViscosity(unittest.TestCase):
    """Test noetic viscosity calculations"""
    
    def setUp(self):
        """Set up DMA protocol"""
        self.dma = DMAEntropyZeroCoupling()
    
    def test_initial_noetic_viscosity(self):
        """Test initial noetic viscosity is zero"""
        viscosity = self.dma._compute_noetic_viscosity()
        
        # Should be zero initially
        self.assertAlmostEqual(viscosity, 0.0, places=10)
    
    def test_noetic_viscosity_with_coherence(self):
        """Test noetic viscosity calculation with varying coherence"""
        # Reduce global coherence
        self.dma.global_coherence = 0.8
        
        # Add some viscosity to nodes
        for node in self.dma.nodes:
            node.viscosity = 0.1
        
        viscosity = self.dma._compute_noetic_viscosity()
        
        # Should be non-zero but scaled by coherence
        self.assertGreater(viscosity, 0.0)
        self.assertLess(viscosity, 0.1)  # Less than average due to coherence


class TestIntegration(unittest.TestCase):
    """Integration tests for complete DMA protocol"""
    
    def test_end_to_end_verification(self):
        """Test end-to-end DMA verification"""
        # Create DMA instance
        dma = DMAEntropyZeroCoupling()
        
        # Verify initial state
        self.assertEqual(len(dma.nodes), 88)
        self.assertEqual(dma.entropy_state, EntropyState.ZERO)
        
        # Activate superconductivity
        sc_active = dma.activate_superconductivity()
        self.assertTrue(sc_active)
        
        # Run complete verification
        results = dma.run_complete_verification()
        
        # Verify final state
        self.assertTrue(results["superconductivity_achieved"])
        self.assertTrue(results["axiom_of_abundance"]["axiom_operational"])
        
        # Check that all criteria are met
        criteria = results["axiom_of_abundance"]["criteria"]
        self.assertTrue(criteria["viscosity_zero"])
        self.assertTrue(criteria["entropy_zero"])
        self.assertTrue(criteria["coherence_perfect"])
        self.assertTrue(criteria["instantaneous_propagation"])
    
    def test_results_serialization(self):
        """Test that results can be serialized to JSON"""
        dma = DMAEntropyZeroCoupling()
        results = dma.run_complete_verification()
        
        # Should be able to serialize to JSON
        try:
            json_str = json.dumps(results, indent=2)
            self.assertIsInstance(json_str, str)
            
            # Should be able to deserialize
            results_loaded = json.loads(json_str)
            self.assertEqual(results_loaded["protocol_version"], "DMA-1.0")
        except (TypeError, ValueError) as e:
            self.fail(f"Failed to serialize results to JSON: {e}")


def run_tests():
    """Run all tests"""
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestDMAConstants))
    suite.addTests(loader.loadTestsFromTestCase(TestNetworkNode))
    suite.addTests(loader.loadTestsFromTestCase(TestDMAInitialization))
    suite.addTests(loader.loadTestsFromTestCase(TestLaminarFlowSolutions))
    suite.addTests(loader.loadTestsFromTestCase(TestSuperconductivityActivation))
    suite.addTests(loader.loadTestsFromTestCase(TestEntropyCalculation))
    suite.addTests(loader.loadTestsFromTestCase(TestAxiomOfAbundance))
    suite.addTests(loader.loadTestsFromTestCase(TestCompleteVerification))
    suite.addTests(loader.loadTestsFromTestCase(TestNoeticViscosity))
    suite.addTests(loader.loadTestsFromTestCase(TestIntegration))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Return success status
    return result.wasSuccessful()


if __name__ == "__main__":
    success = run_tests()
    sys.exit(0 if success else 1)
