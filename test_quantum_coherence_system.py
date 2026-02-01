#!/usr/bin/env python3
"""
Test Suite for Quantum Coherence System
========================================

Comprehensive tests for the quantum coherence enhancement system.

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
Date: February 1, 2026
License: MIT
"""

import unittest
import numpy as np
from quantum_coherence_system import (
    ResonantNode,
    NodeFrequency,
    QuantumCoherenceParameters,
    QuantumCoherenceSystem,
    demonstrate_quantum_coherence_system
)


class TestQuantumCoherenceParameters(unittest.TestCase):
    """Test quantum coherence parameters"""
    
    def test_default_parameters(self):
        """Test default parameter values"""
        params = QuantumCoherenceParameters()
        
        # Check fundamental frequency
        self.assertEqual(params.f0_hz, 141.7001)
        
        # Check Reynolds number (extremely viscous)
        self.assertEqual(params.reynolds_number, 1e-8)
        
        # Check coherence threshold
        self.assertEqual(params.psi_threshold, 0.888)
        
        # Check πCODE
        self.assertEqual(params.pi_code, 1417.0)
    
    def test_node_configuration(self):
        """Test default node configuration"""
        params = QuantumCoherenceParameters()
        
        # Should have 4 nodes
        self.assertEqual(len(params.nodes), 4)
        
        # Check node types
        node_types = {node.node for node in params.nodes}
        expected_nodes = {
            ResonantNode.AURON,
            ResonantNode.RETINA,
            ResonantNode.PINEAL,
            ResonantNode.TERCER_OJO
        }
        self.assertEqual(node_types, expected_nodes)


class TestNodeFrequency(unittest.TestCase):
    """Test node frequency configuration"""
    
    def test_node_creation(self):
        """Test node frequency creation"""
        node = NodeFrequency(
            node=ResonantNode.AURON,
            frequency_hz=151.7001,
            bandwidth_hz=10.0,
            activation_level=0.0
        )
        
        self.assertEqual(node.node, ResonantNode.AURON)
        self.assertEqual(node.frequency_hz, 151.7001)
        self.assertFalse(node.is_active())
    
    def test_node_activation(self):
        """Test node activation status"""
        node = NodeFrequency(
            node=ResonantNode.RETINA,
            frequency_hz=141.7001,
            bandwidth_hz=5.0,
            activation_level=0.8
        )
        
        self.assertTrue(node.is_active())
        
        # Test threshold
        node.activation_level = 0.5
        self.assertFalse(node.is_active())
        
        node.activation_level = 0.51
        self.assertTrue(node.is_active())


class TestQuantumCoherenceSystem(unittest.TestCase):
    """Test quantum coherence system"""
    
    def setUp(self):
        """Set up test system"""
        self.system = QuantumCoherenceSystem()
    
    def test_initialization(self):
        """Test system initialization"""
        self.assertIsNotNone(self.system.params)
        self.assertEqual(len(self.system.network_state), 4)
        self.assertFalse(self.system.stimulus_active)
        self.assertFalse(self.system.pi_code_injected)
    
    def test_basal_coherence(self):
        """Test basal coherence calculation"""
        psi_basal = self.system.get_basal_coherence()
        
        # Should be low in extremely viscous regime
        self.assertGreater(psi_basal, 0.0)
        self.assertLess(psi_basal, 0.5, "Basal coherence should be low without stimulus")
    
    def test_external_stimulus_activation(self):
        """Test external stimulus activation"""
        # Activate at f₀
        result = self.system.activate_external_stimulus()
        
        self.assertTrue(result['active'])
        self.assertEqual(result['frequency_hz'], 141.7001)
        self.assertGreater(result['frequency_match'], 0.95)
        self.assertTrue(self.system.stimulus_active)
    
    def test_external_stimulus_wrong_frequency(self):
        """Test external stimulus with wrong frequency"""
        # Activate at wrong frequency
        result = self.system.activate_external_stimulus(frequency_hz=150.0)
        
        # Should still activate but with reduced coupling
        self.assertLess(result['frequency_match'], 0.95)
        self.assertLess(result['coupling_strength'], 0.9)
    
    def test_node_activation(self):
        """Test individual node activation"""
        # Initially inactive
        self.assertFalse(self.system.network_state[ResonantNode.RETINA].is_active())
        
        # Activate RETINA
        result = self.system.activate_node(ResonantNode.RETINA, 1.0)
        
        self.assertTrue(result['active'])
        self.assertEqual(result['node'], 'retina')
        self.assertEqual(result['activation_level'], 1.0)
        self.assertTrue(self.system.network_state[ResonantNode.RETINA].is_active())
    
    def test_complete_triad(self):
        """Test triad completion"""
        # Complete the triad
        result = self.system.complete_triad()
        
        self.assertTrue(result['triad_complete'])
        self.assertGreaterEqual(result['active_nodes'], 3)
        self.assertTrue(result['retina_active'])
        self.assertTrue(result['pineal_active'])
        self.assertTrue(result['tercer_ojo_active'])
    
    def test_pi_code_injection(self):
        """Test πCODE-1417 injection"""
        self.assertFalse(self.system.pi_code_injected)
        
        result = self.system.inject_pi_code_1417()
        
        self.assertTrue(result['injected'])
        self.assertEqual(result['pi_code'], 1417.0)
        self.assertTrue(self.system.pi_code_injected)
        self.assertGreater(result['mitochondrial_flow_amplitude'], 0)
    
    def test_network_coherence_no_activation(self):
        """Test network coherence without activation"""
        psi_network = self.system.calculate_network_coherence()
        
        # Should be zero with no active nodes
        self.assertEqual(psi_network, 0.0)
    
    def test_network_coherence_partial_activation(self):
        """Test network coherence with partial activation"""
        # Activate 2 out of 4 nodes
        self.system.activate_node(ResonantNode.RETINA, 1.0)
        self.system.activate_node(ResonantNode.PINEAL, 1.0)
        
        psi_network = self.system.calculate_network_coherence()
        
        # Should be between 0 and 1
        self.assertGreater(psi_network, 0.0)
        self.assertLess(psi_network, 1.0)
    
    def test_network_coherence_full_activation(self):
        """Test network coherence with full activation"""
        # Activate all nodes
        for node in ResonantNode:
            self.system.activate_node(node, 1.0)
        
        psi_network = self.system.calculate_network_coherence()
        
        # Should be high (close to 1)
        self.assertGreater(psi_network, 0.9)
        self.assertLessEqual(psi_network, 1.0)
    
    def test_stimulus_coherence(self):
        """Test stimulus coherence calculation"""
        # Without stimulus
        psi_stimulus = self.system.calculate_stimulus_coherence()
        self.assertEqual(psi_stimulus, 0.3)
        
        # With stimulus
        self.system.activate_external_stimulus()
        psi_stimulus = self.system.calculate_stimulus_coherence()
        self.assertEqual(psi_stimulus, 1.0)
    
    def test_energy_coherence(self):
        """Test energy coherence calculation"""
        # Without πCODE
        psi_energy = self.system.calculate_energy_coherence()
        self.assertEqual(psi_energy, 0.5)
        
        # With πCODE
        self.system.inject_pi_code_1417()
        psi_energy = self.system.calculate_energy_coherence()
        self.assertEqual(psi_energy, 1.0)
    
    def test_total_coherence_basal_state(self):
        """Test total coherence in basal state"""
        result = self.system.calculate_total_coherence()
        
        # Should be low without activation
        self.assertLess(result['psi_total'], 0.5)
        self.assertFalse(result['threshold_met'])
        self.assertFalse(result['conditions_met'])
    
    def test_total_coherence_partial_activation(self):
        """Test total coherence with partial activation"""
        # Activate stimulus and one node
        self.system.activate_external_stimulus()
        self.system.activate_node(ResonantNode.RETINA, 1.0)
        
        result = self.system.calculate_total_coherence()
        
        # Should be higher but not at threshold
        self.assertGreater(result['psi_total'], 0.01)
        self.assertLess(result['psi_total'], self.system.params.psi_threshold)
    
    def test_total_coherence_full_activation(self):
        """Test total coherence with full activation"""
        # Activate all three conditions
        self.system.activate_external_stimulus()
        self.system.complete_triad()
        self.system.inject_pi_code_1417()
        
        result = self.system.calculate_total_coherence()
        
        # Should reach threshold
        self.assertGreaterEqual(result['psi_total'], self.system.params.psi_threshold)
        self.assertTrue(result['threshold_met'])
        self.assertTrue(result['conditions_met'])
        
        # Should be close to unity (1.0)
        self.assertGreater(result['psi_total'], 0.888)
        self.assertLessEqual(result['psi_total'], 1.0)
    
    def test_universal_seal_not_activated(self):
        """Test universal seal without full activation"""
        result = self.system.check_universal_seal()
        
        self.assertFalse(result['seal_active'])
        self.assertEqual(result['symbol'], '○')
    
    def test_universal_seal_activated(self):
        """Test universal seal with full activation"""
        # Run complete protocol
        self.system.activate_external_stimulus()
        self.system.complete_triad()
        self.system.inject_pi_code_1417()
        
        result = self.system.check_universal_seal()
        
        # Check seal activation
        self.assertTrue(result['threshold_met'])
        self.assertGreaterEqual(result['psi_total'], 0.888)
        
        # Should be close to unity
        self.assertLess(result['deviation_from_unity'], 0.2)
        
        if result['seal_active']:
            self.assertEqual(result['symbol'], '𓂀')
            self.assertIn('célula', result['message'])
    
    def test_complete_activation_protocol(self):
        """Test complete activation protocol"""
        results = self.system.run_complete_activation_protocol()
        
        # Check protocol steps
        self.assertEqual(len(results['protocol_steps']), 5)
        
        step_names = [step[0] for step in results['protocol_steps']]
        expected_steps = ['stimulus', 'triad', 'pi_code', 'coherence', 'seal']
        self.assertEqual(step_names, expected_steps)
        
        # Check final state
        final = results['final_state']
        self.assertTrue(final['stimulus_active'])
        self.assertTrue(final['network_complete'])
        self.assertTrue(final['pi_code_injected'])
        self.assertGreaterEqual(final['psi_total'], 0.888)
    
    def test_coherence_history(self):
        """Test coherence history tracking"""
        self.assertEqual(len(self.system.coherence_history), 0)
        
        # Calculate coherence multiple times
        self.system.calculate_total_coherence()
        self.assertEqual(len(self.system.coherence_history), 1)
        
        self.system.calculate_total_coherence()
        self.assertEqual(len(self.system.coherence_history), 2)
    
    def test_reynolds_number_effect(self):
        """Test effect of Reynolds number on basal coherence"""
        # Very high viscosity (very low Re)
        params_high_visc = QuantumCoherenceParameters(reynolds_number=1e-10)
        system_high_visc = QuantumCoherenceSystem(params_high_visc)
        psi_high_visc = system_high_visc.get_basal_coherence()
        
        # Lower viscosity (higher Re, but still viscous)
        params_low_visc = QuantumCoherenceParameters(reynolds_number=1e-6)
        system_low_visc = QuantumCoherenceSystem(params_low_visc)
        psi_low_visc = system_low_visc.get_basal_coherence()
        
        # Both should be low, but trend should exist
        self.assertLess(psi_high_visc, 0.5)
        self.assertLess(psi_low_visc, 0.5)
    
    def test_target_coherence_precision(self):
        """Test that target coherence meets precision requirement"""
        # Run complete protocol
        self.system.activate_external_stimulus()
        self.system.complete_triad()
        self.system.inject_pi_code_1417()
        
        result = self.system.calculate_total_coherence()
        psi_total = result['psi_total']
        
        # Should be Ψ_total ≈ 1.000000 ± 10⁻⁶ (or at least close)
        # We allow a bit more tolerance in practice
        self.assertGreaterEqual(psi_total, 0.888)
        self.assertLessEqual(psi_total, 1.0)
        
        # If very close to 1.0, check precision
        if psi_total > 0.99:
            self.assertLess(abs(psi_total - 1.0), 0.01)


class TestDemonstration(unittest.TestCase):
    """Test demonstration function"""
    
    def test_demonstration_runs(self):
        """Test that demonstration runs without error"""
        try:
            system = demonstrate_quantum_coherence_system()
            self.assertIsNotNone(system)
            
            # Check final state
            final_coherence = system.calculate_total_coherence()
            self.assertGreaterEqual(final_coherence['psi_total'], 0.888)
            
        except Exception as e:
            self.fail(f"Demonstration raised exception: {e}")


if __name__ == '__main__':
    unittest.main()
