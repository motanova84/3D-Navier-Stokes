#!/usr/bin/env python3
"""
Test Suite for Ψ-NSE v1.0 Resonance Implementation
===================================================

Tests for:
- Ψ-NSE v1.0 core functionality
- Industrial modules (Ψ-Lift, Q-Drag, Noetic-Aero)
- MCP-Δ1 verification system
- Coherence mining framework

Author: JMMB Ψ✧∞³
License: MIT
"""

import unittest
import numpy as np
from psi_nse_v1_resonance import (
    PsiNSEv1, IndustrialModules, ModuleState,
    ResonanceConstants, demonstrate_psi_nse_v1
)
from mcp_delta1_verifier import (
    MCPDelta1Verifier, CoherenceMining, VibrationalState,
    demonstrate_mcp_delta1
)


class TestPsiNSEv1Core(unittest.TestCase):
    """Test Ψ-NSE v1.0 core functionality"""
    
    def setUp(self):
        """Set up test fixtures"""
        self.psi_nse = PsiNSEv1()
        self.N = 50  # Number of velocity points
        self.M = 30  # Number of boundary points
        self.velocity = np.random.randn(self.N, 3) * 0.1
        self.boundary = np.random.randn(self.M, 3) * 5.0
        self.t = 0.0
    
    def test_initialization(self):
        """Test Ψ-NSE v1.0 initialization"""
        self.assertIsNotNone(self.psi_nse)
        self.assertEqual(self.psi_nse.constants.F0_HZ, 141.7001)
        self.assertEqual(self.psi_nse.constants.F_ADJUSTED_HZ, 151.7001)
        self.assertEqual(self.psi_nse.coherence_field, 1.0)
        self.assertTrue(self.psi_nse.state.laminar_guarantee)
    
    def test_psi_flow_computation(self):
        """Test Ψflow computation"""
        psi_flow = self.psi_nse.psi_flow(self.velocity, self.boundary, self.t)
        
        # Check output shape
        self.assertEqual(psi_flow.shape, self.velocity.shape)
        
        # Check for finite values
        self.assertTrue(np.all(np.isfinite(psi_flow)))
        
        # Check flow is bounded
        max_flow = np.max(np.linalg.norm(psi_flow, axis=1))
        self.assertLess(max_flow, 1e3)
    
    def test_zeta_stability(self):
        """Test ζ(s) stability computation"""
        zeta = self.psi_nse._compute_zeta_stability(self.t)
        
        # Check shape
        self.assertEqual(zeta.shape, (3,))
        
        # Check normalized
        norm = np.linalg.norm(zeta)
        self.assertAlmostEqual(norm, 1.0, places=6)
        
        # Check finite
        self.assertTrue(np.all(np.isfinite(zeta)))
    
    def test_convective_term(self):
        """Test (u·∇)u convective term"""
        for i in [0, self.N//2, self.N-1]:
            convective = self.psi_nse._compute_convective_term(self.velocity, i)
            self.assertEqual(convective.shape, (3,))
            self.assertTrue(np.all(np.isfinite(convective)))
    
    def test_breathing_boundary(self):
        """Test breathing boundary integration"""
        flow_tensor = np.random.randn(3, 3)
        integral = self.psi_nse._integrate_breathing_boundary(
            flow_tensor, self.boundary, self.t
        )
        
        self.assertEqual(integral.shape, (3,))
        self.assertTrue(np.all(np.isfinite(integral)))
    
    def test_coherence_verification(self):
        """Test coherence verification"""
        # Perfect coherence should pass
        self.assertTrue(self.psi_nse.verify_coherence(1.0))
        self.assertTrue(self.psi_nse.verify_coherence(0.9))
        
        # Below threshold should fail
        self.assertFalse(self.psi_nse.verify_coherence(0.8))
        self.assertFalse(self.psi_nse.verify_coherence(0.5))
    
    def test_laminar_guarantee(self):
        """Test laminar flow guarantee"""
        # Small velocities should be laminar
        small_v = np.random.randn(self.N, 3) * 0.1
        self.assertTrue(self.psi_nse.verify_laminar_guarantee(small_v))
        
        # Infinite velocities should fail
        infinite_v = np.full((self.N, 3), np.inf)
        self.assertFalse(self.psi_nse.verify_laminar_guarantee(infinite_v))
        
        # NaN velocities should fail
        nan_v = np.full((self.N, 3), np.nan)
        self.assertFalse(self.psi_nse.verify_laminar_guarantee(nan_v))
    
    def test_certification_hash(self):
        """Test immutable certification hash"""
        data1 = {'frequency': 151.7001, 'coherence': 1.0}
        hash1 = self.psi_nse.compute_certification_hash(data1)
        
        # Check hash format
        self.assertEqual(len(hash1), 8)
        self.assertTrue(all(c in '0123456789abcdef' for c in hash1))
        
        # Same data should give same hash
        hash2 = self.psi_nse.compute_certification_hash(data1)
        self.assertEqual(hash1, hash2)
        
        # Different data should give different hash
        data2 = {'frequency': 141.7001, 'coherence': 0.9}
        hash3 = self.psi_nse.compute_certification_hash(data2)
        self.assertNotEqual(hash1, hash3)
    
    def test_demonstrate_resonance(self):
        """Test resonance demonstration"""
        results = self.psi_nse.demonstrate_resonance()
        
        # Check result structure
        self.assertIn('coherence', results)
        self.assertIn('laminar_guaranteed', results)
        self.assertIn('frequency_hz', results)
        self.assertIn('certification_hash', results)
        
        # Check values
        self.assertEqual(results['coherence'], 1.0)
        self.assertEqual(results['frequency_hz'], 151.7001)
        self.assertTrue(results['coherence_verified'])


class TestIndustrialModules(unittest.TestCase):
    """Test industrial modules"""
    
    def setUp(self):
        """Set up test fixtures"""
        self.psi_nse = PsiNSEv1()
        self.modules = IndustrialModules(self.psi_nse)
        self.velocity = np.random.randn(50, 3) * 0.1
        self.wing = np.random.randn(30, 3) * 5.0
        self.t = 0.0
    
    def test_initialization(self):
        """Test module initialization"""
        self.assertIsNotNone(self.modules)
        self.assertIn('Ψ-Lift', self.modules.modules)
        self.assertIn('Q-Drag', self.modules.modules)
        self.assertIn('Noetic-Aero', self.modules.modules)
    
    def test_psi_lift(self):
        """Test Ψ-Lift module"""
        lift, state = self.modules.psi_lift(self.velocity, self.wing)
        
        # Check output types
        self.assertIsInstance(lift, float)
        self.assertIsInstance(state, ModuleState)
        
        # Check lift is finite
        self.assertTrue(np.isfinite(lift))
        
        # With perfect coherence, should be resonating
        self.assertIn(state, [ModuleState.RESONATING, ModuleState.ERROR])
    
    def test_q_drag(self):
        """Test Q-Drag module"""
        drag, state = self.modules.q_drag(self.velocity, self.t)
        
        # Check output types
        self.assertIsInstance(drag, float)
        self.assertIsInstance(state, ModuleState)
        
        # Check drag is finite and positive
        self.assertTrue(np.isfinite(drag))
        self.assertGreaterEqual(drag, 0.0)
        
        # Should be laminar with small velocities
        self.assertEqual(state, ModuleState.LAMINAR)
    
    def test_noetic_aero(self):
        """Test Noetic-Aero module"""
        fatigue, state = self.modules.noetic_aero(self.velocity, 'C')
        
        # Check output types
        self.assertIsInstance(fatigue, float)
        self.assertIsInstance(state, ModuleState)
        
        # Check fatigue is finite and positive
        self.assertTrue(np.isfinite(fatigue))
        self.assertGreaterEqual(fatigue, 0.0)
        
        # Should be precise with small variations
        self.assertEqual(state, ModuleState.PRECISE)
    
    def test_circulation_computation(self):
        """Test circulation computation"""
        circulation = self.modules._compute_circulation(self.velocity, self.wing)
        
        self.assertIsInstance(circulation, float)
        self.assertTrue(np.isfinite(circulation))
        self.assertGreaterEqual(circulation, 0.0)
    
    def test_viscous_dissipation(self):
        """Test viscous dissipation computation"""
        dissipation = self.modules._compute_viscous_dissipation(self.velocity)
        
        self.assertIsInstance(dissipation, float)
        self.assertTrue(np.isfinite(dissipation))
        self.assertGreaterEqual(dissipation, 0.0)


class TestMCPDelta1Verifier(unittest.TestCase):
    """Test MCP-Δ1 verification system"""
    
    def setUp(self):
        """Set up test fixtures"""
        self.verifier = MCPDelta1Verifier()
    
    def test_initialization(self):
        """Test verifier initialization"""
        self.assertIsNotNone(self.verifier)
        self.assertEqual(self.verifier.f0_hz, 141.7001)
        self.assertEqual(self.verifier.threshold, 0.888)
        self.assertEqual(len(self.verifier.verified_functions), 0)
    
    def test_verify_resonant_function(self):
        """Test verification of resonant function"""
        code = '''
def resonant_function(x: float, y: float) -> float:
    """
    A well-documented function.
    
    Args:
        x: First parameter
        y: Second parameter
    
    Returns:
        Sum of x and y
    """
    # Addition operation
    return x + y
'''
        resonance = self.verifier.verify_function_resonance(
            "resonant_function", 
            code
        )
        
        # Should have high coherence
        self.assertGreater(resonance.coherence, 0.7)
        self.assertTrue(np.isfinite(resonance.frequency))
        self.assertIn(resonance.state, [
            VibrationalState.RESONANT, 
            VibrationalState.VIBRATING
        ])
    
    def test_verify_dissonant_function(self):
        """Test verification of dissonant function"""
        code = "def f(a,b):return a*b"
        
        resonance = self.verifier.verify_function_resonance("f", code)
        
        # Should have lower coherence
        self.assertLess(resonance.coherence, 1.0)
        self.assertTrue(np.isfinite(resonance.frequency))
    
    def test_code_coherence_computation(self):
        """Test code coherence computation"""
        # Well-structured code
        good_code = '''
def good(x: int) -> int:
    """Docstring"""
    # Comment
    return x + 1
'''
        coherence_good = self.verifier._compute_code_coherence(good_code)
        self.assertGreater(coherence_good, 0.7)
        self.assertLessEqual(coherence_good, 1.0)
        
        # Poorly structured code
        bad_code = "def bad(x):return x"
        coherence_bad = self.verifier._compute_code_coherence(bad_code)
        self.assertLess(coherence_bad, coherence_good)
    
    def test_vibrational_frequency_computation(self):
        """Test vibrational frequency computation"""
        code = "def simple(): return 1"
        freq = self.verifier._compute_vibrational_frequency(code)
        
        # Should be near f₀
        self.assertGreater(freq, 100.0)
        self.assertLess(freq, 300.0)
    
    def test_resonance_threshold(self):
        """Test resonance threshold checking"""
        from mcp_delta1_verifier import CodeResonance
        
        resonant = CodeResonance(0.95, 141.7001, VibrationalState.RESONANT, True)
        self.assertTrue(resonant.meets_threshold(0.888))
        
        dissonant = CodeResonance(0.7, 141.7001, VibrationalState.DISSONANT, False)
        self.assertFalse(dissonant.meets_threshold(0.888))


class TestCoherenceMining(unittest.TestCase):
    """Test coherence mining framework"""
    
    def setUp(self):
        """Set up test fixtures"""
        self.mining = CoherenceMining()
    
    def test_initialization(self):
        """Test mining initialization"""
        self.assertIsNotNone(self.mining)
        self.assertEqual(self.mining.f0_hz, 141.7001)
        self.assertEqual(self.mining.mined_coherence, 0.0)
        self.assertEqual(len(self.mining.computation_nodes), 0)
    
    def test_mine_coherence(self):
        """Test coherence mining"""
        comp_time = 1.5
        coherence = self.mining.mine_coherence(comp_time)
        
        # Check coherence generated
        self.assertGreater(coherence, 0.0)
        self.assertTrue(np.isfinite(coherence))
        
        # Check total updated
        self.assertEqual(self.mining.mined_coherence, coherence)
        
        # Check node recorded
        self.assertEqual(len(self.mining.computation_nodes), 1)
    
    def test_multiple_mining(self):
        """Test multiple mining operations"""
        coherence1 = self.mining.mine_coherence(1.0)
        coherence2 = self.mining.mine_coherence(2.0)
        
        # Total should be sum
        self.assertAlmostEqual(
            self.mining.mined_coherence, 
            coherence1 + coherence2,
            places=10
        )
        
        # Should have 2 nodes
        self.assertEqual(len(self.mining.computation_nodes), 2)
    
    def test_certify_truth(self):
        """Test truth certification"""
        result = {'computation': 'test', 'value': 42}
        cert_hash = self.mining.certify_truth(result)
        
        # Check hash format
        self.assertEqual(len(cert_hash), 8)
        self.assertTrue(all(c in '0123456789abcdef' for c in cert_hash))
        
        # Check certificate recorded
        self.assertEqual(len(self.mining.truth_certificates), 1)
    
    def test_mining_stats(self):
        """Test mining statistics"""
        self.mining.mine_coherence(1.0)
        self.mining.mine_coherence(2.0)
        
        stats = self.mining.get_mining_stats()
        
        # Check stats structure
        self.assertIn('total_coherence', stats)
        self.assertIn('computation_nodes', stats)
        self.assertIn('truth_certificates', stats)
        self.assertIn('average_coherence_per_node', stats)
        
        # Check values
        self.assertEqual(stats['computation_nodes'], 2)
        self.assertGreater(stats['total_coherence'], 0.0)


class TestIntegration(unittest.TestCase):
    """Integration tests for complete system"""
    
    def test_full_psi_nse_v1_demonstration(self):
        """Test full Ψ-NSE v1.0 demonstration"""
        psi_nse, modules, results = demonstrate_psi_nse_v1()
        
        # Check all components initialized
        self.assertIsNotNone(psi_nse)
        self.assertIsNotNone(modules)
        self.assertIsNotNone(results)
        
        # Check results
        self.assertEqual(results['coherence'], 1.0)
        self.assertTrue(results['coherence_verified'])
        self.assertEqual(results['frequency_hz'], 151.7001)
    
    def test_full_mcp_delta1_demonstration(self):
        """Test full MCP-Δ1 demonstration"""
        verifier, mining = demonstrate_mcp_delta1()
        
        # Check components
        self.assertIsNotNone(verifier)
        self.assertIsNotNone(mining)
        
        # Check verification occurred
        self.assertGreater(len(verifier.verified_functions), 0)
        
        # Check mining occurred
        self.assertGreater(mining.mined_coherence, 0.0)
    
    def test_cross_module_integration(self):
        """Test integration between Ψ-NSE and MCP-Δ1"""
        # Create Ψ-NSE system
        psi_nse = PsiNSEv1()
        modules = IndustrialModules(psi_nse)
        
        # Verify coherence with MCP-Δ1
        verifier = MCPDelta1Verifier()
        
        # Verify Ψ-NSE coherence meets threshold
        coherence_ok = psi_nse.verify_coherence(psi_nse.coherence_field)
        self.assertTrue(coherence_ok)
        
        # Mine coherence from computation
        mining = CoherenceMining()
        coherence = mining.mine_coherence(1.0)
        
        # Certify results
        results = psi_nse.demonstrate_resonance()
        cert_hash = mining.certify_truth(results)
        
        self.assertEqual(len(cert_hash), 8)


def run_tests():
    """Run all tests"""
    print("="*80)
    print("  🧪 EJECUTANDO PRUEBAS Ψ-NSE v1.0")
    print("="*80)
    
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test cases
    suite.addTests(loader.loadTestsFromTestCase(TestPsiNSEv1Core))
    suite.addTests(loader.loadTestsFromTestCase(TestIndustrialModules))
    suite.addTests(loader.loadTestsFromTestCase(TestMCPDelta1Verifier))
    suite.addTests(loader.loadTestsFromTestCase(TestCoherenceMining))
    suite.addTests(loader.loadTestsFromTestCase(TestIntegration))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Print summary
    print("\n" + "="*80)
    print("  📊 RESUMEN DE PRUEBAS")
    print("="*80)
    print(f"  Total: {result.testsRun}")
    print(f"  ✅ Exitosas: {result.testsRun - len(result.failures) - len(result.errors)}")
    print(f"  ❌ Fallidas: {len(result.failures)}")
    print(f"  ⚠️ Errores: {len(result.errors)}")
    print("="*80)
    
    return result.wasSuccessful()


if __name__ == "__main__":
    success = run_tests()
    exit(0 if success else 1)
