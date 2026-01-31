#!/usr/bin/env python3
"""
Test suite for QCAL Unified Framework

Tests the core functionality of the QCAL unified framework including:
- Universal constants
- Spectral operators
- Problem verification
- Cross-verification protocol
"""

import unittest
import numpy as np
from qcal_unified_framework import (
    QCALUnifiedFramework, 
    UniversalConstants,
    MillenniumProblem
)
from cross_verification_protocol import CrossVerificationProtocol


class TestUniversalConstants(unittest.TestCase):
    """Test universal constants structure and relationships"""
    
    def setUp(self):
        self.constants = UniversalConstants()
    
    def test_constant_values(self):
        """Test that constants have expected values"""
        self.assertAlmostEqual(self.constants.kappa_pi, 2.5773, places=4)
        self.assertAlmostEqual(self.constants.f0, 141.7001, places=4)
        self.assertAlmostEqual(self.constants.critical_line, 0.5, places=10)
        self.assertAlmostEqual(self.constants.ramsey_ratio, 43.0/108.0, places=6)
        self.assertAlmostEqual(self.constants.navier_stokes_epsilon, 0.5772, places=4)
        self.assertAlmostEqual(self.constants.bsd_delta, 1.0, places=10)
    
    def test_constant_coherence(self):
        """Test that constants form coherent system"""
        coherence = self.constants.verify_coherence()
        
        # All checks should pass
        self.assertTrue(coherence['critical_line_is_half'])
        self.assertTrue(coherence['bsd_delta_is_one'])
        self.assertTrue(coherence['correspondence'])
        self.assertTrue(coherence['kappa_positive'])
        self.assertTrue(coherence['f0_positive'])
        self.assertTrue(coherence['ramsey_positive'])
        self.assertTrue(coherence['epsilon_positive'])
    
    def test_constant_relationships(self):
        """Test mathematical relationships between constants"""
        relationships = self.constants.constant_relationships()
        
        # Check that all relationship values are computed
        self.assertIn('f0_kappa_product', relationships)
        self.assertIn('ramsey_scaled', relationships)
        self.assertIn('epsilon_times_critical', relationships)
        self.assertIn('universal_coherence_measure', relationships)
        
        # Values should be positive
        for value in relationships.values():
            self.assertGreater(value, 0)


class TestQCALFramework(unittest.TestCase):
    """Test main QCAL unified framework"""
    
    def setUp(self):
        self.framework = QCALUnifiedFramework()
    
    def test_framework_initialization(self):
        """Test framework initializes correctly"""
        self.assertIsNotNone(self.framework.constants)
        self.assertIsNotNone(self.framework.problems)
        self.assertIsNotNone(self.framework.operators)
        
        # Should have 6 problems
        self.assertEqual(len(self.framework.problems), 6)
        self.assertEqual(len(self.framework.operators), 6)
    
    def test_millennium_problems(self):
        """Test millennium problem instances"""
        expected_problems = [
            'p_vs_np', 'riemann', 'bsd', 
            'navier_stokes', 'ramsey', 'yang_mills'
        ]
        
        for problem_key in expected_problems:
            self.assertIn(problem_key, self.framework.problems)
            problem = self.framework.problems[problem_key]
            self.assertIsInstance(problem, MillenniumProblem)
            self.assertIsNotNone(problem.name)
            self.assertIsNotNone(problem.problem_statement)
            self.assertIsNotNone(problem.qcal_operator_name)
            self.assertGreater(problem.universal_constant, 0)
    
    def test_p_vs_np_operator(self):
        """Test D_PNP operator"""
        result = self.framework.D_PNP_operator({'kappa_pi': 2.5773, 'treewidth': 10})
        
        self.assertEqual(result['operator'], 'D_PNP')
        self.assertGreater(result['eigenvalue'], 0)
        self.assertEqual(result['constant'], 2.5773)
        self.assertIn('interpretation', result)
    
    def test_riemann_operator(self):
        """Test H_Psi operator"""
        result = self.framework.H_Psi_operator({'f0': 141.7001})
        
        self.assertEqual(result['operator'], 'H_Ψ')
        self.assertAlmostEqual(result['eigenvalue'], 141.7001, places=4)
        self.assertGreater(result['resonant_frequency'], 0)
        self.assertEqual(result['critical_line'], 0.5)
    
    def test_bsd_operator(self):
        """Test L_E operator"""
        result = self.framework.L_E_operator({'delta': 1.0})
        
        self.assertEqual(result['operator'], 'L_E')
        self.assertEqual(result['eigenvalue'], 1.0)
        self.assertEqual(result['constant'], 1.0)
    
    def test_navier_stokes_operator(self):
        """Test NS operator"""
        result = self.framework.NS_operator({'epsilon': 0.5772, 'f0': 141.7001})
        
        self.assertEqual(result['operator'], '∇·u')
        self.assertAlmostEqual(result['eigenvalue'], 0.5772, places=4)
        self.assertGreater(result['regularity_bound'], 0)
        self.assertAlmostEqual(result['resonant_frequency'], 141.7001, places=4)
    
    def test_ramsey_operator(self):
        """Test Ramsey operator"""
        result = self.framework.R_operator({'phi_r': 43.0/108.0, 'm': 3, 'n': 3})
        
        self.assertEqual(result['operator'], 'R(m,n)')
        self.assertAlmostEqual(result['eigenvalue'], 43.0/108.0, places=6)
        self.assertGreater(result['ramsey_bound'], 0)
    
    def test_yang_mills_operator(self):
        """Test Yang-Mills operator"""
        result = self.framework.YM_operator({'g_ym': np.sqrt(2)})
        
        self.assertEqual(result['operator'], 'YM(A)')
        self.assertAlmostEqual(result['eigenvalue'], np.sqrt(2), places=10)
        self.assertAlmostEqual(result['mass_gap'], np.sqrt(2), places=10)
    
    def test_demonstrate_unification(self):
        """Test unification demonstration"""
        results = self.framework.demonstrate_unification()
        
        # Should have results for all 6 problems
        self.assertEqual(len(results), 6)
        
        for problem_key, result in results.items():
            self.assertIn('problem', result)
            self.assertIn('eigenvalue', result)
            self.assertIn('connected_via', result)
            self.assertIn('verification_status', result)
            
            # Verification should succeed
            self.assertTrue(result['verification_status']['verified'])
    
    def test_coherence_calculation(self):
        """Test coherence score calculation"""
        coherence = self.framework.calculate_coherence()
        
        # Coherence should be high (>0.95)
        self.assertGreater(coherence, 0.95)
        self.assertLessEqual(coherence, 1.0)
    
    def test_problem_connections(self):
        """Test problem connection mapping"""
        connections = self.framework.get_problem_connections()
        
        # Each problem should connect to others
        for problem_key, connected_to in connections.items():
            self.assertIsInstance(connected_to, list)
    
    def test_verification_status(self):
        """Test verification status for all problems"""
        status = self.framework.get_verification_status()
        
        # All problems should verify
        for problem_key, verify_result in status.items():
            self.assertTrue(verify_result['verified'])
            self.assertIn('protocol', verify_result)
            self.assertIn('constant', verify_result)
            self.assertIn('operator', verify_result)


class TestCrossVerification(unittest.TestCase):
    """Test cross-verification protocol"""
    
    def setUp(self):
        self.protocol = CrossVerificationProtocol()
    
    def test_protocol_initialization(self):
        """Test protocol initializes correctly"""
        self.assertIsNotNone(self.protocol.framework)
        self.assertIsNotNone(self.protocol.problem_solutions)
        self.assertEqual(len(self.protocol.problem_solutions), 6)
    
    def test_verify_p_vs_np(self):
        """Test P vs NP verification"""
        result = self.protocol.verify_p_vs_np()
        
        self.assertEqual(result.test_name, 'P vs NP')
        self.assertTrue(result.passed)
        self.assertGreater(result.confidence, 0.9)
        self.assertIn('kappa_pi', result.details)
    
    def test_verify_riemann(self):
        """Test Riemann verification"""
        result = self.protocol.verify_riemann()
        
        self.assertEqual(result.test_name, 'Riemann Hypothesis')
        self.assertTrue(result.passed)
        self.assertGreater(result.confidence, 0.9)
        self.assertIn('f0', result.details)
        self.assertIn('critical_line', result.details)
    
    def test_verify_bsd(self):
        """Test BSD verification"""
        result = self.protocol.verify_bsd()
        
        self.assertEqual(result.test_name, 'BSD Conjecture')
        self.assertTrue(result.passed)
        self.assertGreater(result.confidence, 0.85)
        self.assertIn('delta_bsd', result.details)
    
    def test_verify_navier_stokes(self):
        """Test Navier-Stokes verification"""
        result = self.protocol.verify_navier_stokes()
        
        self.assertEqual(result.test_name, 'Navier-Stokes')
        self.assertTrue(result.passed)
        self.assertGreater(result.confidence, 0.9)
        self.assertIn('epsilon_ns', result.details)
    
    def test_verify_ramsey(self):
        """Test Ramsey verification"""
        result = self.protocol.verify_ramsey()
        
        self.assertEqual(result.test_name, 'Ramsey Numbers')
        self.assertTrue(result.passed)
        self.assertGreater(result.confidence, 0.8)
        self.assertIn('phi_ramsey', result.details)
    
    def test_verify_yang_mills(self):
        """Test Yang-Mills verification"""
        result = self.protocol.verify_yang_mills()
        
        self.assertEqual(result.test_name, 'Yang-Mills')
        self.assertTrue(result.passed)
        self.assertGreater(result.confidence, 0.85)
        self.assertIn('g_yang_mills', result.details)
    
    def test_consistency_matrix(self):
        """Test consistency matrix construction"""
        # Run individual verifications
        results = {
            key: verifier() 
            for key, verifier in self.protocol.problem_solutions.items()
        }
        
        matrix = self.protocol.build_consistency_matrix(results)
        
        # Matrix should be 6x6
        self.assertEqual(matrix.shape, (6, 6))
        
        # Diagonal should be 1.0
        for i in range(6):
            self.assertEqual(matrix[i, i], 1.0)
        
        # All values should be between 0 and 1
        self.assertTrue(np.all(matrix >= 0))
        self.assertTrue(np.all(matrix <= 1))
    
    def test_qcal_coherence(self):
        """Test QCAL coherence verification"""
        results = {
            key: verifier() 
            for key, verifier in self.protocol.problem_solutions.items()
        }
        matrix = self.protocol.build_consistency_matrix(results)
        coherence = self.protocol.verify_qcal_coherence(matrix)
        
        # Should have all required fields
        self.assertIn('constant_coherence', coherence)
        self.assertIn('matrix_coherence', coherence)
        self.assertIn('overall_coherence', coherence)
        self.assertIn('constant_checks', coherence)
        self.assertIn('all_constants_coherent', coherence)
        
        # Coherence scores should be high
        self.assertGreater(coherence['constant_coherence'], 0.95)
        self.assertGreater(coherence['overall_coherence'], 0.9)
        
        # All constants should be coherent
        self.assertTrue(coherence['all_constants_coherent'])


def run_tests():
    """Run all tests"""
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add test classes
    suite.addTests(loader.loadTestsFromTestCase(TestUniversalConstants))
    suite.addTests(loader.loadTestsFromTestCase(TestQCALFramework))
    suite.addTests(loader.loadTestsFromTestCase(TestCrossVerification))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Return success/failure
    return result.wasSuccessful()


if __name__ == '__main__':
    import sys
    success = run_tests()
    sys.exit(0 if success else 1)
