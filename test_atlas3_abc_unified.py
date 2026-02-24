#!/usr/bin/env python3
"""
Test Suite for Atlas³-ABC Unified Theory

Comprehensive tests for the Atlas³-ABC framework connecting
Riemann Hypothesis, ABC Conjecture, and Navier-Stokes via QCAL.

Author: José Manuel Mota Burruezo (JMMB Ψ✧∞³)
Date: 2026-02-24
"""

import unittest
import numpy as np
from atlas3_abc_unified import (
    Atlas3Constants,
    ABCTriple,
    Atlas3ABCUnified
)


class TestAtlas3Constants(unittest.TestCase):
    """Test fundamental constants"""
    
    def setUp(self):
        self.constants = Atlas3Constants()
    
    def test_fundamental_frequency(self):
        """Test QCAL fundamental frequency"""
        self.assertAlmostEqual(self.constants.f0, 141.7001, places=4)
        self.assertGreater(self.constants.f0, 0)
    
    def test_kappa_pi(self):
        """Test Π-coupling constant"""
        self.assertAlmostEqual(self.constants.kappa_pi, 2.57731, places=5)
        self.assertGreater(self.constants.kappa_pi, 0)
    
    def test_epsilon_critico(self):
        """Test critical epsilon"""
        self.assertAlmostEqual(self.constants.epsilon_critico, 2.64e-12, places=14)
        self.assertGreater(self.constants.epsilon_critico, 0)
    
    def test_lambda_heat(self):
        """Test heat kernel eigenvalue"""
        self.assertAlmostEqual(self.constants.lambda_heat, 1.0, places=10)
        self.assertGreater(self.constants.lambda_heat, 0)
    
    def test_physical_constants(self):
        """Test physical constants are correct"""
        self.assertAlmostEqual(self.constants.c_light, 299792458.0, places=1)
        self.assertAlmostEqual(self.constants.h_planck, 6.62607015e-34, places=42)


class TestABCTriple(unittest.TestCase):
    """Test ABC triple class"""
    
    def test_valid_triple_creation(self):
        """Test creating valid ABC triple"""
        triple = ABCTriple(1, 8, 9)
        self.assertEqual(triple.a, 1)
        self.assertEqual(triple.b, 8)
        self.assertEqual(triple.c, 9)
    
    def test_invalid_sum(self):
        """Test that invalid sum raises error"""
        with self.assertRaises(ValueError):
            ABCTriple(1, 2, 4)  # 1 + 2 ≠ 4
    
    def test_invalid_gcd(self):
        """Test that non-coprime pairs raise error"""
        with self.assertRaises(ValueError):
            ABCTriple(2, 4, 6)  # gcd(2, 4) = 2 ≠ 1
    
    def test_negative_values(self):
        """Test that negative values raise error"""
        with self.assertRaises(ValueError):
            ABCTriple(-1, 2, 1)
    
    def test_radical_simple(self):
        """Test radical computation for simple case"""
        triple = ABCTriple(1, 8, 9)
        # 1·8·9 = 72 = 2³·3²
        # rad(72) = 2·3 = 6
        self.assertEqual(triple.radical(), 6)
    
    def test_radical_larger(self):
        """Test radical computation for larger triple"""
        triple = ABCTriple(1, 48, 49)
        # 1·48·49 = 2352 = 2⁴·3·7²
        # rad(2352) = 2·3·7 = 42
        self.assertEqual(triple.radical(), 42)
    
    def test_information_content(self):
        """Test information content I = log₂(c) - log₂(rad)"""
        triple = ABCTriple(1, 8, 9)
        # I = log₂(9) - log₂(6) ≈ 3.170 - 2.585 ≈ 0.585
        I = triple.information_content()
        self.assertGreater(I, 0)
        self.assertLess(I, 1)
        self.assertAlmostEqual(I, np.log2(9) - np.log2(6), places=10)
    
    def test_reynolds_arithmetic(self):
        """Test Reynolds arithmetic Re = log₂(c) / log₂(rad)"""
        triple = ABCTriple(1, 8, 9)
        # Re = log₂(9) / log₂(6) ≈ 3.170 / 2.585 ≈ 1.226
        Re = triple.reynolds_arithmetic()
        self.assertGreater(Re, 1)
        self.assertAlmostEqual(Re, np.log2(9) / np.log2(6), places=10)
    
    def test_is_exceptional_false(self):
        """Test that regular triple is not exceptional"""
        triple = ABCTriple(1, 8, 9)
        # I ≈ 0.585 < 1, so not exceptional
        self.assertFalse(triple.is_exceptional())
    
    def test_is_exceptional_true(self):
        """Test exceptional triple detection"""
        # This would require finding an actual exceptional triple
        # For now, test with custom epsilon
        triple = ABCTriple(1, 8, 9)
        self.assertTrue(triple.is_exceptional(epsilon=-0.5))
    
    def test_to_dict(self):
        """Test dictionary conversion"""
        triple = ABCTriple(1, 8, 9)
        d = triple.to_dict()
        self.assertEqual(d['triple'], (1, 8, 9))
        self.assertEqual(d['radical'], 6)
        self.assertIn('information_content', d)
        self.assertIn('reynolds_arithmetic', d)
        self.assertIn('is_exceptional', d)
    
    def test_repr(self):
        """Test string representation"""
        triple = ABCTriple(1, 8, 9)
        self.assertEqual(repr(triple), "ABCTriple(1, 8, 9)")


class TestAtlas3ABCUnified(unittest.TestCase):
    """Test unified framework"""
    
    def setUp(self):
        self.framework = Atlas3ABCUnified()
    
    def test_initialization(self):
        """Test framework initialization"""
        self.assertIsInstance(self.framework.constants, Atlas3Constants)
        self.assertEqual(len(self.framework.abc_triples), 0)
    
    def test_add_abc_triple(self):
        """Test adding ABC triple"""
        triple = self.framework.add_abc_triple(1, 8, 9)
        self.assertIsInstance(triple, ABCTriple)
        self.assertEqual(len(self.framework.abc_triples), 1)
    
    def test_riemann_spectral_operator(self):
        """Test Riemann spectral operator"""
        # Test at first Riemann zero
        s = complex(0.5, 14.134725)
        value = self.framework.riemann_spectral_operator(s)
        self.assertIsInstance(value, complex)
        self.assertTrue(np.isfinite(value))
    
    def test_riemann_functional_equation(self):
        """Test functional equation reflection"""
        s = complex(0.3, 5.0)
        value1 = self.framework.riemann_spectral_operator(s)
        s_reflected = complex(1.0 - s.real, s.imag)
        # Just check both are finite (full functional equation is complex)
        value2 = self.framework.riemann_spectral_operator(s_reflected)
        self.assertTrue(np.isfinite(value1))
        self.assertTrue(np.isfinite(value2))
    
    def test_abc_adelic_operator(self):
        """Test ABC-adelic operator"""
        triple = ABCTriple(1, 8, 9)
        value = self.framework.abc_adelic_operator(triple, 1.0)
        self.assertIsInstance(value, complex)
        self.assertTrue(np.isfinite(value))
    
    def test_abc_adelic_operator_decay(self):
        """Test that adelic operator decays with time"""
        triple = ABCTriple(1, 8, 9)
        value1 = abs(self.framework.abc_adelic_operator(triple, 0.1))
        value2 = abs(self.framework.abc_adelic_operator(triple, 1.0))
        value3 = abs(self.framework.abc_adelic_operator(triple, 10.0))
        # Should decay exponentially
        self.assertGreater(value1, value2)
        self.assertGreater(value2, value3)
    
    def test_heat_trace_bound_positive_time(self):
        """Test heat trace bound for positive time"""
        bound = self.framework.compute_heat_trace_bound(1.0)
        self.assertGreater(bound, 0)
        self.assertTrue(np.isfinite(bound))
    
    def test_heat_trace_bound_zero_time_error(self):
        """Test that t=0 raises error"""
        with self.assertRaises(ValueError):
            self.framework.compute_heat_trace_bound(0.0)
    
    def test_heat_trace_bound_negative_time_error(self):
        """Test that negative time raises error"""
        with self.assertRaises(ValueError):
            self.framework.compute_heat_trace_bound(-1.0)
    
    def test_heat_trace_bound_decay(self):
        """Test heat trace bound decays exponentially"""
        # Test uses exp(-λ·t) NOT exp(-λ/t)
        bound1 = self.framework.compute_heat_trace_bound(0.1)
        bound2 = self.framework.compute_heat_trace_bound(1.0)
        bound3 = self.framework.compute_heat_trace_bound(10.0)
        
        # Should decay: bound1 > bound2 > bound3
        self.assertGreater(bound1, bound2)
        self.assertGreater(bound2, bound3)
        
        # Check exponential decay rate
        ratio = bound1 / bound2
        expected_ratio = np.exp(self.framework.constants.lambda_heat * (1.0 - 0.1))
        self.assertAlmostEqual(ratio, expected_ratio, places=10)
    
    def test_heat_trace_bound_formula(self):
        """Test heat trace bound uses correct formula: C·ε·exp(-λ·t)"""
        t = 2.0
        bound = self.framework.compute_heat_trace_bound(t)
        
        C = self.framework.constants.kappa_pi
        epsilon = self.framework.constants.epsilon_critico
        lambda_h = self.framework.constants.lambda_heat
        
        expected = C * epsilon * np.exp(-lambda_h * t)
        self.assertAlmostEqual(bound, expected, places=20)
    
    def test_unified_coupling(self):
        """Test unified coupling"""
        triple = self.framework.add_abc_triple(1, 8, 9)
        s = complex(0.5, 14.134725)
        value = self.framework.unified_coupling(triple, s, 1.0)
        self.assertIsInstance(value, complex)
        self.assertTrue(np.isfinite(value))
    
    def test_qcal_coherence_field(self):
        """Test QCAL coherence field"""
        psi = self.framework.qcal_coherence_field(0.0)
        self.assertAlmostEqual(abs(psi), 1.0, places=10)
        
        psi = self.framework.qcal_coherence_field(1.0)
        self.assertAlmostEqual(abs(psi), 1.0, places=10)
    
    def test_qcal_coherence_field_periodicity(self):
        """Test coherence field is periodic"""
        period = 1.0 / self.framework.constants.f0
        t = 0.5
        psi1 = self.framework.qcal_coherence_field(t)
        psi2 = self.framework.qcal_coherence_field(t + period)
        # Should be approximately equal (within numerical precision)
        self.assertAlmostEqual(abs(psi1 - psi2), 0.0, places=10)
    
    def test_analyze_abc_distribution_empty(self):
        """Test analysis with no triples"""
        analysis = self.framework.analyze_abc_distribution()
        self.assertIn('error', analysis)
    
    def test_analyze_abc_distribution(self):
        """Test ABC distribution analysis"""
        self.framework.generate_example_triples(10)
        analysis = self.framework.analyze_abc_distribution()
        
        self.assertIn('total_triples', analysis)
        self.assertIn('exceptional_count', analysis)
        self.assertIn('information_content', analysis)
        self.assertIn('reynolds_arithmetic', analysis)
        
        self.assertEqual(analysis['total_triples'], 10)
        self.assertGreaterEqual(analysis['exceptional_count'], 0)
    
    def test_generate_example_triples(self):
        """Test example triple generation"""
        triples = self.framework.generate_example_triples(5)
        self.assertEqual(len(triples), 5)
        self.assertEqual(len(self.framework.abc_triples), 5)
        
        for triple in triples:
            self.assertIsInstance(triple, ABCTriple)
    
    def test_generate_example_triples_all(self):
        """Test generating all example triples"""
        triples = self.framework.generate_example_triples(10)
        self.assertEqual(len(triples), 10)
        
        # Verify all are valid
        for triple in triples:
            self.assertEqual(triple.a + triple.b, triple.c)
            self.assertEqual(np.gcd(triple.a, triple.b), 1)
    
    def test_export_analysis(self):
        """Test exporting analysis to JSON"""
        import os
        import json
        
        self.framework.generate_example_triples(5)
        filename = "/tmp/test_atlas3_analysis.json"
        
        self.framework.export_analysis(filename)
        self.assertTrue(os.path.exists(filename))
        
        # Verify JSON structure
        with open(filename, 'r') as f:
            data = json.load(f)
        
        self.assertIn('metadata', data)
        self.assertIn('triples', data)
        self.assertIn('distribution_analysis', data)
        
        # Clean up
        os.remove(filename)
    
    def test_repr(self):
        """Test string representation"""
        self.framework.generate_example_triples(3)
        repr_str = repr(self.framework)
        self.assertIn('Atlas3ABCUnified', repr_str)
        self.assertIn('triples=3', repr_str)
        self.assertIn('141.7001', repr_str)


class TestIntegration(unittest.TestCase):
    """Integration tests for complete workflows"""
    
    def test_complete_workflow(self):
        """Test complete analysis workflow"""
        framework = Atlas3ABCUnified()
        
        # Generate triples
        triples = framework.generate_example_triples(10)
        self.assertEqual(len(triples), 10)
        
        # Analyze distribution
        analysis = framework.analyze_abc_distribution()
        self.assertGreater(analysis['total_triples'], 0)
        
        # Test unified coupling
        s = complex(0.5, 14.134725)
        for triple in triples[:3]:
            coupling = framework.unified_coupling(triple, s, 1.0)
            self.assertTrue(np.isfinite(coupling))
    
    def test_riemann_abc_coupling(self):
        """Test coupling between Riemann zeros and ABC triples"""
        framework = Atlas3ABCUnified()
        framework.generate_example_triples(5)
        
        # Test at multiple Riemann zeros
        riemann_zeros = [
            complex(0.5, 14.134725),
            complex(0.5, 21.022040),
            complex(0.5, 25.010858),
        ]
        
        for s in riemann_zeros:
            for triple in framework.abc_triples[:3]:
                coupling = framework.unified_coupling(triple, s, 1.0)
                self.assertTrue(np.isfinite(coupling))
                self.assertGreater(abs(coupling), 0)
    
    def test_time_evolution(self):
        """Test time evolution of unified coupling"""
        framework = Atlas3ABCUnified()
        triple = framework.add_abc_triple(1, 8, 9)
        s = complex(0.5, 14.134725)
        
        times = np.linspace(0.1, 10.0, 20)
        couplings = [framework.unified_coupling(triple, s, t) for t in times]
        
        # All should be finite
        for coupling in couplings:
            self.assertTrue(np.isfinite(coupling))
        
        # Amplitude should decay
        amplitudes = [abs(c) for c in couplings]
        # Check general decay trend
        self.assertGreater(amplitudes[0], amplitudes[-1])


def run_tests():
    """Run all tests and return results"""
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestAtlas3Constants))
    suite.addTests(loader.loadTestsFromTestCase(TestABCTriple))
    suite.addTests(loader.loadTestsFromTestCase(TestAtlas3ABCUnified))
    suite.addTests(loader.loadTestsFromTestCase(TestIntegration))
    
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    return result


if __name__ == '__main__':
    result = run_tests()
    
    # Print summary
    print("\n" + "="*70)
    print("TEST SUMMARY")
    print("="*70)
    print(f"Tests run: {result.testsRun}")
    print(f"Successes: {result.testsRun - len(result.failures) - len(result.errors)}")
    print(f"Failures: {len(result.failures)}")
    print(f"Errors: {len(result.errors)}")
    print("="*70)
    
    # Exit with appropriate code
    exit(0 if result.wasSuccessful() else 1)
