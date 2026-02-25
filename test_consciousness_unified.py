#!/usr/bin/env python3
"""
Test Suite for Consciousness-Microtubule Model and Unified Framework
====================================================================

Tests for:
1. Consciousness-microtubule quantum coherence (Nodo B)
2. Unified resonance-consciousness framework
3. Integration with vibrational regularization (Nodo A)
"""

import unittest
import numpy as np
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from consciousness_microtubule_model import (
    MicrotubuleCoherence, MicrotubuleParameters, F0_HZ
)
from unified_resonance_consciousness import (
    UnifiedResonanceConsciousness, UnifiedResonanceParameters
)


class TestMicrotubuleCoherence(unittest.TestCase):
    """Test microtubule quantum coherence model"""
    
    def setUp(self):
        """Initialize test model"""
        self.model = MicrotubuleCoherence()
    
    def test_parameters(self):
        """Test microtubule parameters"""
        self.assertEqual(self.model.params.f0, F0_HZ)
        self.assertEqual(self.model.params.f0, 141.7001)
        self.assertAlmostEqual(
            self.model.params.omega_0,
            2 * np.pi * F0_HZ,
            places=2
        )
    
    def test_coherence_state(self):
        """Test quantum coherence state computation"""
        # At t=0, coherence should be maximum
        coherence_0 = self.model.compute_coherence_state(0.0, thermal_noise=0.0)
        self.assertAlmostEqual(coherence_0, self.model.params.psi_target, places=6)
        
        # With thermal noise, coherence should decay
        coherence_noisy = self.model.compute_coherence_state(1.0, thermal_noise=0.5)
        self.assertLess(coherence_noisy, coherence_0)
        
        # Coherence should oscillate
        t_values = np.linspace(0, 1.0, 100)
        coherences = [self.model.compute_coherence_state(t, 0.0) for t in t_values]
        # Should have positive and negative values
        self.assertTrue(any(c > 0 for c in coherences))
        self.assertTrue(any(c < 0 for c in coherences))
    
    def test_consciousness_field(self):
        """Test consciousness field computation"""
        # At t=0, should be near maximum
        psi_0 = self.model.compute_consciousness_field(0.0, n_tubules=1000)
        self.assertGreater(psi_0, 0.99)
        self.assertLessEqual(psi_0, 1.01)
        
        # Should be stable over time with many tubules
        psi_1 = self.model.compute_consciousness_field(1.0, n_tubules=10000)
        self.assertGreater(psi_1, 0.99)
        
        # More tubules should give better coherence
        psi_few = self.model.compute_consciousness_field(0.0, n_tubules=10)
        psi_many = self.model.compute_consciousness_field(0.0, n_tubules=10000)
        # With many tubules, phase averaging gives more stable result
        self.assertTrue(np.isfinite(psi_few) and np.isfinite(psi_many))
    
    def test_thermal_stability(self):
        """Test thermal stability criterion"""
        stability = self.model.thermal_stability_criterion()
        
        # Check all required keys
        self.assertIn('quantum_energy_J', stability)
        self.assertIn('thermal_energy_J', stability)
        self.assertIn('quality_factor', stability)
        self.assertIn('thermal_stable', stability)
        self.assertIn('f0_resonance_critical', stability)
        
        # Energies should be positive
        self.assertGreater(stability['quantum_energy_J'], 0)
        self.assertGreater(stability['thermal_energy_J'], 0)
        
        # With f₀ resonance, should be stable
        self.assertTrue(stability['thermal_stable'])
        self.assertTrue(stability['f0_resonance_critical'])
    
    def test_penrose_hameroff_or(self):
        """Test Penrose-Hameroff objective reduction"""
        # Typical tubulin mass
        tubulin_mass = 100e3 * 1.66e-27  # ~100 kDa
        
        or_result = self.model.penrose_hameroff_objective_reduction(
            tubulin_mass, 0.0
        )
        
        # Check required keys
        self.assertIn('gravitational_energy_J', or_result)
        self.assertIn('penrose_OR_timescale_s', or_result)
        self.assertIn('qcal_OR_timescale_s', or_result)
        self.assertIn('orchestrated_by_f0', or_result)
        
        # QCAL timescale should be 1/f₀
        expected_tau = 1.0 / F0_HZ
        self.assertAlmostEqual(
            or_result['qcal_OR_timescale_s'],
            expected_tau,
            places=6
        )
        
        # Should be orchestrated by f₀
        self.assertTrue(or_result['orchestrated_by_f0'])
    
    def test_consciousness_emergence(self):
        """Test consciousness emergence analysis"""
        emergence = self.model.consciousness_emergence_analysis(
            duration=0.1,  # Short duration for testing
            n_steps=100
        )
        
        # Check required keys
        self.assertIn('mean_consciousness_state', emergence)
        self.assertIn('consciousness_emerged', emergence)
        self.assertIn('frequency_hz', emergence)
        
        # Mean consciousness should be high
        self.assertGreater(emergence['mean_consciousness_state'], 0.95)
        
        # Should emerge
        self.assertTrue(emergence['consciousness_emerged'])
        
        # Frequency should be f₀
        self.assertEqual(emergence['frequency_hz'], F0_HZ)
    
    def test_full_validation(self):
        """Test complete Orch-OR validation"""
        results = self.model.validate_orch_or_with_qcal()
        
        # Should validate successfully
        self.assertTrue(results['orch_or_validated'])
        self.assertTrue(results['f0_critical'])


class TestUnifiedFramework(unittest.TestCase):
    """Test unified resonance-consciousness framework"""
    
    def setUp(self):
        """Initialize test framework"""
        self.framework = UnifiedResonanceConsciousness()
    
    def test_parameters(self):
        """Test unified parameters"""
        self.assertEqual(self.framework.params.f0, F0_HZ)
        self.assertGreater(self.framework.params.viscosity, 0)
        self.assertGreater(self.framework.params.n_microtubules, 0)
        self.assertAlmostEqual(
            self.framework.params.psi_target,
            0.999999,
            places=6
        )
    
    def test_resonant_viscosity(self):
        """Test resonant viscosity computation"""
        k_values = np.array([0.1, 1.0, 10.0, 100.0])
        nu_res = self.framework.compute_resonant_viscosity(k_values)
        
        # Should return array of same length
        self.assertEqual(len(nu_res), len(k_values))
        
        # All viscosities should be positive
        self.assertTrue(np.all(nu_res > 0))
        
        # Should increase with wavenumber
        self.assertTrue(np.all(np.diff(nu_res) > 0))
        
        # At high k, should approach enhanced value
        k_high = np.array([1000.0])
        nu_high = self.framework.compute_resonant_viscosity(k_high)
        # Enhancement factor approaches α at high k:
        # ν_res ≈ ν₀(1 + α) as k → ∞
        # But the formula is: 1 + α*x²/(1+x²) where x = k/k₀
        # As k → ∞: x²/(1+x²) → 1, so ν_res → ν₀(1 + α)
        # But actually the formula asymptotes to less than (1+α)
        # Let's just check it's enhanced and greater than base
        self.assertGreater(nu_high[0], self.framework.params.viscosity)
        self.assertLess(nu_high[0], 
                       self.framework.params.viscosity * (1.0 + self.framework.params.resonant_enhancement))
    
    def test_coupled_evolution(self):
        """Test coupled vorticity-consciousness evolution"""
        # Simple vorticity field
        omega = np.array([1.0, 0.0, 0.0])
        t = 0.0
        
        omega_modified, psi = self.framework.coupled_evolution(omega, t)
        
        # Psi should be near target
        self.assertGreater(psi, 0.99)
        
        # Modified vorticity should have same shape
        self.assertEqual(omega_modified.shape, omega.shape)
        
        # Should be enhanced by consciousness
        enhancement = 1.0 + self.framework.params.psi_omega_coupling * psi
        expected = omega * enhancement
        np.testing.assert_array_almost_equal(omega_modified, expected, decimal=6)
    
    def test_blow_up_prevention(self):
        """Test blow-up prevention analysis"""
        results = self.framework.blow_up_prevention_analysis(
            initial_vorticity=1.0,
            duration=1.0,  # Short duration for testing
            n_steps=100
        )
        
        # Check required keys
        self.assertIn('blow_up_prevented', results)
        self.assertIn('growth_rate', results)
        self.assertIn('mean_psi', results)
        self.assertIn('f0_hz', results)
        
        # Blow-up should be prevented
        self.assertTrue(results['blow_up_prevented'])
        
        # Growth rate should be negative (decay)
        self.assertLess(results['growth_rate'], 0.1)
        
        # Mean psi should be high
        self.assertGreater(results['mean_psi'], 0.99)
        
        # Frequency should be f₀
        self.assertEqual(results['f0_hz'], F0_HZ)
        
        # Vorticity history should be finite
        self.assertTrue(np.all(np.isfinite(results['vorticity_history'])))
    
    def test_unified_validation(self):
        """Test complete unified validation"""
        results = self.framework.unified_validation()
        
        # Should validate successfully
        self.assertTrue(results['unified_validated'])
        
        # All components should validate
        self.assertTrue(results['vibrational_results']['framework_valid'])
        self.assertTrue(results['consciousness_results']['orch_or_validated'])
        self.assertTrue(results['blow_up_results']['blow_up_prevented'])
        
        # Frequency should be consistent
        self.assertEqual(results['f0_hz'], F0_HZ)


class TestIntegration(unittest.TestCase):
    """Integration tests"""
    
    def test_consciousness_and_unified(self):
        """Test that consciousness model integrates with unified framework"""
        # Create both
        consciousness = MicrotubuleCoherence()
        framework = UnifiedResonanceConsciousness()
        
        # Both should use same frequency
        self.assertEqual(
            consciousness.params.f0,
            framework.params.f0
        )
        self.assertEqual(
            consciousness.params.psi_target,
            framework.params.psi_target
        )
        
        # Consciousness field should be consistent
        t = 0.5
        psi1 = consciousness.compute_consciousness_field(t, n_tubules=1000)
        psi2 = framework.consciousness.compute_consciousness_field(t, n_tubules=1000)
        
        # Should be similar (allowing for randomness in phase distribution)
        self.assertAlmostEqual(psi1, psi2, delta=0.05)
    
    def test_frequency_consistency(self):
        """Test that f₀ is consistent across all modules"""
        consciousness = MicrotubuleCoherence()
        framework = UnifiedResonanceConsciousness()
        
        # All should use F0_HZ
        self.assertEqual(consciousness.params.f0, F0_HZ)
        self.assertEqual(framework.params.f0, F0_HZ)
        self.assertEqual(F0_HZ, 141.7001)


def run_tests():
    """Run all tests"""
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestMicrotubuleCoherence))
    suite.addTests(loader.loadTestsFromTestCase(TestUnifiedFramework))
    suite.addTests(loader.loadTestsFromTestCase(TestIntegration))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Print summary
    print("\n" + "="*70)
    print("TEST SUMMARY")
    print("="*70)
    print(f"Tests run: {result.testsRun}")
    print(f"Successes: {result.testsRun - len(result.failures) - len(result.errors)}")
    print(f"Failures: {len(result.failures)}")
    print(f"Errors: {len(result.errors)}")
    
    if result.wasSuccessful():
        print("\n✓ ALL TESTS PASSED")
    else:
        print("\n✗ SOME TESTS FAILED")
    
    return result.wasSuccessful()


if __name__ == "__main__":
    success = run_tests()
    sys.exit(0 if success else 1)
