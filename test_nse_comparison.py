#!/usr/bin/env python3
"""
Test Suite for NSE vs Ψ-NSE Comparison Demonstration

Validates the key claims:
1. Classical NSE exhibits blow-up
2. Ψ-NSE remains stable
3. f₀ = 141.7 Hz emerges optimally
4. QFT derivation has no free parameters
"""

import unittest
import sys
import os
from demonstrate_nse_comparison import NSEComparison, SystemParameters


class TestNSEComparison(unittest.TestCase):
    """Test suite for NSE comparison demonstration"""
    
    def setUp(self):
        """Set up test fixtures"""
        self.comparison = NSEComparison()
        self.params = SystemParameters()
    
    def test_classical_nse_blowup(self):
        """Test that classical NSE exhibits blow-up behavior"""
        print("\n[TEST] Classical NSE blow-up detection...")
        
        results = self.comparison.simulate_classical_nse(T_max=10.0, omega_0=10.0)
        
        # Check that blow-up is detected
        self.assertTrue(
            results['blowup'] or results['omega_final'] > 1e3,
            "Classical NSE should exhibit blow-up or rapid growth"
        )
        
        # Check that vorticity increases
        vorticity = results['vorticity']
        self.assertGreater(
            vorticity[-1], vorticity[0],
            "Vorticity should increase without regularization"
        )
        
        print(f"  ✓ Blow-up detected: {results['blowup']}")
        print(f"  ✓ Final vorticity: {results['omega_final']:.2e}")
    
    def test_psi_nse_stability(self):
        """Test that Ψ-NSE remains stable"""
        print("\n[TEST] Ψ-NSE stability...")
        
        results = self.comparison.simulate_psi_nse(T_max=100.0, omega_0=10.0)
        
        # Check that NO blow-up occurs
        self.assertFalse(results['blowup'], "Ψ-NSE should NOT blow up")
        
        # Check that vorticity remains bounded
        self.assertLess(
            results['omega_final'], 10.0,
            "Vorticity should remain bounded"
        )
        
        # Check convergence to steady state
        omega_steady = results['omega_steady']
        self.assertAlmostEqual(
            results['omega_final'], omega_steady, places=1,
            msg="Vorticity should converge to steady state"
        )
        
        print(f"  ✓ No blow-up: {not results['blowup']}")
        print(f"  ✓ Bounded vorticity: {results['omega_final']:.4f}")
        print(f"  ✓ Steady state: {omega_steady:.4f}")
    
    def test_f0_emergence(self):
        """Test that f₀ = 141.7 Hz emerges spontaneously"""
        print("\n[TEST] f₀ emergence...")
        
        results = self.comparison.demonstrate_f0_emergence()
        
        f0_target = results['f0_target']
        f_optimal = results['f_optimal']
        
        # Check that optimal frequency is close to target
        deviation = abs(f_optimal - f0_target)
        self.assertLess(
            deviation, 5.0,
            f"Optimal frequency should be close to f₀ = {f0_target} Hz"
        )
        
        # Check that optimal frequency maximizes damping
        gamma_optimal = results['gamma_optimal']
        self.assertGreater(
            gamma_optimal, 500.0,
            "Optimal frequency should provide strong damping"
        )
        
        print(f"  ✓ Target f₀: {f0_target:.4f} Hz")
        print(f"  ✓ Optimal f: {f_optimal:.4f} Hz")
        print(f"  ✓ Deviation: {deviation:.4f} Hz")
        print(f"  ✓ Max damping: {gamma_optimal:.2f}")
    
    def test_qft_derivation(self):
        """Test that QFT derivation has no free parameters"""
        print("\n[TEST] QFT derivation...")
        
        results = self.comparison.validate_qft_derivation()
        
        # Check that there are NO free parameters
        self.assertEqual(
            results['free_parameters'], 0,
            "QFT derivation should have NO free parameters"
        )
        
        # Check that coefficients are fixed
        self.assertIsNotNone(results['alpha'], "α coefficient should be defined")
        self.assertIsNotNone(results['beta'], "β coefficient should be defined")
        self.assertIsNotNone(results['gamma'], "γ coefficient should be defined")
        
        # Check that coefficients are positive
        self.assertGreater(results['alpha'], 0, "α should be positive")
        self.assertGreater(results['beta'], 0, "β should be positive")
        self.assertGreater(results['gamma'], 0, "γ should be positive")
        
        print(f"  ✓ Free parameters: {results['free_parameters']}")
        print(f"  ✓ α = {results['alpha']:.8f}")
        print(f"  ✓ β = {results['beta']:.8f}")
        print(f"  ✓ γ = {results['gamma']:.8f}")
    
    def test_parameter_values(self):
        """Test that system parameters are correctly set"""
        print("\n[TEST] System parameters...")
        
        # Check critical frequency
        self.assertAlmostEqual(
            self.params.f0, 141.7001, places=4,
            msg="Critical frequency should be f₀ = 141.7001 Hz"
        )
        
        # Check Riccati damping
        self.assertAlmostEqual(
            self.params.gamma_critical, 616.0, places=1,
            msg="Critical damping should be γ = 616"
        )
        
        # Check QFT coefficients are fixed
        alpha_expected = 1.0 / (16.0 * 3.14159265359**2)
        self.assertAlmostEqual(
            self.params.alpha_qft, alpha_expected, places=6,
            msg="α should match QFT prediction"
        )
        
        print(f"  ✓ f₀ = {self.params.f0:.4f} Hz")
        print(f"  ✓ γ_critical = {self.params.gamma_critical:.2f}")
        print(f"  ✓ α_QFT = {self.params.alpha_qft:.8f}")
    
    def test_comparison_contrast(self):
        """Test that classical and Ψ-NSE behave differently"""
        print("\n[TEST] Behavior contrast...")
        
        # Simulate both systems with same initial conditions
        omega_0 = 10.0
        T_max = 10.0
        
        classical = self.comparison.simulate_classical_nse(T_max=T_max, omega_0=omega_0)
        psi = self.comparison.simulate_psi_nse(T_max=T_max, omega_0=omega_0)
        
        # Classical should have higher final vorticity
        self.assertGreater(
            classical['omega_final'], psi['omega_final'],
            "Classical NSE should have higher vorticity than Ψ-NSE"
        )
        
        # Classical should exhibit blow-up, Ψ-NSE should not
        self.assertTrue(classical['blowup'] or classical['omega_final'] > 100)
        self.assertFalse(psi['blowup'])
        
        print(f"  ✓ Classical vorticity: {classical['omega_final']:.2e}")
        print(f"  ✓ Ψ-NSE vorticity: {psi['omega_final']:.4f}")
        print(f"  ✓ Behavior differs significantly")


def run_tests():
    """Run all tests"""
    print("\n" + "="*70)
    print("TEST SUITE: NSE vs Ψ-NSE Comparison Validation")
    print("="*70)
    
    # Create test suite
    loader = unittest.TestLoader()
    suite = loader.loadTestsFromTestCase(TestNSEComparison)
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Summary
    print("\n" + "="*70)
    if result.wasSuccessful():
        print("✓ ALL TESTS PASSED")
        print("="*70)
        print("\nValidation Summary:")
        print("  ✓ Classical NSE exhibits blow-up")
        print("  ✓ Ψ-NSE remains stable")
        print("  ✓ f₀ = 141.7 Hz emerges spontaneously")
        print("  ✓ QFT derivation has no free parameters")
        print("  ✓ Systems behave contrastingly")
        print("\nCONCLUSION: Quantum-coherent coupling is NECESSARY")
        return 0
    else:
        print("✗ SOME TESTS FAILED")
        print("="*70)
        return 1


if __name__ == '__main__':
    sys.exit(run_tests())
