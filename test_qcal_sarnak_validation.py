#!/usr/bin/env python3
"""
Tests for QCAL-Sarnak validation module.
"""

import unittest
import numpy as np
from fractions import Fraction
from qcal_sarnak_validation import (
    ErdosUlamValidator, CoherentFunction, SarnakValidator
)


class TestErdosUlam(unittest.TestCase):
    """Test Erdős-Ulam construction."""
    
    def test_rational_points_distance_squared(self):
        """Test that distance squared between rational points is rational."""
        validator = ErdosUlamValidator()
        
        # Add some rational points
        validator.add_rational_point(Fraction(1, 2), Fraction(3, 4))
        validator.add_rational_point(Fraction(5, 6), Fraction(7, 8))
        validator.add_rational_point(Fraction(0, 1), Fraction(1, 1))
        
        # Verify all distances squared are rational
        self.assertTrue(validator.verify_all_distances_rational())
    
    def test_generate_lattice(self):
        """Test rational lattice generation."""
        validator = ErdosUlamValidator()
        count = validator.generate_rational_lattice(max_denominator=3)
        
        # Should generate multiple points
        self.assertGreater(count, 10)
        self.assertEqual(len(validator.points), count)
    
    def test_distance_calculation(self):
        """Test distance squared calculation."""
        validator = ErdosUlamValidator()
        
        p1 = (Fraction(0, 1), Fraction(0, 1))
        p2 = (Fraction(3, 1), Fraction(4, 1))
        
        d_sq = validator.distance_squared(p1, p2)
        
        # Distance squared should be 3² + 4² = 25
        self.assertEqual(d_sq, Fraction(25, 1))


class TestCoherentFunction(unittest.TestCase):
    """Test coherent function properties."""
    
    def test_coherent_wave(self):
        """Test that a pure frequency wave is coherent."""
        N = 1000
        f0 = 141.7001
        t = np.arange(N)
        wave = np.exp(2j * np.pi * f0 * t / N)
        
        f = CoherentFunction(wave)
        coherence = f.coherence()
        
        # Pure frequency should have high coherence
        self.assertGreater(coherence, 0.5)
    
    def test_noise_not_coherent(self):
        """Test that noise is not coherent."""
        N = 1000
        noise = np.random.randn(N) + 1j * np.random.randn(N)
        
        f = CoherentFunction(noise)
        coherence = f.coherence()
        
        # Noise should have low coherence
        self.assertLess(coherence, 0.3)
    
    def test_coherence_threshold(self):
        """Test coherence threshold."""
        f = CoherentFunction(np.ones(100))
        self.assertEqual(f.coherence_threshold, 0.888)


class TestSarnakPrinciple(unittest.TestCase):
    """Test QCAL-Sarnak orthogonality principle."""
    
    def test_moebius_function(self):
        """Test Möbius function calculation."""
        validator = SarnakValidator()
        
        # Test known values
        self.assertEqual(validator.moebius(1), 1)
        self.assertEqual(validator.moebius(2), -1)
        self.assertEqual(validator.moebius(3), -1)
        self.assertEqual(validator.moebius(4), 0)  # 4 = 2²
        self.assertEqual(validator.moebius(6), 1)   # 6 = 2·3
        self.assertEqual(validator.moebius(30), -1) # 30 = 2·3·5
    
    def test_orthogonality_coherent_wave(self):
        """Test orthogonality with coherent wave."""
        validator = SarnakValidator()
        
        # Create coherent wave
        N = 500
        t = np.arange(N)
        wave = np.exp(2j * np.pi * 141.7001 * t / N)
        
        f = CoherentFunction(wave)
        partial_sums = validator.test_orthogonality(f, N=N)
        
        # Check that later values are small
        late_values = [abs(s) for s in partial_sums[-50:]]
        avg_late = np.mean(late_values)
        
        # Should be decreasing toward zero
        self.assertLess(avg_late, 0.5)
    
    def test_convergence_check(self):
        """Test convergence detection."""
        validator = SarnakValidator()
        
        # Create sequence converging to zero
        converging = [1.0 / (n + 1) for n in range(1000)]
        self.assertTrue(
            validator.verify_convergence_to_zero(converging, tolerance=0.1)
        )
        
        # Create sequence not converging to zero
        not_converging = [1.0 + 0.1 * n for n in range(1000)]
        self.assertFalse(
            validator.verify_convergence_to_zero(not_converging, tolerance=0.1)
        )


class TestParameters(unittest.TestCase):
    """Test QCAL parameters."""
    
    def test_fundamental_frequency(self):
        """Test fundamental frequency value."""
        validator = SarnakValidator()
        self.assertAlmostEqual(validator.f0, 141.7001, places=4)
    
    def test_damping_coefficient(self):
        """Test damping coefficient."""
        validator = SarnakValidator()
        self.assertEqual(validator.gamma0, 888.0)


def run_tests():
    """Run all tests."""
    unittest.main(argv=[''], verbosity=2, exit=False)


if __name__ == '__main__':
    run_tests()
