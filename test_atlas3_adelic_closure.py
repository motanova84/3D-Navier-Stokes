#!/usr/bin/env python3
"""
Tests for Atlas³ Adelic Closure Framework
==========================================

Comprehensive test suite for verifying:
1. Vladimirov Laplacian spectral properties
2. Exponential remainder decay
3. Hadamard factorization
4. Ξ = ξ identity
5. ABC coherence constraints
6. Self-adjointness of operator L

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
Date: February 14, 2026
"""

import unittest
import numpy as np
from atlas3_adelic_closure import (
    AdelicParameters,
    VladimirovLaplacian,
    AdelicViscosityOperator,
    FredholmDeterminant,
    HadamardFactorization,
    Atlas3Closure,
    verify_atlas3_closure,
    F0_HZ,
    QCAL_SEAL,
    PSI_TARGET,
)


class TestVladimirovLaplacian(unittest.TestCase):
    """Test Vladimirov p-adic Laplacian"""
    
    def test_initialization(self):
        """Test Vladimirov Laplacian initialization"""
        lap = VladimirovLaplacian(prime=2)
        self.assertEqual(lap.p, 2)
        self.assertAlmostEqual(lap.lambda_1, np.log(2), places=6)
    
    def test_spectral_gap_positive(self):
        """Test that spectral gap is positive for all primes"""
        primes = [2, 3, 5, 7, 11, 13, 17]
        for p in primes:
            lap = VladimirovLaplacian(prime=p)
            gap = lap.spectral_gap()
            self.assertGreater(gap, 0, f"Spectral gap should be positive for p={p}")
            self.assertAlmostEqual(gap, np.log(p), places=6)
    
    def test_heat_kernel_decay(self):
        """Test exponential decay of p-adic heat kernel"""
        lap = VladimirovLaplacian(prime=2)
        
        # Heat kernel should decay exponentially
        t_values = [0.1, 1.0, 5.0, 10.0]
        for i in range(len(t_values) - 1):
            t1, t2 = t_values[i], t_values[i + 1]
            k1 = lap.heat_kernel(t1)
            k2 = lap.heat_kernel(t2)
            self.assertGreater(k1, k2, "Heat kernel should decay with time")
    
    def test_heat_kernel_initial_value(self):
        """Test heat kernel at t=0"""
        lap = VladimirovLaplacian(prime=2)
        k_0 = lap.heat_kernel(0.0)
        self.assertAlmostEqual(k_0, 1.0, places=10)
    
    def test_eigenvalue_growth(self):
        """Test eigenvalue growth is linear in n"""
        lap = VladimirovLaplacian(prime=3)
        
        # λₙ should grow linearly with n
        for n in range(1, 10):
            lambda_n = lap.eigenvalue(n)
            expected = n * np.log(3)
            self.assertAlmostEqual(lambda_n, expected, places=6)


class TestAdelicParameters(unittest.TestCase):
    """Test Adelic parameters configuration"""
    
    def test_default_parameters(self):
        """Test default parameter values"""
        params = AdelicParameters()
        
        self.assertEqual(params.nu, 1.0)
        self.assertIsInstance(params.lambda_p_gaps, dict)
        self.assertIn(2, params.lambda_p_gaps)
        self.assertIn(17, params.lambda_p_gaps)  # QCAL resonance prime
    
    def test_min_gap_computation(self):
        """Test minimum gap computation"""
        params = AdelicParameters()
        min_gap = params.get_min_gap()
        
        # Minimum should be from p=2
        expected_min = np.log(2)
        self.assertAlmostEqual(min_gap, expected_min, places=2)
    
    def test_qcal_prime_17_present(self):
        """Test that QCAL resonance prime p=17 is included"""
        params = AdelicParameters()
        self.assertIn(17, params.lambda_p_gaps)
        
        # Gap should be ln(17)
        expected_gap = np.log(17)
        self.assertAlmostEqual(params.lambda_p_gaps[17], expected_gap, places=2)


class TestAdelicViscosityOperator(unittest.TestCase):
    """Test Adelic viscosity operator"""
    
    def test_initialization(self):
        """Test operator initialization"""
        params = AdelicParameters()
        op = AdelicViscosityOperator(params)
        
        self.assertEqual(op.params, params)
        self.assertIsInstance(op.laplacians, dict)
        self.assertGreater(len(op.laplacians), 0)
    
    def test_remainder_bound_decay(self):
        """Test exponential decay of remainder bound"""
        params = AdelicParameters(nu=1.0)
        op = AdelicViscosityOperator(params)
        
        # Remainder should decay exponentially
        t_values = [0.1, 1.0, 5.0, 10.0, 20.0]
        remainders = [op.compute_remainder_bound(t) for t in t_values]
        
        # Check monotonic decay
        for i in range(len(remainders) - 1):
            self.assertGreater(remainders[i], remainders[i + 1],
                             "Remainder should decay monotonically")
    
    def test_remainder_bound_positive(self):
        """Test that remainder bound is always positive"""
        params = AdelicParameters()
        op = AdelicViscosityOperator(params)
        
        for t in [0.1, 1.0, 5.0, 10.0]:
            r = op.compute_remainder_bound(t)
            self.assertGreater(r, 0, "Remainder bound should be positive")
    
    def test_remainder_bound_infinity_at_zero(self):
        """Test that remainder is infinite at t=0"""
        params = AdelicParameters()
        op = AdelicViscosityOperator(params)
        
        r = op.compute_remainder_bound(0.0)
        self.assertTrue(np.isinf(r) or r > 1e10)
    
    def test_self_adjointness_positive_viscosity(self):
        """Test self-adjointness for ν > 0"""
        params = AdelicParameters(nu=1.0)
        op = AdelicViscosityOperator(params)
        
        self.assertTrue(op.is_essentially_selfadjoint())
        self.assertTrue(op.spectrum_is_real())
    
    def test_self_adjointness_zero_viscosity(self):
        """Test that ν = 0 fails self-adjointness"""
        params = AdelicParameters(nu=0.0)
        op = AdelicViscosityOperator(params)
        
        self.assertFalse(op.is_essentially_selfadjoint())
    
    def test_closure_verification(self):
        """Test closure verification at large t"""
        params = AdelicParameters(nu=1.0)
        op = AdelicViscosityOperator(params)
        
        # At t=10, remainder should be negligible
        is_closed = op.verify_closure(t=10.0, epsilon=1e-3)
        self.assertTrue(is_closed, "Remainder should be negligible at t=10")


class TestFredholmDeterminant(unittest.TestCase):
    """Test Fredholm determinant"""
    
    def test_initialization_default_zeros(self):
        """Test initialization with default zeros"""
        fd = FredholmDeterminant()
        
        self.assertIsInstance(fd.zeros, list)
        self.assertGreater(len(fd.zeros), 0)
        
        # First zero should be approximately 14.13
        self.assertAlmostEqual(fd.zeros[0], 14.134725, places=3)
    
    def test_initialization_custom_zeros(self):
        """Test initialization with custom zeros"""
        custom_zeros = [10.0, 20.0, 30.0]
        fd = FredholmDeterminant(zeros=custom_zeros)
        
        self.assertEqual(fd.zeros, custom_zeros)
    
    def test_evaluate_at_zero(self):
        """Test Ξ(0) = 1 (normalization)"""
        fd = FredholmDeterminant()
        xi_0 = fd.evaluate(0.0)
        
        self.assertAlmostEqual(xi_0, 1.0, places=10)
    
    def test_evaluate_symmetry(self):
        """Test Ξ(-t) = Ξ(t) (even function)"""
        fd = FredholmDeterminant()
        
        for t in [1.0, 5.0, 10.0]:
            xi_pos = fd.evaluate(t)
            xi_neg = fd.evaluate(-t)
            self.assertAlmostEqual(xi_pos, xi_neg, places=10,
                                 msg=f"Ξ should be even at t={t}")
    
    def test_evaluate_at_zeros(self):
        """Test that Ξ(γₙ) = 0 at zeros"""
        fd = FredholmDeterminant()
        
        # At first zero, product should be very small
        gamma_1 = fd.zeros[0]
        xi_gamma1 = fd.evaluate(gamma_1, n_terms=1)
        
        self.assertAlmostEqual(xi_gamma1, 0.0, places=10)
    
    def test_log_derivative_at_zero(self):
        """Test logarithmic derivative at t=0"""
        fd = FredholmDeterminant()
        
        # At t=0, log derivative should be 0 by symmetry
        log_deriv = fd.log_derivative(0.0)
        self.assertAlmostEqual(log_deriv, 0.0, places=10)


class TestHadamardFactorization(unittest.TestCase):
    """Test Hadamard factorization"""
    
    def test_initialization(self):
        """Test Hadamard factorization initialization"""
        zeros = [1j * 14.13, 1j * 21.02]
        params = AdelicParameters()
        hf = HadamardFactorization(zeros, params)
        
        self.assertEqual(hf.zeros, zeros)
        self.assertEqual(hf.A, 0.0)  # Forced to 0 by ABC
        self.assertEqual(hf.B, 0.0)
    
    def test_abc_coherence_satisfied(self):
        """Test ABC coherence lemma is satisfied"""
        zeros = [1j * 14.13, 1j * 21.02]
        params = AdelicParameters()
        hf = HadamardFactorization(zeros, params)
        
        # A = 0 should satisfy ABC coherence
        self.assertTrue(hf.verify_abc_coherence())
    
    def test_abc_coherence_violated(self):
        """Test ABC coherence violation detection"""
        zeros = [1j * 14.13]
        params = AdelicParameters(abc_growth_bound=0.1)
        hf = HadamardFactorization(zeros, params)
        
        # Set A beyond bound
        hf.A = 1.0
        self.assertFalse(hf.verify_abc_coherence())
    
    def test_berry_phase_bounded(self):
        """Test Berry phase is bounded when A=0"""
        zeros = [1j * 14.13]
        params = AdelicParameters()
        hf = HadamardFactorization(zeros, params)
        
        # Berry phase should be 0 for all t when A=0
        for t in [1.0, 10.0, 100.0]:
            phase = hf.berry_phase(t)
            self.assertAlmostEqual(phase, 0.0, places=10)
    
    def test_order_one_verification(self):
        """Test order 1 growth verification"""
        zeros = [1j * 14.13]
        params = AdelicParameters()
        hf = HadamardFactorization(zeros, params)
        
        test_points = [1.0, 10.0, 100.0]
        self.assertTrue(hf.verify_order_one(test_points))


class TestAtlas3Closure(unittest.TestCase):
    """Test complete Atlas³ closure framework"""
    
    def test_initialization(self):
        """Test Atlas³ closure initialization"""
        closure = Atlas3Closure()
        
        self.assertIsInstance(closure.params, AdelicParameters)
        self.assertIsInstance(closure.operator, AdelicViscosityOperator)
        self.assertIsInstance(closure.fredholm, FredholmDeterminant)
        self.assertIsInstance(closure.hadamard, HadamardFactorization)
    
    def test_verify_remainder_closure(self):
        """Test remainder closure verification"""
        closure = Atlas3Closure()
        result = closure.verify_remainder_closure(t=10.0)
        
        self.assertIn("status", result)
        self.assertIn("remainder_value", result)
        self.assertIn("is_negligible", result)
        self.assertGreater(result["decay_rate"], 0)
        
        # At t=10 with default params, should be closed
        self.assertEqual(result["status"], "CERRADO")
    
    def test_verify_xi_identity(self):
        """Test Ξ = ξ identity verification"""
        closure = Atlas3Closure()
        result = closure.verify_xi_identity()
        
        self.assertIn("status", result)
        self.assertIn("is_normalized", result)
        self.assertIn("abc_coherence", result)
        self.assertIn("test_points", result)
        
        # Should be normalized at t=0
        self.assertTrue(result["is_normalized"])
        
        # ABC coherence should be satisfied
        self.assertTrue(result["abc_coherence"])
    
    def test_verify_self_adjointness(self):
        """Test self-adjointness verification"""
        closure = Atlas3Closure()
        result = closure.verify_self_adjointness()
        
        self.assertIn("status", result)
        self.assertIn("is_selfadjoint", result)
        self.assertIn("spectrum_real", result)
        
        # Should be self-adjoint with ν > 0
        self.assertTrue(result["is_selfadjoint"])
        self.assertTrue(result["spectrum_real"])
        self.assertEqual(result["status"], "CERRADO")
    
    def test_compute_closure_certificate(self):
        """Test complete closure certificate generation"""
        closure = Atlas3Closure()
        cert = closure.compute_closure_certificate()
        
        # Check certificate structure
        self.assertIn("framework", cert)
        self.assertIn("psi_coherence", cert)
        self.assertIn("is_complete", cert)
        self.assertIn("frequency", cert)
        self.assertIn("seal", cert)
        self.assertIn("closure_table", cert)
        
        # Check QCAL constants
        self.assertEqual(cert["frequency"], F0_HZ)
        self.assertEqual(cert["seal"], QCAL_SEAL)
        
        # Check Ψ coherence
        self.assertGreaterEqual(cert["psi_coherence"], 0.0)
        self.assertLessEqual(cert["psi_coherence"], 1.0)
        
        # With default params, should achieve complete closure
        self.assertGreaterEqual(cert["psi_coherence"], 0.999)
        self.assertTrue(cert["is_complete"])
    
    def test_closure_table_structure(self):
        """Test closure table structure"""
        closure = Atlas3Closure()
        cert = closure.compute_closure_certificate()
        
        table = cert["closure_table"]
        
        # Check all three modules are present
        self.assertIn("Resto R(t)", table)
        self.assertIn("Identidad con ξ", table)
        self.assertIn("Auto-adjunción", table)
        
        # Each module should have obstacle, solution, status
        for module, info in table.items():
            self.assertIn("obstacle", info)
            self.assertIn("solution", info)
            self.assertIn("status", info)
            self.assertIn(info["status"], ["CERRADO", "ABIERTO"])
    
    def test_all_flanks_closed(self):
        """Test that all flanks are closed"""
        closure = Atlas3Closure()
        cert = closure.compute_closure_certificate()
        
        table = cert["closure_table"]
        
        # All three should be CERRADO
        for module, info in table.items():
            self.assertEqual(info["status"], "CERRADO",
                           f"Module {module} should be closed")
    
    def test_psi_target_achievement(self):
        """Test Ψ = 1.000000 achievement"""
        closure = Atlas3Closure()
        cert = closure.compute_closure_certificate()
        
        # Should achieve Ψ = 1.000000 (perfect coherence)
        self.assertAlmostEqual(cert["psi_coherence"], PSI_TARGET, places=6)


class TestConvenienceFunction(unittest.TestCase):
    """Test convenience verification function"""
    
    def test_verify_atlas3_closure(self):
        """Test quick verification function"""
        cert = verify_atlas3_closure(verbose=False)
        
        self.assertIsInstance(cert, dict)
        self.assertIn("psi_coherence", cert)
        self.assertTrue(cert["is_complete"])
    
    def test_verify_with_custom_viscosity(self):
        """Test verification with custom viscosity"""
        cert = verify_atlas3_closure(nu=2.0, verbose=False)
        
        # Higher viscosity should still give closure
        self.assertTrue(cert["is_complete"])
    
    def test_verify_with_custom_time(self):
        """Test verification with custom time parameter"""
        cert = verify_atlas3_closure(t_verification=20.0, verbose=False)
        
        # Longer time should still verify closure
        self.assertTrue(cert["is_complete"])


class TestQCALConstants(unittest.TestCase):
    """Test QCAL constant values"""
    
    def test_root_frequency(self):
        """Test QCAL root frequency value"""
        self.assertAlmostEqual(F0_HZ, 141.7001, places=4)
    
    def test_seal_format(self):
        """Test QCAL seal format"""
        self.assertEqual(QCAL_SEAL, "∴𓂀Ω∞³Φ")
    
    def test_psi_target(self):
        """Test Ψ target value"""
        self.assertAlmostEqual(PSI_TARGET, 1.000000, places=6)


class TestIntegration(unittest.TestCase):
    """Integration tests for complete workflow"""
    
    def test_complete_verification_workflow(self):
        """Test complete verification from start to finish"""
        # Create closure framework
        params = AdelicParameters(nu=1.0)
        closure = Atlas3Closure(params)
        
        # Verify each component
        remainder_ok = closure.verify_remainder_closure(t=10.0)
        xi_ok = closure.verify_xi_identity()
        selfadj_ok = closure.verify_self_adjointness()
        
        # All should be closed
        self.assertEqual(remainder_ok["status"], "CERRADO")
        self.assertEqual(xi_ok["status"], "CERRADO")
        self.assertEqual(selfadj_ok["status"], "CERRADO")
        
        # Generate certificate
        cert = closure.compute_closure_certificate()
        
        # Certificate should show complete closure
        self.assertTrue(cert["is_complete"])
        self.assertAlmostEqual(cert["psi_coherence"], 1.0, places=6)
    
    def test_viscosity_sensitivity(self):
        """Test sensitivity to viscosity parameter"""
        viscosities = [0.1, 0.5, 1.0, 2.0, 5.0]
        
        for nu in viscosities:
            with self.subTest(nu=nu):
                params = AdelicParameters(nu=nu)
                closure = Atlas3Closure(params)
                cert = closure.compute_closure_certificate()
                
                # All positive viscosities should give closure
                self.assertTrue(cert["is_complete"],
                              f"Should have closure for ν={nu}")


def run_tests():
    """Run all tests"""
    unittest.main(argv=[''], verbosity=2, exit=False)


if __name__ == "__main__":
    print("="*75)
    print("Atlas³ Adelic Closure Framework - Test Suite")
    print("="*75)
    print()
    
    run_tests()
