#!/usr/bin/env python3
"""
Test Suite for Vibrational Dual Regularization Framework
=========================================================

Tests for:
1. Vibrational regularization with f₀ = 141.7001 Hz
2. Riccati damping with γ ≥ 616
3. Dyadic dissociation and Serrin endpoint L⁵ₜL⁵ₓ
4. Noetic field Ψ coupling
"""

import unittest
import numpy as np
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from NavierStokes.vibrational_regularization import (
    VibrationalRegularization, VibrationalParameters
)
from NavierStokes.dyadic_serrin_endpoint import (
    DyadicSerrinAnalysis, SerrinEndpointParams
)
from NavierStokes.noetic_field_coupling import (
    NoeticFieldCoupling, NoeticFieldParams
)


class TestVibrationalRegularization(unittest.TestCase):
    """Test vibrational regularization framework"""
    
    def setUp(self):
        """Initialize test framework"""
        self.vr = VibrationalRegularization()
    
    def test_universal_frequency(self):
        """Test that universal frequency is correctly set"""
        self.assertAlmostEqual(self.vr.params.f0, 141.7001, places=4)
        self.assertAlmostEqual(self.vr.omega_0, 2 * np.pi * 141.7001, places=2)
    
    def test_critical_gamma_threshold(self):
        """Test critical Riccati damping threshold"""
        self.assertEqual(self.vr.params.gamma_critical, 616.0)
    
    def test_riccati_damping_equation(self):
        """Test Riccati damping equation"""
        E = 1.0
        t = 0.0
        gamma = 616.0
        C = 1.0
        
        dE_dt = self.vr.riccati_damping_equation(E, t, gamma, C)
        
        # Should be C - gamma*E^2 = 1 - 616*1 = -615
        expected = C - gamma * E**2
        self.assertAlmostEqual(dE_dt, expected, places=6)
    
    def test_riccati_energy_boundedness(self):
        """Test that energy remains bounded with γ ≥ 616"""
        t_span = np.linspace(0, 10, 100)
        E0 = 1.0
        gamma = self.vr.params.gamma_critical
        C = gamma * 0.01
        
        E = self.vr.solve_riccati_energy(E0, t_span, gamma, C)
        
        # Energy should remain finite
        self.assertTrue(np.all(np.isfinite(E)))
        
        # Energy should not explode
        self.assertLess(np.max(E), 100.0)
    
    def test_harmonic_damping(self):
        """Test harmonic damping at different frequencies"""
        k = np.array([0.1, 1.0, 10.0, 100.0])
        viscosity = 1e-3
        
        damping = self.vr.compute_harmonic_damping(k, viscosity)
        
        # Damping should be positive
        self.assertTrue(np.all(damping > 0))
        
        # Damping should increase with wavenumber
        self.assertTrue(np.all(np.diff(damping) > 0))
    
    def test_noetic_field_computation(self):
        """Test noetic field computation"""
        t = 0.0
        x = np.array([0.0, 0.0, 0.0])
        
        psi = self.vr.compute_noetic_field(x, t)
        
        # Should be Ψ₀ cos(0) = Ψ₀
        expected = self.vr.params.compute_psi()
        self.assertAlmostEqual(psi, expected, places=6)
    
    def test_serrin_endpoint_control(self):
        """Test Serrin endpoint control"""
        u_norms = np.ones(10) * 0.5
        t_norms = np.linspace(0, 1, 10)
        
        result = self.vr.serrin_endpoint_control(u_norms, t_norms)
        
        self.assertTrue(result['is_finite'])
        self.assertEqual(result['p'], 5.0)
        self.assertTrue(result['serrin_endpoint_achieved'])
    
    def test_framework_validation(self):
        """Test complete framework validation"""
        results = self.vr.validate_framework()
        
        self.assertEqual(results['vibrational_frequency'], 141.7001)
        self.assertEqual(results['gamma_critical'], 616.0)
        self.assertTrue(results['energy_bounded'])
        self.assertTrue(results['harmonic_damping_valid'])
        self.assertTrue(results['framework_valid'])


class TestDyadicSerrinAnalysis(unittest.TestCase):
    """Test dyadic dissociation and Serrin endpoint"""
    
    def setUp(self):
        """Initialize test framework"""
        self.dsa = DyadicSerrinAnalysis()
    
    def test_serrin_condition(self):
        """Test Serrin critical condition: 2/p + d/p = 1"""
        self.assertTrue(self.dsa.params.verify_serrin_condition())
        self.assertEqual(self.dsa.params.p_critical, 5.0)
        self.assertEqual(self.dsa.params.dimension, 3)
    
    def test_L5_norm_computation(self):
        """Test L⁵ norm computation"""
        # Simple test field
        u = np.ones((8, 8, 8))
        
        L5_norm = self.dsa.compute_dyadic_L5_norm(u)
        
        # For constant field of value 1, ||u||_L5 = (∫1^5 dx)^(1/5) = (volume)^(1/5)
        volume = 8**3
        expected = volume**(1/5)
        self.assertAlmostEqual(L5_norm, expected, places=1)
    
    def test_dyadic_projection(self):
        """Test Littlewood-Paley projection"""
        N = 16
        u_hat = np.random.randn(N, N, N) + 1j * np.random.randn(N, N, N)
        
        # Create wavenumber grid
        k = np.fft.fftfreq(N, d=1.0) * 2 * np.pi
        kx, ky, kz = np.meshgrid(k, k, k, indexing='ij')
        k_mag = np.sqrt(kx**2 + ky**2 + kz**2)
        
        # Project to low frequencies
        u_j = self.dsa.littlewood_paley_projection(u_hat, k_mag, j=-1)
        
        # Should zero out high frequencies
        mask = k_mag >= 1.0
        self.assertTrue(np.allclose(u_j[mask], 0.0))
    
    def test_bkm_integral(self):
        """Test BKM integral computation"""
        # Decaying vorticity
        t_grid = np.linspace(0, 10, 50)
        vorticity = np.exp(-0.1 * t_grid)
        
        result = self.dsa.compute_bkm_integral(vorticity, t_grid)
        
        self.assertTrue(result['is_finite'])
        self.assertTrue(result['no_blowup'])
        self.assertGreater(result['bkm_integral'], 0)
    
    def test_dyadic_energy_estimate(self):
        """Test dyadic energy estimates"""
        viscosity = 1e-3
        vorticity_norm = 1.0
        
        # Low frequency damping
        damping_low = self.dsa.dyadic_energy_estimate(-1, viscosity, vorticity_norm)
        self.assertGreater(damping_low, 0)
        
        # High frequency damping should be much stronger
        damping_high = self.dsa.dyadic_energy_estimate(5, viscosity, vorticity_norm)
        self.assertGreater(damping_high, damping_low * 10)
    
    def test_serrin_endpoint_verification(self):
        """Test Serrin endpoint verification"""
        # Generate bounded L5 norms
        t_grid = np.linspace(0, 10, 50)
        L5x_norms = np.exp(-0.1 * t_grid)
        
        result = self.dsa.verify_serrin_endpoint(L5x_norms, t_grid)
        
        self.assertTrue(result['is_finite'])
        self.assertTrue(result['serrin_condition_verified'])
        self.assertTrue(result['endpoint_achieved'])
        self.assertTrue(result['global_smoothness'])


class TestNoeticFieldCoupling(unittest.TestCase):
    """Test noetic field coupling"""
    
    def setUp(self):
        """Initialize test framework"""
        self.nfc = NoeticFieldCoupling()
    
    def test_noetic_parameters(self):
        """Test noetic field parameters"""
        self.assertEqual(self.nfc.params.f0, 141.7001)
        self.assertAlmostEqual(self.nfc.omega_0, 2 * np.pi * 141.7001, places=2)
        self.assertEqual(self.nfc.psi_0, self.nfc.params.I * self.nfc.params.A_eff**2)
    
    def test_noetic_field_oscillation(self):
        """Test noetic field oscillation"""
        t_values = np.linspace(0, 1.0, 1000)
        psi_values = [self.nfc.compute_noetic_field(t) for t in t_values]
        psi_array = np.array(psi_values)
        
        # Should oscillate between -Ψ₀ and +Ψ₀
        self.assertAlmostEqual(np.max(psi_array), self.nfc.psi_0, places=6)
        self.assertLessEqual(np.min(psi_array), -self.nfc.psi_0 * 0.99)  # Allow numerical tolerance
    
    def test_noetic_coupling_term(self):
        """Test noetic coupling term computation"""
        N = 8
        omega = np.random.randn(3, N, N, N) * 0.1
        psi = 1.0
        
        coupling = self.nfc.compute_noetic_coupling_term(omega, psi)
        
        # Should have same shape as vorticity
        self.assertEqual(coupling.shape, omega.shape)
        
        # Should be real
        self.assertTrue(np.all(np.isfinite(coupling)))
    
    def test_coherence_metric(self):
        """Test coherence metric computation"""
        N = 8
        omega = np.random.randn(3, N, N, N)
        strain = np.random.randn(3, N, N, N)
        
        coherence = self.nfc.compute_coherence_metric(omega, strain)
        
        # Coherence should be between 0 and 1
        self.assertGreaterEqual(coherence, 0.0)
        self.assertLessEqual(coherence, 1.0)
    
    def test_singularity_prevention(self):
        """Test singularity prevention analysis"""
        # Generate decaying vorticity (no blow-up)
        t_grid = np.linspace(0, 10, 50)
        N = 8
        
        omega_history = []
        for t in t_grid:
            omega = np.random.randn(3, N, N, N) * np.exp(-0.2 * t)
            omega_history.append(omega)
        
        result = self.nfc.analyze_singularity_prevention(omega_history, t_grid)
        
        # Should detect no blow-up
        self.assertTrue(result['blow_up_prevented'])
        self.assertLess(result['vorticity_growth_rate'], 0.1)
        self.assertTrue(result['noetic_effectiveness'])
    
    def test_framework_validation(self):
        """Test noetic framework validation"""
        results = self.nfc.validate_noetic_coupling()
        
        self.assertAlmostEqual(results['frequency_hz'], 141.7001, places=4)
        self.assertTrue(results['amplitude_correct'])
        self.assertTrue(results['framework_valid'])


class TestIntegratedFramework(unittest.TestCase):
    """Integration tests for complete framework"""
    
    def test_complete_pipeline(self):
        """Test complete vibrational regularization pipeline"""
        # Initialize all components
        vr = VibrationalRegularization()
        dsa = DyadicSerrinAnalysis()
        nfc = NoeticFieldCoupling()
        
        # All should use same frequency
        self.assertEqual(vr.params.f0, nfc.params.f0)
        self.assertEqual(vr.params.f0, 141.7001)
        
        # Generate synthetic flow
        t_grid = np.linspace(0, 5, 25)
        N = 16
        
        u_series = []
        omega_series = []
        
        for t in t_grid:
            psi = nfc.compute_noetic_field(t)
            decay = np.exp(-0.1 * t) * (1 + 0.1 * psi)
            
            x = np.linspace(0, 2*np.pi, N)
            X, Y, Z = np.meshgrid(x, x, x, indexing='ij')
            
            u = np.array([
                decay * np.sin(X) * np.cos(Y),
                decay * -np.cos(X) * np.sin(Y),
                decay * 0.5 * np.cos(X) * np.cos(Y)
            ])
            
            omega = np.array([
                decay * np.cos(X) * np.cos(Y),
                decay * np.sin(X) * np.sin(Y),
                decay * np.sin(X) * np.cos(Y)
            ])
            
            u_series.append(u)
            omega_series.append(omega)
        
        # Verify complete framework
        results = dsa.full_dyadic_serrin_verification(
            u_series, omega_series, t_grid, viscosity=1e-3
        )
        
        # Should achieve global regularity
        self.assertTrue(results['serrin_endpoint']['endpoint_achieved'])
        self.assertTrue(results['bkm_criterion']['no_blowup'])
        self.assertTrue(results['global_regularity'])


def run_tests():
    """Run all tests"""
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestVibrationalRegularization))
    suite.addTests(loader.loadTestsFromTestCase(TestDyadicSerrinAnalysis))
    suite.addTests(loader.loadTestsFromTestCase(TestNoeticFieldCoupling))
    suite.addTests(loader.loadTestsFromTestCase(TestIntegratedFramework))
    
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
