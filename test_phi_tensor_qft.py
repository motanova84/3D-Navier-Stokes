#!/usr/bin/env python3
"""
Test suite for QFT-based Φ_ij tensor derivation and DNS validation scripts.

Tests basic functionality and numerical outputs.
"""

import unittest
import numpy as np
import os
import sys

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

# Import test modules
from validate_phi_coupling_DNS import (
    PhiTensorCoupling,
    NavierStokesExtendedDNS,
    detect_resonance_frequency
)


class TestPhiTensorCoupling(unittest.TestCase):
    """Test PhiTensorCoupling class."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.phi_coupling = PhiTensorCoupling(f0=141.7001)
    
    def test_initialization(self):
        """Test proper initialization of PhiTensorCoupling."""
        self.assertAlmostEqual(self.phi_coupling.f0, 141.7001)
        self.assertAlmostEqual(
            self.phi_coupling.omega0, 
            2 * np.pi * 141.7001, 
            places=4
        )
        
    def test_coefficients(self):
        """Test Seeley-DeWitt coefficients are computed correctly."""
        # Check a1 coefficient
        expected_a1 = 1 / (720 * np.pi**2)
        self.assertAlmostEqual(self.phi_coupling.a1, expected_a1, places=8)
        
        # Check a2 coefficient
        expected_a2 = 1 / (2880 * np.pi**2)
        self.assertAlmostEqual(self.phi_coupling.a2, expected_a2, places=8)
        
        # Check a3 coefficient
        expected_a3 = -1 / (1440 * np.pi**2)
        self.assertAlmostEqual(self.phi_coupling.a3, expected_a3, places=8)
    
    def test_compute_psi(self):
        """Test field Ψ computation."""
        t = 0.0
        psi = self.phi_coupling.compute_psi(t)
        # At t=0, cos(0) = 1
        self.assertAlmostEqual(psi, self.phi_coupling.A_psi, places=8)
        
        # At t = π/(2ω₀), cos(π/2) = 0
        t_zero = np.pi / (2 * self.phi_coupling.omega0)
        psi_zero = self.phi_coupling.compute_psi(t_zero)
        self.assertAlmostEqual(psi_zero, 0.0, places=6)
    
    def test_compute_phi_tensor(self):
        """Test tensor computation."""
        N = 8
        u = np.random.randn(3, N, N, N) * 0.1
        t = 0.0
        dx = 1.0
        
        coupling = self.phi_coupling.compute_phi_tensor(u, t, dx)
        
        # Check shape
        self.assertEqual(coupling.shape, (3, N, N, N))
        
        # Check that it's finite
        self.assertTrue(np.all(np.isfinite(coupling)))
        
        # Check that coupling is proportional to u (simplified model)
        # ratio should be constant across components
        for i in range(3):
            ratio = coupling[i] / (u[i] + 1e-10)
            # All ratios should be similar (within tolerance)
            self.assertTrue(np.std(ratio) / (np.mean(np.abs(ratio)) + 1e-10) < 0.1)


class TestNavierStokesExtendedDNS(unittest.TestCase):
    """Test NavierStokesExtendedDNS class."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.solver = NavierStokesExtendedDNS(
            N=8,
            L=2*np.pi,
            nu=1e-2,
            dt=1e-3
        )
    
    def test_initialization(self):
        """Test proper initialization of DNS solver."""
        self.assertEqual(self.solver.N, 8)
        self.assertEqual(self.solver.L, 2*np.pi)
        self.assertAlmostEqual(self.solver.nu, 1e-2)
        self.assertAlmostEqual(self.solver.dt, 1e-3)
    
    def test_initialize_turbulent_field(self):
        """Test turbulent field initialization."""
        u = self.solver.initialize_turbulent_field(u0_rms=0.1)
        
        # Check shape
        self.assertEqual(u.shape, (3, 8, 8, 8))
        
        # Check that field is finite and reasonable
        self.assertTrue(np.all(np.isfinite(u)))
        
        # Check RMS is approximately correct (within factor of 2)
        u_rms = np.sqrt(np.mean(u**2))
        self.assertLess(u_rms, 0.3)  # Should be close to 0.1
        self.assertGreater(u_rms, 0.01)  # Should not be too small
    
    def test_project_divergence_free(self):
        """Test divergence-free projection doesn't fail."""
        N = self.solver.N
        u_hat = np.random.randn(3, N, N, N) + 1j * np.random.randn(3, N, N, N)
        
        u_proj = self.solver.project_divergence_free(u_hat)
        
        # Check shape preserved
        self.assertEqual(u_proj.shape, u_hat.shape)
        
        # Check result is finite
        self.assertTrue(np.all(np.isfinite(u_proj)))
    
    def test_compute_energy(self):
        """Test energy computation."""
        N = self.solver.N
        u = np.ones((3, N, N, N)) * 0.1
        
        E = self.solver.compute_energy(u)
        
        # Energy should be positive
        self.assertGreater(E, 0)
        
        # Energy should scale with u²
        u2 = u * 2
        E2 = self.solver.compute_energy(u2)
        self.assertAlmostEqual(E2 / E, 4.0, places=1)


class TestResonanceDetection(unittest.TestCase):
    """Test resonance frequency detection."""
    
    def test_detect_simple_frequency(self):
        """Test detection of a simple sinusoidal signal."""
        f_test = 10.0  # Hz
        dt = 0.001  # s
        T = 1.0  # s
        t = np.arange(0, T, dt)
        
        # Create signal with known frequency
        signal = np.sin(2 * np.pi * f_test * t) + 1.0
        
        results = detect_resonance_frequency(
            signal.tolist(),
            dt,
            expected_f0=f_test
        )
        
        # Should detect frequency close to f_test
        self.assertLess(results['relative_error'], 0.1)  # Within 10%
    
    def test_detect_with_noise(self):
        """Test detection with noisy signal."""
        f_test = 50.0  # Hz
        dt = 0.001  # s
        T = 2.0  # s
        t = np.arange(0, T, dt)
        
        # Create signal with noise
        signal = np.sin(2 * np.pi * f_test * t) + 1.0 + 0.1 * np.random.randn(len(t))
        
        results = detect_resonance_frequency(
            signal.tolist(),
            dt,
            expected_f0=f_test
        )
        
        # Should still detect frequency reasonably well
        self.assertLess(results['relative_error'], 0.2)  # Within 20%


class TestQFTDerivationScript(unittest.TestCase):
    """Test QFT derivation script can run and generate files."""
    
    def test_script_runs(self):
        """Test that derive_phi_tensor_qft_rigorous.py runs successfully."""
        import subprocess
        
        result = subprocess.run(
            ['python', 'derive_phi_tensor_qft_rigorous.py'],
            capture_output=True,
            text=True,
            timeout=30
        )
        
        # Script should complete successfully
        self.assertEqual(result.returncode, 0)
        
        # Should generate LaTeX file
        self.assertTrue(os.path.exists('Results/Phi_tensor_QFT.tex'))
        
        # Should generate numerical summary
        self.assertTrue(os.path.exists('Results/Phi_tensor_numerical_summary.txt'))
    
    def test_latex_output_format(self):
        """Test LaTeX output has correct format."""
        tex_file = 'Results/Phi_tensor_QFT.tex'
        
        if os.path.exists(tex_file):
            with open(tex_file, 'r') as f:
                content = f.read()
            
            # Should contain key elements
            self.assertIn(r'\Phi_{ij}', content)
            self.assertIn(r'\alpha', content)
            self.assertIn(r'\beta', content)
            self.assertIn(r'\gamma', content)
            self.assertIn('141.7001', content)


def run_tests():
    """Run all tests."""
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add test classes
    suite.addTests(loader.loadTestsFromTestCase(TestPhiTensorCoupling))
    suite.addTests(loader.loadTestsFromTestCase(TestNavierStokesExtendedDNS))
    suite.addTests(loader.loadTestsFromTestCase(TestResonanceDetection))
    suite.addTests(loader.loadTestsFromTestCase(TestQFTDerivationScript))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    return result.wasSuccessful()


if __name__ == '__main__':
    success = run_tests()
    sys.exit(0 if success else 1)
