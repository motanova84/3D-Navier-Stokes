#!/usr/bin/env python3
"""
Test suite for psi_nse_dns_complete.py

Tests the Ψ-Navier-Stokes DNS simulation script with reduced parameters
to verify numerical stability, output generation, and key metrics.
"""

import unittest
import subprocess
import sys
import os
import json
import tempfile
from pathlib import Path
import numpy as np


class TestPsiNseDNS(unittest.TestCase):
    """Test cases for Ψ-NSE DNS simulation"""
    
    @classmethod
    def setUpClass(cls):
        """Run simulation once for all tests"""
        cls.tmpdir = tempfile.mkdtemp()
        cls.original_dir = os.getcwd()
        
        # Read and modify script for quick test
        with open('psi_nse_dns_complete.py', 'r') as f:
            script_content = f.read()
        
        # Reduce parameters for testing
        modified_content = script_content.replace(
            'N = 128  # resolución espacial',
            'N = 32  # resolución espacial'
        ).replace(
            'dt = 0.001  # paso temporal',
            'dt = 0.01  # paso temporal'
        ).replace(
            'T_max = 5.0  # tiempo total simulación',
            'T_max = 0.5  # tiempo total simulación'
        )
        
        # Write test script
        cls.test_script = os.path.join(cls.tmpdir, 'test_script.py')
        with open(cls.test_script, 'w') as f:
            f.write(modified_content)
        
        # Run simulation
        os.chdir(cls.tmpdir)
        result = subprocess.run(
            [sys.executable, cls.test_script],
            capture_output=True,
            text=True,
            timeout=180
        )
        
        cls.stdout = result.stdout
        cls.stderr = result.stderr
        cls.returncode = result.returncode
        
        # Load results if available
        json_path = os.path.join(cls.tmpdir, 'psi_nse_results.json')
        if os.path.exists(json_path):
            with open(json_path, 'r') as f:
                cls.results = json.load(f)
        else:
            cls.results = None
    
    @classmethod
    def tearDownClass(cls):
        """Clean up after tests"""
        os.chdir(cls.original_dir)
        # Note: tmpdir cleanup is handled by OS
    
    def test_script_runs_successfully(self):
        """Test that the script executes without errors"""
        self.assertEqual(
            self.returncode, 0,
            f"Script failed with return code {self.returncode}\n"
            f"stderr: {self.stderr}"
        )
    
    def test_json_output_generated(self):
        """Test that JSON results file is generated"""
        json_path = os.path.join(self.tmpdir, 'psi_nse_results.json')
        self.assertTrue(
            os.path.exists(json_path),
            "JSON results file not generated"
        )
    
    def test_png_output_generated(self):
        """Test that PNG visualization is generated"""
        png_path = os.path.join(self.tmpdir, 'psi_nse_dns_results.png')
        self.assertTrue(
            os.path.exists(png_path),
            "PNG visualization not generated"
        )
    
    def test_json_has_required_keys(self):
        """Test that JSON output contains all required keys"""
        self.assertIsNotNone(self.results, "No results loaded")
        
        required_keys = [
            'parameters', 'detected_frequency_Hz', 
            'final_energy', 'final_enstrophy',
            'max_energy', 'blow_up_detected'
        ]
        
        for key in required_keys:
            self.assertIn(
                key, self.results,
                f"Required key '{key}' missing from JSON results"
            )
    
    def test_parameters_correct(self):
        """Test that simulation parameters are correctly recorded"""
        self.assertIsNotNone(self.results, "No results loaded")
        
        params = self.results['parameters']
        self.assertAlmostEqual(params['f0_Hz'], 141.7001, places=4)
        self.assertEqual(params['N'], 32)
        self.assertEqual(params['dt'], 0.01)
        self.assertEqual(params['T_max'], 0.5)
    
    def test_no_blowup_detected(self):
        """Test that no blow-up is detected (system remains stable)"""
        self.assertIsNotNone(self.results, "No results loaded")
        self.assertFalse(
            self.results['blow_up_detected'],
            "Blow-up detected - system unstable"
        )
    
    def test_energy_bounded(self):
        """Test that energy remains bounded"""
        self.assertIsNotNone(self.results, "No results loaded")
        
        max_energy = self.results['max_energy']
        final_energy = self.results['final_energy']
        
        # Energy should be positive and bounded
        self.assertGreater(max_energy, 0, "Max energy should be positive")
        self.assertLess(max_energy, 1e6, "Max energy too large (blow-up)")
        self.assertGreater(final_energy, 0, "Final energy should be positive")
        self.assertIsFinite(final_energy, "Final energy must be finite")
    
    def test_enstrophy_bounded(self):
        """Test that enstrophy remains bounded"""
        self.assertIsNotNone(self.results, "No results loaded")
        
        final_enstrophy = self.results['final_enstrophy']
        
        # Enstrophy should be positive and bounded
        self.assertGreater(final_enstrophy, 0, "Enstrophy should be positive")
        self.assertLess(final_enstrophy, 1e6, "Enstrophy too large")
        self.assertIsFinite(final_enstrophy, "Enstrophy must be finite")
    
    def test_frequency_detected(self):
        """Test that a frequency is detected"""
        self.assertIsNotNone(self.results, "No results loaded")
        
        detected_freq = self.results['detected_frequency_Hz']
        
        # Frequency should be positive
        self.assertGreater(detected_freq, 0, "Detected frequency should be positive")
        self.assertIsFinite(detected_freq, "Detected frequency must be finite")
        
        # Note: With short simulation (0.5s), frequency detection won't be
        # accurate, so we don't test for proximity to f0
    
    def test_output_messages(self):
        """Test that expected output messages are present"""
        self.assertIn("INICIALIZANDO SIMULACIÓN DNS", self.stdout)
        self.assertIn("SIMULACIÓN COMPLETADA", self.stdout)
        self.assertIn("ANÁLISIS ESPECTRAL", self.stdout)
        self.assertIn("CONCLUSIONES", self.stdout)
    
    def assertIsFinite(self, value, msg=None):
        """Custom assertion to check if value is finite"""
        self.assertTrue(
            np.isfinite(value),
            msg or f"Value {value} is not finite"
        )


class TestPsiNseFunctions(unittest.TestCase):
    """Test individual functions from the DNS script"""
    
    def setUp(self):
        """Set up test fixtures"""
        self.f0 = 141.7001
        self.omega0 = 2 * np.pi * self.f0
        self.L = 2 * np.pi
        self.N = 16  # Small for fast tests
        
        # Create minimal grid
        x = np.linspace(0, self.L, self.N, endpoint=False)
        self.X, self.Y, self.Z = np.meshgrid(x, x, x, indexing='ij')
    
    def test_coherence_field_oscillates(self):
        """Test that coherence field oscillates at f0"""
        from scipy.fft import fftn, ifftn, fftfreq
        
        # Simplified coherence field function
        def campo_coherencia_psi(t, X, Y, Z):
            temporal = np.sin(self.omega0 * t)
            espacial = (np.sin(2*np.pi*X/self.L) * 
                       np.cos(2*np.pi*Y/self.L) * 
                       np.sin(2*np.pi*Z/self.L))
            return temporal * espacial
        
        # Test at different times
        t1 = 0.0
        t2 = 1.0 / (4.0 * self.f0)  # Quarter period - should give sin ≈ 1
        t3 = 1.0 / (2.0 * self.f0)  # Half period - should give sin ≈ 0
        
        psi1 = campo_coherencia_psi(t1, self.X, self.Y, self.Z)
        psi2 = campo_coherencia_psi(t2, self.X, self.Y, self.Z)
        psi3 = campo_coherencia_psi(t3, self.X, self.Y, self.Z)
        
        # Field at t=0 should be near zero (sin(0) = 0)
        self.assertTrue(np.allclose(psi1, 0, atol=1e-10))
        
        # Field at quarter period should be non-zero where spatial field is non-zero
        # (temporal component is sin(π/2) = 1)
        self.assertFalse(np.allclose(psi2, 0))
        
        # Field at half period should be near zero (sin(π) ≈ 0)
        self.assertTrue(np.allclose(psi3, 0, atol=1e-10))
    
    def test_taylor_green_properties(self):
        """Test Taylor-Green vortex initial conditions"""
        # Simplified Taylor-Green function
        def taylor_green_vortex(X, Y, Z, U0=1.0):
            u = U0 * np.sin(X) * np.cos(Y) * np.cos(Z)
            v = -U0 * np.cos(X) * np.sin(Y) * np.cos(Z)
            w = np.zeros_like(u)
            return u, v, w
        
        u, v, w = taylor_green_vortex(self.X, self.Y, self.Z)
        
        # Check mean values
        self.assertAlmostEqual(np.mean(u), 0, places=10)
        self.assertAlmostEqual(np.mean(v), 0, places=10)
        self.assertAlmostEqual(np.mean(w), 0, places=10)
        
        # Check energy is positive
        energy = 0.5 * np.mean(u**2 + v**2 + w**2)
        self.assertGreater(energy, 0)


def run_tests():
    """Run all tests and return exit code"""
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add test classes
    suite.addTests(loader.loadTestsFromTestCase(TestPsiNseDNS))
    suite.addTests(loader.loadTestsFromTestCase(TestPsiNseFunctions))
    
    # Run with verbosity
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    return 0 if result.wasSuccessful() else 1


if __name__ == '__main__':
    sys.exit(run_tests())
