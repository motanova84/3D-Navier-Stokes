#!/usr/bin/env python3
"""
Test suite for QFT Φ_ij(Ψ) tensor derivation script.

This test validates that the phi_qft_derivation_complete.py script
runs successfully and generates the expected output files with correct content.
"""

import json
import math
import os
import subprocess
import sys
import unittest
from pathlib import Path


class TestQFTDerivation(unittest.TestCase):
    """Test the QFT tensor derivation script."""

    @classmethod
    def setUpClass(cls):
        """Run the derivation script before tests."""
        # Change to script directory
        cls.script_dir = Path(__file__).parent
        cls.script_path = cls.script_dir / "phi_qft_derivation_complete.py"
        
        # Output file paths
        cls.symbolic_file = cls.script_dir / "Phi_tensor_symbolic.txt"
        cls.latex_file = cls.script_dir / "Phi_tensor.tex"
        cls.metadata_file = cls.script_dir / "Phi_tensor_metadata.json"
        
        # Clean up any existing output files
        for f in [cls.symbolic_file, cls.latex_file, cls.metadata_file]:
            if f.exists():
                f.unlink()
        
        # Run the script
        result = subprocess.run(
            [sys.executable, str(cls.script_path)],
            capture_output=True,
            text=True,
            cwd=cls.script_dir
        )
        
        cls.stdout = result.stdout
        cls.stderr = result.stderr
        cls.returncode = result.returncode

    def test_script_runs_successfully(self):
        """Test that the script runs without errors."""
        if self.returncode != 0:
            print(f"STDOUT:\n{self.stdout}")
            print(f"STDERR:\n{self.stderr}")
        self.assertEqual(self.returncode, 0, "Script should execute successfully")

    def test_symbolic_file_generated(self):
        """Test that symbolic tensor file is generated."""
        self.assertTrue(
            self.symbolic_file.exists(),
            "Phi_tensor_symbolic.txt should be generated"
        )

    def test_latex_file_generated(self):
        """Test that LaTeX file is generated."""
        self.assertTrue(
            self.latex_file.exists(),
            "Phi_tensor.tex should be generated"
        )

    def test_metadata_file_generated(self):
        """Test that metadata JSON file is generated."""
        self.assertTrue(
            self.metadata_file.exists(),
            "Phi_tensor_metadata.json should be generated"
        )

    def test_metadata_valid_json(self):
        """Test that metadata file contains valid JSON."""
        with open(self.metadata_file, 'r') as f:
            try:
                data = json.load(f)
            except json.JSONDecodeError as e:
                self.fail(f"Metadata file is not valid JSON: {e}")
        
        # Check that data is a dictionary
        self.assertIsInstance(data, dict, "Metadata should be a dictionary")

    def test_metadata_frequency(self):
        """Test that the frequency is correct."""
        with open(self.metadata_file, 'r') as f:
            data = json.load(f)
        
        self.assertIn('frequency_Hz', data, "Metadata should contain frequency_Hz")
        self.assertEqual(data['frequency_Hz'], 141.7001, "Frequency should be 141.7001 Hz")

    def test_metadata_omega(self):
        """Test that omega is computed correctly."""
        with open(self.metadata_file, 'r') as f:
            data = json.load(f)
        
        self.assertIn('omega_rad_s', data, "Metadata should contain omega_rad_s")
        expected_omega = 2 * math.pi * 141.7001
        self.assertAlmostEqual(
            data['omega_rad_s'], 
            expected_omega, 
            places=4,
            msg="Omega should be 2π × frequency"
        )

    def test_metadata_wavelength(self):
        """Test that wavelength is computed correctly."""
        with open(self.metadata_file, 'r') as f:
            data = json.load(f)
        
        self.assertIn('lambda_m', data, "Metadata should contain lambda_m")
        c = 299792458  # m/s
        expected_lambda = c / 141.7001
        self.assertAlmostEqual(
            data['lambda_m'],
            expected_lambda,
            places=2,
            msg="Wavelength should be c/frequency"
        )

    def test_seeley_dewitt_coefficients(self):
        """Test that Seeley-DeWitt coefficients are correct."""
        with open(self.metadata_file, 'r') as f:
            data = json.load(f)
        
        self.assertIn('coefficients', data, "Metadata should contain coefficients")
        coeff = data['coefficients']
        
        # Expected values
        expected_a1 = 1 / (720 * math.pi**2)
        expected_a2 = 1 / (2880 * math.pi**2)
        expected_a3 = -1 / (1440 * math.pi**2)
        
        self.assertAlmostEqual(
            coeff['a1'], expected_a1, places=10,
            msg="a1 coefficient should be 1/(720π²)"
        )
        self.assertAlmostEqual(
            coeff['a2'], expected_a2, places=10,
            msg="a2 coefficient should be 1/(2880π²)"
        )
        self.assertAlmostEqual(
            coeff['a3'], expected_a3, places=10,
            msg="a3 coefficient should be -1/(1440π²)"
        )

    def test_effective_mass(self):
        """Test that effective mass is computed."""
        with open(self.metadata_file, 'r') as f:
            data = json.load(f)
        
        self.assertIn('effective_mass_kg', data, "Metadata should contain effective_mass_kg")
        # Should be very small (quantum scale)
        self.assertLess(data['effective_mass_kg'], 1e-40, "Effective mass should be quantum scale")
        self.assertGreater(data['effective_mass_kg'], 0, "Effective mass should be positive")

    def test_coupling_scale(self):
        """Test that coupling scale is computed."""
        with open(self.metadata_file, 'r') as f:
            data = json.load(f)
        
        self.assertIn('coupling_scale', data, "Metadata should contain coupling_scale")
        # Should be small but non-zero
        self.assertGreater(data['coupling_scale'], 0, "Coupling scale should be positive")

    def test_metadata_references(self):
        """Test that references are included."""
        with open(self.metadata_file, 'r') as f:
            data = json.load(f)
        
        self.assertIn('references', data, "Metadata should contain references")
        self.assertIsInstance(data['references'], list, "References should be a list")
        self.assertGreater(len(data['references']), 0, "Should have at least one reference")
        
        # Check for key references
        refs_text = " ".join(data['references'])
        self.assertIn("Birrell", refs_text, "Should reference Birrell & Davies")
        self.assertIn("Quantum Fields in Curved Space", refs_text, "Should reference QFT book")

    def test_latex_file_structure(self):
        """Test that LaTeX file has correct structure."""
        with open(self.latex_file, 'r') as f:
            latex_content = f.read()
        
        # Check for LaTeX document structure
        self.assertIn(r"\documentclass{article}", latex_content, "Should have documentclass")
        self.assertIn(r"\usepackage{amsmath}", latex_content, "Should include amsmath package")
        self.assertIn(r"\begin{document}", latex_content, "Should have begin document")
        self.assertIn(r"\end{document}", latex_content, "Should have end document")
        
        # Check for tensor content
        self.assertIn(r"\Phi_{ij}", latex_content, "Should contain Phi tensor")
        self.assertIn(r"\Psi", latex_content, "Should contain Psi field")

    def test_symbolic_file_content(self):
        """Test that symbolic file contains matrix representation."""
        with open(self.symbolic_file, 'r') as f:
            symbolic_content = f.read()
        
        # Check for matrix structure
        self.assertIn("Matrix", symbolic_content, "Should contain Matrix")
        # Check for key symbols
        self.assertIn("Ψ", symbolic_content, "Should contain Ψ symbol")

    def test_stdout_contains_completion_message(self):
        """Test that script outputs completion message."""
        self.assertIn("DERIVACIÓN COMPLETADA", self.stdout, "Should print completion message")
        self.assertIn("JMMB", self.stdout, "Should include author signature")

    def test_stdout_contains_steps(self):
        """Test that all derivation steps are printed."""
        required_steps = [
            "PASO 1",  # QFT calculation
            "PASO 2",  # Effective geometry
            "PASO 3",  # Tensor construction
            "PASO 4",  # Physical interpretation
            "PASO 5",  # Extended NSE
            "PASO 6",  # Magnitude estimation
            "PASO 7",  # Export results
        ]
        
        for step in required_steps:
            self.assertIn(step, self.stdout, f"Output should include {step}")


class TestMathematicalConsistency(unittest.TestCase):
    """Test mathematical consistency of the derivation."""

    def test_coefficient_relationships(self):
        """Test mathematical relationships between coefficients."""
        metadata_file = Path(__file__).parent / "Phi_tensor_metadata.json"
        with open(metadata_file, 'r') as f:
            data = json.load(f)
        
        coeff = data['coefficients']
        a1 = coeff['a1']
        a2 = coeff['a2']
        a3 = coeff['a3']
        
        # a2 should be a1/4
        self.assertAlmostEqual(a2, a1/4, places=10, msg="a2 should equal a1/4")
        
        # a3 should be -a1/2
        self.assertAlmostEqual(a3, -a1/2, places=10, msg="a3 should equal -a1/2")


def run_tests():
    """Run all tests and return exit code."""
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestQFTDerivation))
    suite.addTests(loader.loadTestsFromTestCase(TestMathematicalConsistency))
    
    # Run tests with verbose output
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Return 0 if successful, 1 otherwise
    return 0 if result.wasSuccessful() else 1


if __name__ == '__main__':
    sys.exit(run_tests())
