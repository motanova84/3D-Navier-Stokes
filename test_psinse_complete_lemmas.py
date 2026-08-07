#!/usr/bin/env python3
"""
Test suite for PsiNSE Complete Lemmas with QCAL Infrastructure

Validates the structure and presence of the Lean4 formalization files
for the Ψ-NSE complete lemmas integrated with QCAL framework.
"""

import os
import re
import unittest
from pathlib import Path


class TestPsiNSECompleteLemmas(unittest.TestCase):
    """Test suite for PsiNSE complete lemmas implementation"""
    
    @classmethod
    def setUpClass(cls):
        """Set up paths to Lean files"""
        cls.base_path = Path(__file__).parent / "Lean4-Formalization" / "NavierStokes"
        
        cls.files = {
            "psinse": cls.base_path / "PsiNSE_CompleteLemmas_WithInfrastructure.lean",
            "pnp": cls.base_path / "PNP.lean",
            "qcal": cls.base_path / "QCAL.lean",
            "advanced": cls.base_path / "AdvancedSpaces.lean",
            "tests": cls.base_path / "PsiNSE_Tests.lean",
            "readme": cls.base_path / "README_PsiNSE.md",
        }
    
    def test_files_exist(self):
        """Test that all required files exist"""
        for name, path in self.files.items():
            with self.subTest(file=name):
                self.assertTrue(
                    path.exists(),
                    f"File {name} does not exist at {path}"
                )
    
    def test_f0_constant_defined(self):
        """Test that f₀ = 141.7001 Hz is defined"""
        psinse_content = self.files["psinse"].read_text()
        
        # Check f₀ definition
        self.assertIn("def f₀", psinse_content)
        self.assertIn("141.7001", psinse_content)
        
        # Check in QCAL module
        qcal_content = self.files["qcal"].read_text()
        self.assertIn("141.7001", qcal_content)
    
    def test_theorem_statements_present(self):
        """Test that all key theorems are defined"""
        psinse_content = self.files["psinse"].read_text()
        
        required_theorems = [
            "f0_from_primes",
            "sobolev_embedding_l_infty",
            "banach_fixed_point_complete",
            "integration_by_parts_divergence_free",
            "poincare_inequality_expander",
            "agmon_inequality_3d",
            "local_existence_kato_complete",
            "phi_tensor_treewidth_connection",
            "qcal_coherence_implies_regularity",
        ]
        
        for theorem in required_theorems:
            with self.subTest(theorem=theorem):
                self.assertIn(
                    f"theorem {theorem}",
                    psinse_content,
                    f"Theorem {theorem} not found"
                )
    
    def test_module_imports(self):
        """Test that required modules are imported"""
        psinse_content = self.files["psinse"].read_text()
        
        required_imports = [
            "NavierStokes.PNP",
            "NavierStokes.QCAL",
            "NavierStokes.AdvancedSpaces",
            "NavierStokes.BasicDefinitions",
            "Mathlib.Analysis.Calculus.FDeriv.Basic",
            "Mathlib.Topology.MetricSpace.Lipschitz",
        ]
        
        for import_stmt in required_imports:
            with self.subTest(import_module=import_stmt):
                self.assertIn(
                    f"import {import_stmt}",
                    psinse_content,
                    f"Import {import_stmt} not found"
                )
    
    def test_pnp_module_structure(self):
        """Test PNP module has required definitions"""
        pnp_content = self.files["pnp"].read_text()
        
        required_defs = [
            "CNF_Formula",
            "incidence_graph",
            "treewidth",
            "IC_complexity",
            "coupled_with",
        ]
        
        for def_name in required_defs:
            with self.subTest(definition=def_name):
                self.assertIn(
                    f"def {def_name}",
                    pnp_content,
                    f"Definition {def_name} not found in PNP module"
                )
    
    def test_qcal_module_structure(self):
        """Test QCAL module has required definitions"""
        qcal_content = self.files["qcal"].read_text()
        
        required_components = [
            "validated_f0",
            "derive_fundamental_frequency",
            "dominant_frequency",
            "derive_from_prime_harmonics",
        ]
        
        for component in required_components:
            with self.subTest(component=component):
                self.assertIn(
                    component,
                    qcal_content,
                    f"Component {component} not found in QCAL module"
                )
    
    def test_advanced_spaces_definitions(self):
        """Test AdvancedSpaces module has required type definitions"""
        advanced_content = self.files["advanced"].read_text()
        
        required_types = [
            "SobolevSpace",
            "Graph",
            "ExpanderGraph",
            "spectral_gap",
        ]
        
        for type_name in required_types:
            with self.subTest(type_def=type_name):
                self.assertIn(
                    type_name,
                    advanced_content,
                    f"Type {type_name} not found in AdvancedSpaces module"
                )
    
    def test_operators_defined(self):
        """Test that differential operators are defined"""
        advanced_content = self.files["advanced"].read_text()
        
        operators = [
            "divergence",
            "gradient",
            "laplacian",
            "time_deriv",
        ]
        
        for op in operators:
            with self.subTest(operator=op):
                self.assertIn(
                    f"def {op}",
                    advanced_content,
                    f"Operator {op} not found"
                )
    
    def test_test_file_structure(self):
        """Test that the test file is properly structured"""
        test_content = self.files["tests"].read_text()
        
        # Check imports
        self.assertIn(
            "import NavierStokes.PsiNSE_CompleteLemmas_WithInfrastructure",
            test_content
        )
        
        # Check that theorem checks exist
        self.assertIn("#check sobolev_embedding_l_infty", test_content)
        self.assertIn("#check f0_from_primes", test_content)
    
    def test_documentation_exists(self):
        """Test that documentation is comprehensive"""
        readme_content = self.files["readme"].read_text()
        
        required_sections = [
            "## Overview",
            "## Files Added",
            "## Implementation Status",
            "## Building",
            "## Integration Points",
        ]
        
        for section in required_sections:
            with self.subTest(section=section):
                self.assertIn(
                    section,
                    readme_content,
                    f"Documentation section {section} not found"
                )
    
    def test_no_placeholder_values(self):
        """Test that critical constants are not placeholders"""
        psinse_content = self.files["psinse"].read_text()
        
        # f₀ should be 141.7001, not 0 or 1
        self.assertIn("141.7001", psinse_content)
        
        # Check that f₀ uses QCAL validation
        self.assertIn(
            "QCAL.FrequencyValidation.validated_f0",
            psinse_content
        )
    
    def test_integration_comments(self):
        """Test that integration points are documented"""
        psinse_content = self.files["psinse"].read_text()
        
        # Check for integration documentation
        self.assertIn("QCAL", psinse_content)
        self.assertIn("P≠NP", psinse_content)
        self.assertIn("141hz", psinse_content)
        self.assertIn("adelic-bsd", psinse_content)
    
    def test_namespace_consistency(self):
        """Test that namespaces are used consistently"""
        for file_key in ["psinse", "pnp", "qcal", "advanced"]:
            content = self.files[file_key].read_text()
            with self.subTest(file=file_key):
                # Check for namespace declarations
                self.assertTrue(
                    "namespace" in content or "open" in content,
                    f"No namespace usage in {file_key}"
                )


class TestIntegrationReadiness(unittest.TestCase):
    """Test that the implementation is ready for integration"""
    
    def setUp(self):
        """Set up paths"""
        self.base_path = Path(__file__).parent / "Lean4-Formalization"
    
    def test_lakefile_exists(self):
        """Test that lakefile.lean exists"""
        lakefile = self.base_path / "lakefile.lean"
        self.assertTrue(lakefile.exists())
    
    def test_lean_toolchain_exists(self):
        """Test that lean-toolchain file exists"""
        toolchain = Path(__file__).parent / "lean-toolchain"
        self.assertTrue(toolchain.exists())
    
    def test_gitignore_configured(self):
        """Test that .gitignore is properly configured"""
        gitignore = self.base_path / ".gitignore"
        if gitignore.exists():
            content = gitignore.read_text()
            # Check for Lean build artifacts
            self.assertIn(".lake", content)
            self.assertIn("*.olean", content)


def run_tests():
    """Run all tests and print results"""
    print("=" * 70)
    print("PsiNSE Complete Lemmas - Test Suite")
    print("=" * 70)
    print()
    
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    suite.addTests(loader.loadTestsFromTestCase(TestPsiNSECompleteLemmas))
    suite.addTests(loader.loadTestsFromTestCase(TestIntegrationReadiness))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Print summary
    print()
    print("=" * 70)
    print("Test Summary")
    print("=" * 70)
    print(f"Tests run: {result.testsRun}")
    print(f"Successes: {result.testsRun - len(result.failures) - len(result.errors)}")
    print(f"Failures: {len(result.failures)}")
    print(f"Errors: {len(result.errors)}")
    print("=" * 70)
    
    return result.wasSuccessful()


if __name__ == "__main__":
    success = run_tests()
    exit(0 if success else 1)
