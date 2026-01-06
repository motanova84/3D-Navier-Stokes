#!/usr/bin/env python3
"""
Test Suite for Security and Reproducibility Documentation
Validates the existence and content of security-related files.
"""

import unittest
import os
import sys

class TestSecurityDocumentation(unittest.TestCase):
    """Test cases for security and reproducibility documentation"""
    
    def setUp(self):
        """Get project root directory"""
        self.project_root = os.path.dirname(os.path.abspath(__file__))
    
    def test_env_lock_exists(self):
        """Test that ENV.lock file exists"""
        env_lock = os.path.join(self.project_root, 'ENV.lock')
        self.assertTrue(
            os.path.exists(env_lock),
            "ENV.lock file must exist for reproducibility"
        )
    
    def test_env_lock_has_content(self):
        """Test that ENV.lock has required package specifications"""
        env_lock = os.path.join(self.project_root, 'ENV.lock')
        with open(env_lock, 'r') as f:
            content = f.read()
        
        # Check for required packages
        required_packages = ['numpy', 'scipy', 'matplotlib', 'sympy', 'psutil', 'PyPDF2']
        for package in required_packages:
            self.assertIn(
                package,
                content,
                f"ENV.lock must contain {package} specification"
            )
        
        # Check for version specifications
        self.assertIn('==', content, "ENV.lock must contain exact version specifications")
    
    def test_seguridad_md_exists(self):
        """Test that SEGURIDAD.md exists"""
        seguridad = os.path.join(self.project_root, 'SEGURIDAD.md')
        self.assertTrue(
            os.path.exists(seguridad),
            "SEGURIDAD.md must exist for security documentation"
        )
    
    def test_seguridad_md_has_sections(self):
        """Test that SEGURIDAD.md has required sections"""
        seguridad = os.path.join(self.project_root, 'SEGURIDAD.md')
        with open(seguridad, 'r', encoding='utf-8') as f:
            content = f.read()
        
        required_sections = [
            'Resumen Ejecutivo',
            'Análisis de Seguridad',
            'Gestión de Dependencias',
            'Validación de Entrada',
            'Estabilidad Numérica',
            'Reproducibilidad'
        ]
        
        for section in required_sections:
            self.assertIn(
                section,
                content,
                f"SEGURIDAD.md must contain section: {section}"
            )
    
    def test_resumen_seguridad_exists(self):
        """Test that RESUMEN_DE_SEGURIDAD.md exists"""
        resumen = os.path.join(self.project_root, 'RESUMEN_DE_SEGURIDAD.md')
        self.assertTrue(
            os.path.exists(resumen),
            "RESUMEN_DE_SEGURIDAD.md must exist for security summary"
        )
    
    def test_resumen_seguridad_has_status(self):
        """Test that RESUMEN_DE_SEGURIDAD.md has security status"""
        resumen = os.path.join(self.project_root, 'RESUMEN_DE_SEGURIDAD.md')
        with open(resumen, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Check for security status indicators
        self.assertTrue(
            'SEGURO' in content or 'SECURE' in content,
            "RESUMEN_DE_SEGURIDAD.md must indicate security status"
        )
        
        # Check for key sections
        self.assertIn('CodeQL', content, "Must mention CodeQL analysis")
        self.assertIn('ENV.lock', content, "Must reference ENV.lock")
    
    def test_verify_environment_script_exists(self):
        """Test that verify_environment.sh script exists"""
        script = os.path.join(self.project_root, 'Scripts', 'verify_environment.sh')
        self.assertTrue(
            os.path.exists(script),
            "Scripts/verify_environment.sh must exist for environment verification"
        )
    
    def test_verify_environment_script_executable(self):
        """Test that verify_environment.sh is executable"""
        script = os.path.join(self.project_root, 'Scripts', 'verify_environment.sh')
        if os.path.exists(script):
            # Check if file has execute permission
            self.assertTrue(
                os.access(script, os.X_OK),
                "Scripts/verify_environment.sh must be executable"
            )
    
    def test_readme_references_security_docs(self):
        """Test that README.md references security documentation"""
        readme = os.path.join(self.project_root, 'README.md')
        with open(readme, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Check for references to security documentation
        self.assertIn(
            'SEGURIDAD.md',
            content,
            "README.md must reference SEGURIDAD.md"
        )
        self.assertIn(
            'ENV.lock',
            content,
            "README.md must reference ENV.lock"
        )
    
    def test_lean_toolchain_referenced(self):
        """Test that lean-toolchain is referenced in ENV.lock"""
        env_lock = os.path.join(self.project_root, 'ENV.lock')
        with open(env_lock, 'r') as f:
            content = f.read()
        
        self.assertIn(
            'lean-toolchain',
            content,
            "ENV.lock must reference lean-toolchain"
        )
        self.assertIn(
            'Lean',
            content,
            "ENV.lock must mention Lean dependencies"
        )
    
    def test_lake_manifest_referenced(self):
        """Test that lake-manifest.json is referenced in ENV.lock"""
        env_lock = os.path.join(self.project_root, 'ENV.lock')
        with open(env_lock, 'r') as f:
            content = f.read()
        
        self.assertIn(
            'lake-manifest.json',
            content,
            "ENV.lock must reference lake-manifest.json"
        )
    
    def test_reproducibility_instructions(self):
        """Test that ENV.lock contains reproducibility instructions"""
        env_lock = os.path.join(self.project_root, 'ENV.lock')
        with open(env_lock, 'r') as f:
            content = f.read()
        
        # Check for key reproducibility concepts
        reproducibility_terms = [
            'reproducib',  # matches reproducible, reproducibility
            'pip install',
            'lake'
        ]
        
        for term in reproducibility_terms:
            self.assertIn(
                term,
                content.lower(),
                f"ENV.lock should contain reproducibility term: {term}"
            )
    
    def test_security_summary_exists_english(self):
        """Test that SECURITY_SUMMARY.md (English version) exists"""
        security_summary = os.path.join(self.project_root, 'SECURITY_SUMMARY.md')
        self.assertTrue(
            os.path.exists(security_summary),
            "SECURITY_SUMMARY.md must exist (English version)"
        )


class TestEnvironmentVerificationScript(unittest.TestCase):
    """Test cases for the environment verification script"""
    
    def setUp(self):
        """Get project root directory"""
        self.project_root = os.path.dirname(os.path.abspath(__file__))
        self.script_path = os.path.join(self.project_root, 'Scripts', 'verify_environment.sh')
    
    def test_script_has_shebang(self):
        """Test that verify_environment.sh has proper shebang"""
        if os.path.exists(self.script_path):
            with open(self.script_path, 'r') as f:
                first_line = f.readline()
            self.assertTrue(
                first_line.startswith('#!/bin/bash') or first_line.startswith('#!/usr/bin/env bash'),
                "verify_environment.sh must have bash shebang"
            )
    
    def test_script_checks_python_version(self):
        """Test that script checks Python version"""
        if os.path.exists(self.script_path):
            with open(self.script_path, 'r') as f:
                content = f.read()
            self.assertIn(
                'python',
                content.lower(),
                "Script must check Python version"
            )
    
    def test_script_checks_packages(self):
        """Test that script checks package versions"""
        if os.path.exists(self.script_path):
            with open(self.script_path, 'r') as f:
                content = f.read()
            
            # Check for package verification
            self.assertTrue(
                'numpy' in content or 'pip' in content,
                "Script must check package versions"
            )


def run_tests():
    """Run all tests"""
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add test cases
    suite.addTests(loader.loadTestsFromTestCase(TestSecurityDocumentation))
    suite.addTests(loader.loadTestsFromTestCase(TestEnvironmentVerificationScript))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Return exit code
    return 0 if result.wasSuccessful() else 1


if __name__ == '__main__':
    sys.exit(run_tests())
