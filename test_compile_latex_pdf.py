#!/usr/bin/env python3
"""
Test suite for compile_latex_pdf.py

Tests the LaTeX compilation script functionality.
"""

import unittest
import os
import sys
from pathlib import Path
import shutil

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

# Import the module to test
from compile_latex_pdf import compile_latex_to_pdf


class TestCompileLaTeXPDF(unittest.TestCase):
    """Test LaTeX compilation script."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.artifacts_dir = Path("artifacts/paper")
        self.tex_file = self.artifacts_dir / "psi_nse_global_regularity.tex"
        self.pdf_file = self.artifacts_dir / "psi_nse_global_regularity.pdf"
        
    def tearDown(self):
        """Clean up after tests."""
        # Remove test artifacts if they exist
        if self.artifacts_dir.exists():
            # Only remove if it was created by our test
            for file in self.artifacts_dir.glob("psi_nse_global_regularity.*"):
                try:
                    file.unlink()
                except OSError:
                    pass
    
    def test_rigorous_proof_file_exists(self):
        """Test that the source rigorous_proof_psi_nse.tex file exists."""
        source_file = Path("rigorous_proof_psi_nse.tex")
        self.assertTrue(
            source_file.exists(),
            f"Source file {source_file} does not exist"
        )
    
    def test_creates_artifacts_directory(self):
        """Test that the script creates the artifacts directory."""
        # Remove directory if it exists
        if self.artifacts_dir.exists():
            shutil.rmtree(self.artifacts_dir.parent)
        
        compile_latex_to_pdf()
        
        self.assertTrue(
            self.artifacts_dir.exists(),
            "artifacts/paper directory was not created"
        )
    
    def test_creates_tex_file(self):
        """Test that the script creates the combined LaTeX file."""
        compile_latex_to_pdf()
        
        self.assertTrue(
            self.tex_file.exists(),
            f"LaTeX file {self.tex_file} was not created"
        )
    
    def test_tex_file_has_content(self):
        """Test that the generated LaTeX file has content."""
        compile_latex_to_pdf()
        
        with open(self.tex_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Check for key components
        self.assertIn(r'\documentclass[12pt,a4paper]{article}', content)
        self.assertIn(r'\begin{document}', content)
        self.assertIn(r'\end{document}', content)
        self.assertIn('Regularidad Global', content)
        self.assertIn('Navier-Stokes', content)
        self.assertIn(r'\Phi_{ij}(\Psi)', content)
        self.assertIn('141.7001', content)
    
    def test_tex_file_includes_proof_content(self):
        """Test that the combined file includes content from rigorous_proof_psi_nse.tex."""
        compile_latex_to_pdf()
        
        with open(self.tex_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Check for content from the proof file
        self.assertIn(r'\section{Introducción}', content)
        self.assertIn(r'\section{Estimaciones de Energía}', content)
        self.assertIn(r'\section{Criterio de Beale-Kato-Majda}', content)
        self.assertIn('Campo de Coherencia', content)
    
    def test_tex_file_has_proper_structure(self):
        """Test that the LaTeX file has proper structure."""
        compile_latex_to_pdf()
        
        with open(self.tex_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Check structural elements
        self.assertIn(r'\usepackage{amsmath,amsthm,amssymb}', content)
        self.assertIn(r'\newtheorem{theorem}{Teorema}', content)
        self.assertIn(r'\newtheorem{lemma}{Lema}', content)
        self.assertIn(r'\maketitle', content)
        self.assertIn(r'\begin{abstract}', content)
        self.assertIn(r'\tableofcontents', content)
    
    def test_script_runs_without_errors(self):
        """Test that the script runs without raising exceptions."""
        try:
            compile_latex_to_pdf()
        except Exception as e:
            self.fail(f"compile_latex_to_pdf() raised {type(e).__name__}: {e}")
    
    def test_handles_missing_source_file_gracefully(self):
        """Test that the script handles missing source file appropriately."""
        # Temporarily rename the source file
        source_file = Path("rigorous_proof_psi_nse.tex")
        backup_file = Path("rigorous_proof_psi_nse.tex.backup")
        
        if source_file.exists():
            source_file.rename(backup_file)
        
        try:
            # This should raise FileNotFoundError
            with self.assertRaises(FileNotFoundError):
                compile_latex_to_pdf()
        finally:
            # Restore the file
            if backup_file.exists():
                backup_file.rename(source_file)


class TestLaTeXContent(unittest.TestCase):
    """Test the content and structure of the generated LaTeX."""
    
    def setUp(self):
        """Set up test fixtures."""
        compile_latex_to_pdf()
        self.tex_file = Path("artifacts/paper/psi_nse_global_regularity.tex")
        with open(self.tex_file, 'r', encoding='utf-8') as f:
            self.content = f.read()
    
    def test_has_author_information(self):
        """Test that author information is present."""
        self.assertIn('José Manuel Mota Burruezo', self.content)
        self.assertIn('Instituto Consciencia Cuántica', self.content)
    
    def test_has_date(self):
        """Test that date is present."""
        self.assertIn('Noviembre 2025', self.content)
    
    def test_has_abstract_keywords(self):
        """Test that abstract and keywords are present."""
        self.assertIn(r'\begin{abstract}', self.content)
        self.assertIn('Palabras clave', self.content)
        self.assertIn('MSC 2020', self.content)
    
    def test_has_mathematical_content(self):
        """Test that mathematical equations are present."""
        self.assertIn(r'\begin{equation}', self.content)
        self.assertIn(r'\Phi_{ij}(\Psi)', self.content)
        self.assertIn(r'\nabla', self.content)
        self.assertIn(r'\Delta', self.content)
    
    def test_has_fundamental_frequency(self):
        """Test that the fundamental frequency is mentioned."""
        self.assertIn('141.7001', self.content)
        self.assertIn('f_0', self.content)
    
    def test_has_theorems_and_proofs(self):
        """Test that theorems and proofs are present."""
        self.assertIn(r'\begin{theorem}', self.content)
        self.assertIn(r'\begin{proof}', self.content)
        self.assertIn(r'\begin{lemma}', self.content)


if __name__ == '__main__':
    # Run tests
    unittest.main(verbosity=2)
