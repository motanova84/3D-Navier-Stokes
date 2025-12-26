#!/usr/bin/env python3
"""
Test suite for technical_details_expansion.py

Tests the generation of technical details LaTeX file.

Author: 3D-Navier-Stokes Research Team
License: MIT
"""

import unittest
import os
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from technical_details_expansion import generate_detailed_proofs


class TestTechnicalDetailsExpansion(unittest.TestCase):
    """Test cases for technical_details_expansion module"""
    
    def setUp(self):
        """Set up test fixtures"""
        self.output_file = 'artifacts/paper/technical_details_expanded.tex'
        # Remove output file if it exists from previous test
        if os.path.exists(self.output_file):
            os.remove(self.output_file)
    
    def tearDown(self):
        """Clean up after tests"""
        # Keep the generated file for inspection but could remove it if desired
        pass
    
    def test_generate_detailed_proofs_creates_file(self):
        """Test that generate_detailed_proofs creates the output file"""
        # Ensure file doesn't exist before test
        self.assertFalse(os.path.exists(self.output_file))
        
        # Generate the file
        generate_detailed_proofs()
        
        # Check file was created
        self.assertTrue(os.path.exists(self.output_file))
    
    def test_generated_file_not_empty(self):
        """Test that generated file is not empty"""
        generate_detailed_proofs()
        
        # Check file size
        file_size = os.path.getsize(self.output_file)
        self.assertGreater(file_size, 100, "Generated file should not be empty")
    
    def test_file_contains_latex_structure(self):
        """Test that generated file contains valid LaTeX structure"""
        generate_detailed_proofs()
        
        with open(self.output_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Check for essential LaTeX commands
        self.assertIn(r'\documentclass{article}', content)
        self.assertIn(r'\begin{document}', content)
        self.assertIn(r'\end{document}', content)
        self.assertIn(r'\maketitle', content)
    
    def test_file_contains_required_sections(self):
        """Test that file contains all required sections"""
        generate_detailed_proofs()
        
        with open(self.output_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Check for required sections
        required_sections = [
            r'\section{Lema 1 Expandido: Acotación de $\Psi$}',
            r'\section{Lema 2 Expandido: Coercividad de $\Phi$}',
            r'\section{Lema 3 Expandido: Disipación de Energía}',
            r'\section{Lema 4 Expandido: Estimaciones de Sobolev}',
        ]
        
        for section in required_sections:
            self.assertIn(section, content, f"Missing section: {section}")
    
    def test_file_contains_author_and_title(self):
        """Test that file contains author and title"""
        generate_detailed_proofs()
        
        with open(self.output_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        self.assertIn(r'\title{Detalles Técnicos Completos: Lemas Auxiliares}', content)
        self.assertIn(r'\author{José Manuel Mota Burruezo}', content)
    
    def test_file_contains_mathematical_content(self):
        """Test that file contains key mathematical formulas"""
        generate_detailed_proofs()
        
        with open(self.output_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Check for key mathematical content
        math_elements = [
            r'\mathcal{I}',
            r'\mathbb{R}^3',
            r'\Psi',
            r'\Phi',
            'Shannon',
            'Sobolev',
            'Gronwall',
        ]
        
        for element in math_elements:
            self.assertIn(element, content, f"Missing mathematical element: {element}")
    
    def test_directory_structure_created(self):
        """Test that the artifacts/paper directory exists after generation"""
        generate_detailed_proofs()
        
        paper_dir = Path('artifacts/paper')
        self.assertTrue(paper_dir.exists())
        self.assertTrue(paper_dir.is_dir())


if __name__ == '__main__':
    unittest.main()
