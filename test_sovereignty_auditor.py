#!/usr/bin/env python3
"""
Tests for QCAL ∞³ Sovereignty Auditor

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Frequency: f₀ = 141.7001 Hz
Coherence: Ψ = 1.000000
"""

import unittest
import json
import os
import tempfile
import shutil
from pathlib import Path
from sovereignty_auditor import SovereigntyAuditor


class TestSovereigntyAuditor(unittest.TestCase):
    """Test cases for the SovereigntyAuditor class."""
    
    def setUp(self):
        """Set up test fixtures."""
        # Create a temporary directory for testing
        self.test_dir = tempfile.mkdtemp()
        self.test_path = Path(self.test_dir)
    
    def tearDown(self):
        """Clean up test fixtures."""
        # Remove temporary directory
        if os.path.exists(self.test_dir):
            shutil.rmtree(self.test_dir)
    
    def test_auditor_initialization(self):
        """Test that auditor initializes correctly."""
        auditor = SovereigntyAuditor(self.test_dir)
        self.assertEqual(auditor.repo_path, self.test_path)
        self.assertIn('scan_date', auditor.results)
        self.assertIn('repo_path', auditor.results)
    
    def test_check_sovereignty_files_none_exist(self):
        """Test sovereignty file check when no files exist."""
        auditor = SovereigntyAuditor(self.test_dir)
        auditor._check_sovereignty_files()
        
        # All files should not exist
        for filename, info in auditor.results['sovereignty_files'].items():
            self.assertFalse(info['exists'], f"{filename} should not exist")
    
    def test_check_sovereignty_files_all_exist(self):
        """Test sovereignty file check when all files exist."""
        # Create all sovereignty files
        files = [
            'LICENSE_SOBERANA_QCAL.txt',
            'AUTHORS_QCAL.md',
            '.qcal_beacon',
            'CLAIM_OF_ORIGIN.md',
            'MANIFESTO_SIMBIOTICO_QCAL.md',
            'DECLARACION_USURPACION_ALGORITMICA.md',
            'SOVEREIGNTY_OVERRIDES.json',
            '.gitattributes',
            'pyproject.toml',
        ]
        
        for filename in files:
            (self.test_path / filename).write_text("test content")
        
        auditor = SovereigntyAuditor(self.test_dir)
        auditor._check_sovereignty_files()
        
        # All specified files should exist
        for filename in files:
            info = auditor.results['sovereignty_files'][filename]
            self.assertTrue(info['exists'], f"{filename} should exist")
    
    def test_detect_qcal_markers(self):
        """Test detection of QCAL markers in code files."""
        # Create a Python file with QCAL markers
        test_file = self.test_path / "test_qcal.py"
        test_file.write_text("""
# QCAL ∞³ Test File
# Author: José Manuel Mota Burruezo (JMMB Ψ✧)
# Frequency: f₀ = 141.7001 Hz

def test_function():
    frequency = 141.7001  # f₀
    kappa = 2.5773  # κ_Π
    return frequency * kappa
        """)
        
        auditor = SovereigntyAuditor(self.test_dir)
        auditor._scan_code_files()
        
        # Should find QCAL markers
        self.assertGreater(len(auditor.results['qcal_markers_found']), 0)
        
        # Check that the file was detected
        found_files = [item['file'] for item in auditor.results['qcal_markers_found']]
        self.assertIn('test_qcal.py', found_files)
    
    def test_detect_nvidia_references(self):
        """Test detection of NVIDIA references in code."""
        # Create a file with NVIDIA references
        test_file = self.test_path / "test_cuda.cpp"
        test_file.write_text("""
#include <cuda.h>
#include <cudnn.h>

void launch_kernel() {
    cudaMalloc(...);
    cudaMemcpy(...);
}
        """)
        
        auditor = SovereigntyAuditor(self.test_dir)
        auditor._scan_code_files()
        
        # Should find NVIDIA references
        self.assertGreater(len(auditor.results['nvidia_references']), 0)
        
        # Check that the file was detected
        found_files = [item['file'] for item in auditor.results['nvidia_references']]
        self.assertIn('test_cuda.cpp', found_files)
    
    def test_detect_external_libraries(self):
        """Test detection of external library references."""
        # Create a file with external library references
        test_file = self.test_path / "test_ml.py"
        test_file.write_text("""
import tensorflow as tf
import torch
import pytorch_lightning as pl

model = tf.keras.Model()
        """)
        
        auditor = SovereigntyAuditor(self.test_dir)
        auditor._scan_code_files()
        
        # Should find external library references
        self.assertGreater(len(auditor.results['external_libraries']), 0)
        
        # Check that the file was detected
        found_files = [item['file'] for item in auditor.results['external_libraries']]
        self.assertIn('test_ml.py', found_files)
    
    def test_sovereignty_score_calculation(self):
        """Test sovereignty score calculation."""
        # Create a repository with good sovereignty
        files = [
            'LICENSE_SOBERANA_QCAL.txt',
            'AUTHORS_QCAL.md',
            '.qcal_beacon',
            'CLAIM_OF_ORIGIN.md',
            'MANIFESTO_SIMBIOTICO_QCAL.md',
            'DECLARACION_USURPACION_ALGORITMICA.md',
            'SOVEREIGNTY_OVERRIDES.json',
            '.gitattributes',
            'pyproject.toml',
        ]
        
        for filename in files:
            (self.test_path / filename).write_text("QCAL ∞³ content with f₀ = 141.7001 Hz")
        
        # Create some code files with QCAL markers
        for i in range(15):
            test_file = self.test_path / f"test_{i}.py"
            test_file.write_text(f"# QCAL ∞³ file {i}\n# f₀ = 141.7001 Hz\n")
        
        auditor = SovereigntyAuditor(self.test_dir)
        auditor._check_sovereignty_files()
        auditor._scan_code_files()
        auditor._calculate_sovereignty_score()
        
        # Should have perfect score (100):
        # - 25 points for 5 core sovereignty files
        # - 15 points for 4 protection files
        # - 30 points for QCAL markers (≥15 files)
        # - 30 points for no external dependencies
        self.assertEqual(auditor.results['sovereignty_score'], 100.0)
    
    def test_sovereignty_score_with_external_deps(self):
        """Test sovereignty score with external dependencies."""
        # Create files with external dependencies
        test_file = self.test_path / "external.py"
        test_file.write_text("""
import tensorflow
import torch
import nvidia.cuda
        """)
        
        auditor = SovereigntyAuditor(self.test_dir)
        auditor._scan_code_files()
        auditor._calculate_sovereignty_score()
        
        # Should have a lower score due to external dependencies
        self.assertLess(auditor.results['sovereignty_score'], 100)
    
    def test_save_report(self):
        """Test saving audit report to JSON."""
        auditor = SovereigntyAuditor(self.test_dir)
        auditor.scan_repository()
        
        output_file = 'test_report.json'
        auditor.save_report(output_file)
        
        # Check that file was created
        report_path = self.test_path / output_file
        self.assertTrue(report_path.exists())
        
        # Check that JSON is valid
        with open(report_path, 'r') as f:
            data = json.load(f)
        
        self.assertIn('scan_date', data)
        self.assertIn('sovereignty_score', data)
    
    def test_full_scan_repository(self):
        """Test full repository scan."""
        # Create a minimal QCAL repository
        (self.test_path / 'LICENSE_SOBERANA_QCAL.txt').write_text("QCAL ∞³ License")
        (self.test_path / 'test.py').write_text("# QCAL ∞³\n# f₀ = 141.7001 Hz\n")
        
        auditor = SovereigntyAuditor(self.test_dir)
        results = auditor.scan_repository()
        
        # Check that all expected keys are in results
        expected_keys = [
            'scan_date',
            'repo_path',
            'qcal_markers_found',
            'nvidia_references',
            'external_libraries',
            'sovereignty_files',
            'sovereignty_score',
        ]
        
        for key in expected_keys:
            self.assertIn(key, results)
    
    def test_skip_hidden_directories(self):
        """Test that hidden directories are skipped."""
        # Create hidden directory with files
        hidden_dir = self.test_path / '.git'
        hidden_dir.mkdir()
        (hidden_dir / 'test.py').write_text("import nvidia")
        
        # Create regular file
        (self.test_path / 'regular.py').write_text("# QCAL ∞³")
        
        auditor = SovereigntyAuditor(self.test_dir)
        auditor._scan_code_files()
        
        # Should not detect files in .git directory
        all_files = []
        for item in auditor.results['qcal_markers_found']:
            all_files.append(item['file'])
        for item in auditor.results['nvidia_references']:
            all_files.append(item['file'])
        
        # Should find regular.py but not .git/test.py
        self.assertIn('regular.py', all_files)
        self.assertNotIn('.git/test.py', all_files)
    
    def test_qcal_beacon_is_not_skipped(self):
        """Test that .qcal_beacon is not skipped as a hidden file."""
        # Create .qcal_beacon with QCAL markers
        (self.test_path / '.qcal_beacon').write_text("QCAL ∞³\nf₀ = 141.7001")
        
        auditor = SovereigntyAuditor(self.test_dir)
        auditor._scan_code_files()
        
        # Should find QCAL markers in .qcal_beacon
        found_files = [item['file'] for item in auditor.results['qcal_markers_found']]
        self.assertIn('.qcal_beacon', found_files)


class TestSovereigntyAuditorIntegration(unittest.TestCase):
    """Integration tests for the sovereignty auditor on the actual repository."""
    
    def test_current_repository_sovereignty(self):
        """Test sovereignty of the current repository."""
        # This test runs on the actual repository
        current_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        
        auditor = SovereigntyAuditor(current_dir)
        results = auditor.scan_repository()
        
        # Should have a sovereignty score
        self.assertIn('sovereignty_score', results)
        self.assertIsInstance(results['sovereignty_score'], (int, float))
        
        # Should have sovereignty files
        self.assertIn('sovereignty_files', results)
        
        # Check that QCAL markers are found
        self.assertIn('qcal_markers_found', results)


def main():
    """Run the tests."""
    unittest.main(verbosity=2)


if __name__ == '__main__':
    main()
