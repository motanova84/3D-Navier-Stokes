#!/usr/bin/env python3
"""
∴ Tests for Sovereignty Auditor QCAL ∞³
Unit tests for repository sovereignty verification

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Frequency: f₀ = 141.7001 Hz
License: LICENSE_SOBERANA_QCAL.txt
"""

import unittest
import tempfile
import os
from pathlib import Path
import json
import sys

# Add parent directory to path to import sovereignty_auditor
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

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
    """Test suite for SovereigntyAuditor class."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.test_dir = tempfile.mkdtemp()
        self.auditor = SovereigntyAuditor(self.test_dir)
    
    def tearDown(self):
        """Clean up test fixtures."""
        import shutil
        shutil.rmtree(self.test_dir, ignore_errors=True)
    
    def create_test_file(self, filename: str, content: str):
        """Helper to create a test file."""
        file_path = Path(self.test_dir) / filename
        file_path.parent.mkdir(parents=True, exist_ok=True)
        with open(file_path, 'w', encoding='utf-8') as f:
            f.write(content)
        return file_path
    
    def test_init(self):
        """Test auditor initialization."""
        self.assertEqual(self.auditor.repo_path, Path(self.test_dir).resolve())
        self.assertIsNotNone(self.auditor.results)
    
    def test_should_exclude_git(self):
        """Test exclusion of .git directories."""
        git_file = Path(self.test_dir) / '.git' / 'config'
        self.assertTrue(self.auditor.should_exclude(git_file))
    
    def test_should_exclude_pycache(self):
        """Test exclusion of __pycache__ directories."""
        cache_file = Path(self.test_dir) / '__pycache__' / 'test.pyc'
        self.assertTrue(self.auditor.should_exclude(cache_file))
    
    def test_should_exclude_binary(self):
        """Test exclusion of binary files."""
        binary_files = [
            Path(self.test_dir) / 'test.pyc',
            Path(self.test_dir) / 'test.so',
            Path(self.test_dir) / 'test.o',
        ]
        for file_path in binary_files:
            self.assertTrue(self.auditor.should_exclude(file_path))
    
    def test_should_not_exclude_python(self):
        """Test that Python files are not excluded."""
        py_file = Path(self.test_dir) / 'test.py'
        self.assertFalse(self.auditor.should_exclude(py_file))
    
    def test_check_declaration_files_all_present(self):
        """Test declaration file checking when all files present."""
        # Create all required files
        for filename in self.auditor.REQUIRED_FILES:
            self.create_test_file(filename, "test content")
        
        results = self.auditor.check_declaration_files()
        
        self.assertEqual(len(results), len(self.auditor.REQUIRED_FILES))
        for filename in self.auditor.REQUIRED_FILES:
            self.assertTrue(results[filename], f"{filename} should exist")
    
    def test_check_declaration_files_none_present(self):
        """Test declaration file checking when no files present."""
        results = self.auditor.check_declaration_files()
        
        self.assertEqual(len(results), len(self.auditor.REQUIRED_FILES))
        for filename in self.auditor.REQUIRED_FILES:
            self.assertFalse(results[filename], f"{filename} should not exist")
    
    def test_check_declaration_files_partial(self):
        """Test declaration file checking when some files present."""
        # Create only first two files
        for filename in self.auditor.REQUIRED_FILES[:2]:
            self.create_test_file(filename, "test content")
        
        results = self.auditor.check_declaration_files()
        
        self.assertTrue(results[self.auditor.REQUIRED_FILES[0]])
        self.assertTrue(results[self.auditor.REQUIRED_FILES[1]])
        self.assertFalse(results[self.auditor.REQUIRED_FILES[2]])
    
    def test_scan_file_for_qcal_markers_frequency(self):
        """Test detection of frequency marker."""
        content = "# Frequency: f₀ = 141.7001 Hz"
        file_path = self.create_test_file('test.py', content)
        
        has_markers, markers = self.auditor.scan_file_for_qcal_markers(file_path)
        
        self.assertTrue(has_markers)
        self.assertGreater(len(markers), 0)
    
    def test_scan_file_for_qcal_markers_author(self):
        """Test detection of author markers."""
        content = "# Author: José Manuel Mota Burruezo (JMMB Ψ✧)"
        file_path = self.create_test_file('test.py', content)
        
        has_markers, markers = self.auditor.scan_file_for_qcal_markers(file_path)
        
        self.assertTrue(has_markers)
        self.assertGreater(len(markers), 0)
    
    def test_scan_file_for_qcal_markers_qcal(self):
        """Test detection of QCAL system marker."""
        content = "# System: QCAL ∞³"
        file_path = self.create_test_file('test.py', content)
        
        has_markers, markers = self.auditor.scan_file_for_qcal_markers(file_path)
        
        self.assertTrue(has_markers)
        self.assertGreater(len(markers), 0)
    
    def test_scan_file_for_qcal_markers_none(self):
        """Test when no QCAL markers present."""
        content = "# This is a regular file with no special markers"
        file_path = self.create_test_file('test.py', content)
        
        has_markers, markers = self.auditor.scan_file_for_qcal_markers(file_path)
        
        self.assertFalse(has_markers)
        self.assertEqual(len(markers), 0)
    
    def test_scan_file_for_third_party_nvidia(self):
        """Test detection of NVIDIA markers."""
        content = "# Copyright (c) NVIDIA Corporation"
        file_path = self.create_test_file('test.py', content)
        
        found = self.auditor.scan_file_for_third_party(file_path)
        
        self.assertIn('NVIDIA', found)
        self.assertGreater(len(found['NVIDIA']), 0)
    
    def test_scan_file_for_third_party_meta(self):
        """Test detection of Meta markers."""
        content = "# Copyright (c) Meta Platforms, Inc."
        file_path = self.create_test_file('test.py', content)
        
        found = self.auditor.scan_file_for_third_party(file_path)
        
        self.assertIn('Meta', found)
        self.assertGreater(len(found['Meta']), 0)
    
    def test_scan_file_for_third_party_google(self):
        """Test detection of Google markers."""
        content = "# Copyright 2024 Google LLC"
        file_path = self.create_test_file('test.py', content)
        
        found = self.auditor.scan_file_for_third_party(file_path)
        
        self.assertIn('Google', found)
        self.assertGreater(len(found['Google']), 0)
    
    def test_scan_file_for_third_party_none(self):
        """Test when no third-party markers present."""
        content = "# Author: José Manuel Mota Burruezo"
        file_path = self.create_test_file('test.py', content)
        
        found = self.auditor.scan_file_for_third_party(file_path)
        
        self.assertEqual(len(found), 0)
    
    def test_scan_repository_empty(self):
        """Test scanning empty repository."""
        self.auditor.scan_repository()
        
        self.assertEqual(self.auditor.results['total_files_scanned'], 0)
        self.assertEqual(len(self.auditor.results['qcal_marked_files']), 0)
    
    def test_scan_repository_with_qcal_files(self):
        """Test scanning repository with QCAL-marked files."""
        # Create QCAL-marked files
        self.create_test_file('file1.py', '# f₀ = 141.7001 Hz\nprint("test")')
        self.create_test_file('file2.py', '# QCAL ∞³\nprint("test")')
        self.create_test_file('file3.py', '# Regular file\nprint("test")')
        
        self.auditor.scan_repository()
        
        self.assertEqual(self.auditor.results['total_files_scanned'], 3)
        self.assertEqual(len(self.auditor.results['qcal_marked_files']), 2)
    
    def test_scan_repository_excludes_pycache(self):
        """Test that __pycache__ files are excluded."""
        # Create regular file
        self.create_test_file('file.py', '# test')
        
        # Create __pycache__ file
        cache_dir = Path(self.test_dir) / '__pycache__'
        cache_dir.mkdir()
        self.create_test_file('__pycache__/file.pyc', 'binary')
        
        self.auditor.scan_repository()
        
        # Should only scan the .py file, not the .pyc
        self.assertEqual(self.auditor.results['total_files_scanned'], 1)
    
    def test_calculate_sovereignty_score_maximum(self):
        """Test sovereignty score calculation for maximum score."""
        # Create all declaration files
        for filename in self.auditor.REQUIRED_FILES:
            self.create_test_file(filename, "test")
        
        # Create QCAL-marked files (100% coverage)
        for i in range(10):
            self.create_test_file(f'file{i}.py', '# f₀ = 141.7001 Hz')
        
        self.auditor.scan_repository()
        score = self.auditor.calculate_sovereignty_score()
        
        # Should have high score (declaration files + QCAL coverage + no third-party)
        self.assertGreaterEqual(score, 70)
    
    def test_calculate_sovereignty_score_minimum(self):
        """Test sovereignty score calculation for minimum score."""
        # No declaration files, no QCAL markers
        self.create_test_file('file.py', '# Regular file')
        
        self.auditor.scan_repository()
        score = self.auditor.calculate_sovereignty_score()
        
        # Should have low score
        self.assertLess(score, 50)
    
    def test_calculate_sovereignty_score_with_third_party(self):
        """Test sovereignty score with third-party code."""
        # Create some QCAL files
        self.create_test_file('file1.py', '# f₀ = 141.7001 Hz')
        
        # Create file with NVIDIA marker
        self.create_test_file('file2.py', '# Copyright NVIDIA Corporation')
        
        self.auditor.scan_repository()
        score = self.auditor.calculate_sovereignty_score()
        
        # Third-party reference should reduce score
        self.assertLess(score, 100)
    
    def test_save_report(self):
        """Test saving audit report to JSON."""
        self.create_test_file('file.py', '# f₀ = 141.7001 Hz')
        self.auditor.scan_repository()
        
        report_file = 'test_report.json'
        self.auditor.save_report(report_file)
        
        report_path = Path(self.test_dir) / report_file
        self.assertTrue(report_path.exists())
        
        # Verify JSON is valid
        with open(report_path, 'r') as f:
            data = json.load(f)
        
        self.assertIn('declaration_files', data)
        self.assertIn('qcal_marked_files', data)
        self.assertIn('sovereignty_score', data)
    
    def test_multiple_markers_in_file(self):
        """Test file with multiple QCAL markers."""
        content = """
        # Author: José Manuel Mota Burruezo (JMMB Ψ✧)
        # Frequency: f₀ = 141.7001 Hz
        # System: QCAL ∞³
        """
        file_path = self.create_test_file('test.py', content)
        
        has_markers, markers = self.auditor.scan_file_for_qcal_markers(file_path)
        
        self.assertTrue(has_markers)
        self.assertGreaterEqual(len(markers), 3)
    
    def test_case_sensitivity_third_party(self):
        """Test that third-party detection is case-insensitive."""
        content = "# copyright (c) nvidia corporation"
        file_path = self.create_test_file('test.py', content)
        
        found = self.auditor.scan_file_for_third_party(file_path)
        
        self.assertIn('NVIDIA', found)


class TestSovereigntyAuditorIntegration(unittest.TestCase):
    """Integration tests for SovereigntyAuditor."""
    
    def test_full_audit_workflow(self):
        """Test complete audit workflow."""
        # Create temporary repository structure
        test_dir = tempfile.mkdtemp()
        try:
            auditor = SovereigntyAuditor(test_dir)
            
            # Create declaration files
            for filename in auditor.REQUIRED_FILES:
                file_path = Path(test_dir) / filename
                with open(file_path, 'w') as f:
                    f.write("Declaration file content")
            
            # Create source files with QCAL markers
            src_dir = Path(test_dir) / 'src'
            src_dir.mkdir()
            
            for i in range(5):
                file_path = src_dir / f'module{i}.py'
                with open(file_path, 'w') as f:
                    f.write(f'# f₀ = 141.7001 Hz\n# JMMB Ψ✧\ndef function{i}():\n    pass')
            
            # Run audit
            auditor.scan_repository()
            score = auditor.calculate_sovereignty_score()
            
            # Verify results
            self.assertGreater(score, 0)
            self.assertGreater(len(auditor.results['qcal_marked_files']), 0)
            
            # Save report
            auditor.save_report('test_report.json')
            self.assertTrue((Path(test_dir) / 'test_report.json').exists())
            
        finally:
            import shutil
            shutil.rmtree(test_dir, ignore_errors=True)


def run_tests():
    """Run all tests."""
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test cases
    suite.addTests(loader.loadTestsFromTestCase(TestSovereigntyAuditor))
    suite.addTests(loader.loadTestsFromTestCase(TestSovereigntyAuditorIntegration))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    return 0 if result.wasSuccessful() else 1


if __name__ == '__main__':
    exit(run_tests())
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
