#!/usr/bin/env python3
"""
Test suite for parametric_sweep_orchestrator.py

Tests the parametric sweep orchestrator functionality including:
- Parameter package creation
- Cost estimation
- Priority assignment
- Package save/load
- Single simulation execution
"""

import unittest
import tempfile
import shutil
import os
import json
from pathlib import Path

# Import modules to test
from parametric_sweep_orchestrator import (
    create_parameter_packages,
    estimate_computational_cost,
    assign_priority,
    save_packages,
    load_package,
    run_single_simulation
)


class TestParametricSweepOrchestrator(unittest.TestCase):
    """Test cases for parametric sweep orchestrator"""
    
    def setUp(self):
        """Create temporary directory for testing"""
        self.tmpdir = tempfile.mkdtemp()
    
    def tearDown(self):
        """Clean up temporary directory"""
        shutil.rmtree(self.tmpdir, ignore_errors=True)
    
    def test_create_parameter_packages(self):
        """Test parameter package creation"""
        packages = create_parameter_packages(package_size=5)
        
        # Check that packages were created
        self.assertGreater(len(packages), 0)
        
        # Check package structure
        pkg = packages[0]
        self.assertIn('id', pkg)
        self.assertIn('size', pkg)
        self.assertIn('parameters', pkg)
        self.assertIn('status', pkg)
        self.assertIn('created_at', pkg)
        
        # Check parameters structure
        params = pkg['parameters'][0]
        self.assertIn('f0', params)
        self.assertIn('Re', params)
        self.assertIn('nu', params)
        self.assertIn('N', params)
        self.assertIn('T_max', params)
        self.assertIn('L', params)
        self.assertIn('U', params)
        
        # Check parameter ranges
        self.assertGreaterEqual(params['f0'], 100.0)
        self.assertLessEqual(params['f0'], 1000.0)
        self.assertGreaterEqual(params['Re'], 100.0)
        self.assertLessEqual(params['Re'], 1000.0)
        self.assertIn(params['N'], [32, 64, 128])
    
    def test_estimate_computational_cost(self):
        """Test computational cost estimation"""
        packages = create_parameter_packages(package_size=5)
        pkg = packages[0]
        
        cost = estimate_computational_cost(pkg)
        
        # Check cost structure
        self.assertIn('time_hours', cost)
        self.assertIn('memory_gb', cost)
        self.assertIn('disk_gb', cost)
        self.assertIn('cpu_cores', cost)
        
        # Check that costs are positive
        self.assertGreater(cost['time_hours'], 0)
        self.assertGreater(cost['memory_gb'], 0)
        self.assertGreater(cost['disk_gb'], 0)
        self.assertEqual(cost['cpu_cores'], 1)
    
    def test_assign_priority(self):
        """Test priority assignment"""
        packages = create_parameter_packages(package_size=5)
        
        priorities = [assign_priority(pkg) for pkg in packages]
        
        # Check that priorities are valid
        for priority in priorities:
            self.assertIn(priority, ['HIGH', 'MEDIUM', 'LOW'])
        
        # Check that HIGH priority exists (should have packages near f0=141.7 Hz)
        self.assertIn('HIGH', priorities)
    
    def test_save_and_load_packages(self):
        """Test package save and load functionality"""
        packages = create_parameter_packages(package_size=5)
        
        # Save packages
        output_dir = save_packages(packages, output_dir=self.tmpdir)
        
        # Check that files were created
        self.assertTrue(os.path.exists(f'{output_dir}/metadata.json'))
        self.assertTrue(os.path.exists(f'{output_dir}/priority_summary.json'))
        
        # Check that package files exist
        for pkg in packages:
            pkg_file = f"{output_dir}/package_{pkg['id']:04d}.json"
            self.assertTrue(os.path.exists(pkg_file))
        
        # Test loading a package
        loaded_pkg = load_package(0, input_dir=output_dir)
        
        # Check loaded package structure
        self.assertEqual(loaded_pkg['id'], 0)
        self.assertIn('size', loaded_pkg)
        self.assertIn('parameters', loaded_pkg)
        
        # Check that loaded package matches original
        original_pkg = packages[0]
        self.assertEqual(loaded_pkg['id'], original_pkg['id'])
        self.assertEqual(loaded_pkg['size'], original_pkg['size'])
    
    def test_run_single_simulation(self):
        """Test single simulation execution with minimal parameters"""
        # Create a minimal parameter set for quick testing
        params = {
            'f0': 141.7,
            'Re': 100.0,
            'nu': 0.0628,
            'N': 8,  # Very small for quick test
            'T_max': 0.01,  # Very short time
            'L': 6.28,
            'U': 1.0
        }
        
        # Run simulation
        result = run_single_simulation(params)
        
        # Check result structure
        self.assertIn('status', result)
        self.assertIn('params', result)
        self.assertIn('completed_at', result)
        
        # Check that simulation succeeded or failed gracefully
        if result['status'] == 'success':
            self.assertIn('results', result)
            sim_results = result['results']
            
            # Check simulation results structure
            self.assertIn('parameters', sim_results)
            self.assertIn('energy', sim_results)
            self.assertIn('enstrophy', sim_results)
            self.assertIn('detected_frequency_Hz', sim_results)
            self.assertIn('blow_up_detected', sim_results)
        elif result['status'] == 'failed':
            self.assertIn('error', result)


if __name__ == '__main__':
    unittest.main()
