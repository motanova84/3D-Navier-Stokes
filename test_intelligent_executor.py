"""
Test Suite for Intelligent Executor and Parametric Sweep Orchestrator

This module contains tests for the intelligent executor system.
"""

import unittest
import json
import shutil
import tempfile
from pathlib import Path
import sys
import os

# Add parent directory to path for imports
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from parametric_sweep_orchestrator import (
    load_package,
    assign_priority,
    estimate_computational_cost,
    run_package,
    create_example_packages
)

from intelligent_executor import (
    get_available_resources,
    can_run_package,
    get_next_package_to_run
)


class TestParametricSweepOrchestrator(unittest.TestCase):
    """Test cases for the parametric sweep orchestrator"""
    
    def setUp(self):
        """Create temporary directories for testing"""
        self.test_dir = tempfile.mkdtemp()
        self.packages_dir = os.path.join(self.test_dir, 'packages')
        self.results_dir = os.path.join(self.test_dir, 'results')
        os.makedirs(self.packages_dir, exist_ok=True)
        os.makedirs(self.results_dir, exist_ok=True)
        
        # Create test packages
        create_example_packages(packages_dir=self.packages_dir, n_packages=5)
    
    def tearDown(self):
        """Clean up temporary directories"""
        if os.path.exists(self.test_dir):
            shutil.rmtree(self.test_dir)
    
    def test_create_example_packages(self):
        """Test that example packages are created correctly"""
        # Check packages directory exists
        self.assertTrue(Path(self.packages_dir).exists())
        
        # Check priority summary exists
        priority_file = Path(self.packages_dir) / 'priority_summary.json'
        self.assertTrue(priority_file.exists())
        
        # Check individual packages exist
        for i in range(1, 6):
            package_file = Path(self.packages_dir) / f'package_{i:04d}.json'
            self.assertTrue(package_file.exists())
    
    def test_load_package(self):
        """Test loading a package"""
        package = load_package(1, packages_dir=self.packages_dir)
        
        # Check package structure
        self.assertIn('package_id', package)
        self.assertIn('name', package)
        self.assertIn('parameters', package)
        self.assertEqual(package['package_id'], 1)
    
    def test_assign_priority(self):
        """Test priority assignment"""
        # Load package and assign priority
        package = load_package(1, packages_dir=self.packages_dir)
        priority = assign_priority(package)
        
        # Priority should be one of the valid values
        self.assertIn(priority, ['HIGH', 'MEDIUM', 'LOW'])
    
    def test_estimate_computational_cost(self):
        """Test cost estimation"""
        package = load_package(1, packages_dir=self.packages_dir)
        cost = estimate_computational_cost(package)
        
        # Check cost structure
        self.assertIn('memory_gb', cost)
        self.assertIn('disk_gb', cost)
        self.assertIn('time_hours', cost)
        
        # Check values are reasonable
        self.assertGreater(cost['memory_gb'], 0)
        self.assertGreater(cost['disk_gb'], 0)
        self.assertGreater(cost['time_hours'], 0)
    
    def test_run_package(self):
        """Test running a package"""
        result = run_package(1, 
                           output_dir=self.results_dir,
                           packages_dir=self.packages_dir)
        
        # Check result structure
        self.assertIn('package_id', result)
        self.assertIn('status', result)
        self.assertEqual(result['status'], 'completed')
        self.assertEqual(result['package_id'], 1)
        
        # Check result file was created
        result_file = Path(self.results_dir) / 'results_package_0001.json'
        self.assertTrue(result_file.exists())


class TestIntelligentExecutor(unittest.TestCase):
    """Test cases for the intelligent executor"""
    
    def setUp(self):
        """Create temporary directories for testing"""
        self.test_dir = tempfile.mkdtemp()
        self.packages_dir = os.path.join(self.test_dir, 'packages')
        self.results_dir = os.path.join(self.test_dir, 'results')
        os.makedirs(self.packages_dir, exist_ok=True)
        os.makedirs(self.results_dir, exist_ok=True)
        
        # Create test packages
        create_example_packages(packages_dir=self.packages_dir, n_packages=5)
    
    def tearDown(self):
        """Clean up temporary directories"""
        if os.path.exists(self.test_dir):
            shutil.rmtree(self.test_dir)
    
    def test_get_available_resources(self):
        """Test resource detection"""
        resources = get_available_resources()
        
        # Check resource structure
        self.assertIn('cpu_cores', resources)
        self.assertIn('cpu_usage', resources)
        self.assertIn('memory_available_gb', resources)
        self.assertIn('disk_available_gb', resources)
        self.assertIn('cpu_free_cores', resources)
        
        # Check values are reasonable
        self.assertGreater(resources['cpu_cores'], 0)
        self.assertGreaterEqual(resources['cpu_usage'], 0)
        self.assertLessEqual(resources['cpu_usage'], 100)
        self.assertGreater(resources['memory_available_gb'], 0)
        self.assertGreater(resources['disk_available_gb'], 0)
    
    def test_can_run_package(self):
        """Test checking if a package can run"""
        resources = get_available_resources()
        can_run, checks = can_run_package(1, resources)
        
        # Check return types
        self.assertIsInstance(can_run, bool)
        self.assertIsInstance(checks, dict)
        
        # Check checks structure
        self.assertIn('memory', checks)
        self.assertIn('disk', checks)
        self.assertIn('cpu', checks)
    
    def test_get_next_package_to_run(self):
        """Test selecting next package to run"""
        pkg_id, pkg_info = get_next_package_to_run(
            packages_dir=self.packages_dir,
            results_dir=self.results_dir
        )
        
        # Should return a valid package
        self.assertIsNotNone(pkg_id)
        self.assertIsNotNone(pkg_info)
        self.assertIsInstance(pkg_id, int)
        self.assertIsInstance(pkg_info, dict)
    
    def test_get_next_package_respects_completion(self):
        """Test that completed packages are skipped"""
        # Run first package
        run_package(1, 
                   output_dir=self.results_dir,
                   packages_dir=self.packages_dir)
        
        # Get next package
        pkg_id, pkg_info = get_next_package_to_run(
            packages_dir=self.packages_dir,
            results_dir=self.results_dir
        )
        
        # Should not be package 1
        self.assertNotEqual(pkg_id, 1)
    
    def test_priority_order(self):
        """Test that HIGH priority packages are selected first"""
        # Find HIGH priority packages from priority_summary
        with open(f'{self.packages_dir}/priority_summary.json', 'r') as f:
            priorities = json.load(f)
        
        high_priority_ids = [pkg['package_id'] for pkg in priorities['HIGH']]
        
        if high_priority_ids:
            # Get next package (should be HIGH priority)
            pkg_id, pkg_info = get_next_package_to_run(
                packages_dir=self.packages_dir,
                results_dir=self.results_dir
            )
            
            # Should be a HIGH priority package
            self.assertIn(pkg_id, high_priority_ids)


class TestIntegration(unittest.TestCase):
    """Integration tests for the complete system"""
    
    def setUp(self):
        """Create temporary directories for testing"""
        self.test_dir = tempfile.mkdtemp()
        self.packages_dir = os.path.join(self.test_dir, 'packages')
        self.results_dir = os.path.join(self.test_dir, 'results')
        os.makedirs(self.packages_dir, exist_ok=True)
        os.makedirs(self.results_dir, exist_ok=True)
        
        # Create test packages
        create_example_packages(packages_dir=self.packages_dir, n_packages=3)
    
    def tearDown(self):
        """Clean up temporary directories"""
        if os.path.exists(self.test_dir):
            shutil.rmtree(self.test_dir)
    
    def test_complete_workflow(self):
        """Test complete workflow: select, run, verify"""
        # Select package
        pkg_id, pkg_info = get_next_package_to_run(
            packages_dir=self.packages_dir,
            results_dir=self.results_dir
        )
        
        self.assertIsNotNone(pkg_id)
        
        # Run package
        result = run_package(
            pkg_id,
            output_dir=self.results_dir,
            packages_dir=self.packages_dir
        )
        
        self.assertEqual(result['status'], 'completed')
        
        # Verify result file exists
        result_file = Path(self.results_dir) / f'results_package_{pkg_id:04d}.json'
        self.assertTrue(result_file.exists())
        
        # Load and verify result
        with open(result_file, 'r') as f:
            saved_result = json.load(f)
        
        self.assertEqual(saved_result['package_id'], pkg_id)
        self.assertEqual(saved_result['status'], 'completed')


if __name__ == '__main__':
    unittest.main()
