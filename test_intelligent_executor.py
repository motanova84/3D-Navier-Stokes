"""
Test Suite for Intelligent Executor and Parametric Sweep Orchestrator

Tests cover:
- Resource detection
- Package management
- Priority assignment
- Cost estimation
- Package execution
- Intelligent selection
"""

import unittest
import json
import os
import shutil
import tempfile
from pathlib import Path
import sys

# Add parent directory to path for imports
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

# Import modules to test
from parametric_sweep_orchestrator import (
    load_package,
    assign_priority,
    estimate_computational_cost,
    run_package,
    create_sample_packages
)
from intelligent_executor import (
    get_available_resources,
    can_run_package,
    get_next_package_to_run
)


class TestParametricSweepOrchestrator(unittest.TestCase):
    """Test cases for parametric sweep orchestrator"""
    
    def setUp(self):
        """Create temporary directory for test packages"""
        self.test_dir = tempfile.mkdtemp()
        self.packages_dir = os.path.join(self.test_dir, 'packages')
        self.results_dir = os.path.join(self.test_dir, 'results')
        os.makedirs(self.packages_dir)
        os.makedirs(self.results_dir)
    
    def tearDown(self):
        """Clean up temporary directory"""
        if os.path.exists(self.test_dir):
            shutil.rmtree(self.test_dir)
    
    def test_create_sample_packages(self):
        """Test sample package creation"""
        create_sample_packages(n_packages=5, output_dir=self.packages_dir)
        
        # Check that packages were created
        package_files = list(Path(self.packages_dir).glob('package_*.json'))
        self.assertEqual(len(package_files), 5)
        
        # Check that priority summary was created
        summary_file = Path(self.packages_dir) / 'priority_summary.json'
        self.assertTrue(summary_file.exists())
        
        with open(summary_file, 'r') as f:
            summary = json.load(f)
        
        # Check priority structure
        self.assertIn('HIGH', summary)
        self.assertIn('MEDIUM', summary)
        self.assertIn('LOW', summary)
        
        # Total packages should equal n_packages
        total = len(summary['HIGH']) + len(summary['MEDIUM']) + len(summary['LOW'])
        self.assertEqual(total, 5)
    
    def test_load_package(self):
        """Test package loading"""
        # Create a test package
        test_package = {
            'package_id': 0,
            'parameters': {
                'reynolds': 1000,
                'resolution': 64,
                'viscosity': 1e-3
            }
        }
        
        package_file = Path(self.packages_dir) / 'package_0000.json'
        with open(package_file, 'w') as f:
            json.dump(test_package, f)
        
        # Load and verify
        loaded = load_package(0, self.packages_dir)
        self.assertEqual(loaded['package_id'], 0)
        self.assertEqual(loaded['parameters']['reynolds'], 1000)
    
    def test_load_package_not_found(self):
        """Test loading non-existent package"""
        with self.assertRaises(FileNotFoundError):
            load_package(999, self.packages_dir)
    
    def test_assign_priority_high(self):
        """Test high priority assignment"""
        package = {
            'parameters': {
                'reynolds': 2000,
                'resolution': 128,
                'viscosity': 1e-3
            }
        }
        priority = assign_priority(package)
        self.assertEqual(priority, 'HIGH')
    
    def test_assign_priority_low(self):
        """Test low priority assignment"""
        package = {
            'parameters': {
                'reynolds': 50,
                'resolution': 16,
                'viscosity': 1e-3
            }
        }
        priority = assign_priority(package)
        self.assertEqual(priority, 'LOW')
    
    def test_assign_priority_medium(self):
        """Test medium priority assignment"""
        package = {
            'parameters': {
                'reynolds': 500,
                'resolution': 64,
                'viscosity': 1e-3
            }
        }
        priority = assign_priority(package)
        self.assertEqual(priority, 'MEDIUM')
    
    def test_estimate_computational_cost(self):
        """Test computational cost estimation"""
        package = {
            'parameters': {
                'reynolds': 1000,
                'resolution': 64,
                'viscosity': 1e-3,
                'timesteps': 1000
            }
        }
        
        cost = estimate_computational_cost(package)
        
        # Check that all required fields are present
        self.assertIn('time_hours', cost)
        self.assertIn('memory_gb', cost)
        self.assertIn('disk_gb', cost)
        
        # Check that values are positive
        self.assertGreater(cost['time_hours'], 0)
        self.assertGreater(cost['memory_gb'], 0)
        self.assertGreater(cost['disk_gb'], 0)
        
        # Check scaling: larger resolution should require more resources
        package_large = {
            'parameters': {
                'reynolds': 1000,
                'resolution': 128,
                'viscosity': 1e-3,
                'timesteps': 1000
            }
        }
        cost_large = estimate_computational_cost(package_large)
        
        self.assertGreater(cost_large['memory_gb'], cost['memory_gb'])
        self.assertGreater(cost_large['time_hours'], cost['time_hours'])
    
    def test_run_package(self):
        """Test package execution"""
        # Create a test package
        test_package = {
            'package_id': 0,
            'parameters': {
                'reynolds': 1000,
                'resolution': 64,
                'viscosity': 1e-3,
                'timesteps': 100
            }
        }
        
        package_file = Path(self.packages_dir) / 'package_0000.json'
        with open(package_file, 'w') as f:
            json.dump(test_package, f)
        
        # Run package
        result = run_package(0, output_dir=self.results_dir, packages_dir=self.packages_dir)
        
        # Check result structure
        self.assertEqual(result['package_id'], 0)
        self.assertEqual(result['status'], 'completed')
        self.assertIn('execution_time', result)
        self.assertIn('results', result)
        
        # Check that result file was created
        result_file = Path(self.results_dir) / 'results_package_0000.json'
        self.assertTrue(result_file.exists())


class TestIntelligentExecutor(unittest.TestCase):
    """Test cases for intelligent executor"""
    
    def setUp(self):
        """Create temporary directory for test packages"""
        self.test_dir = tempfile.mkdtemp()
        self.packages_dir = os.path.join(self.test_dir, 'packages')
        self.results_dir = os.path.join(self.test_dir, 'results')
        os.makedirs(self.packages_dir)
        os.makedirs(self.results_dir)
        
        # Create sample packages for testing
        create_sample_packages(n_packages=5, output_dir=self.packages_dir)
    
    def tearDown(self):
        """Clean up temporary directory"""
        if os.path.exists(self.test_dir):
            shutil.rmtree(self.test_dir)
    
    def test_get_available_resources(self):
        """Test resource detection"""
        resources = get_available_resources()
        
        # Check that all required fields are present
        self.assertIn('cpu_cores', resources)
        self.assertIn('cpu_usage', resources)
        self.assertIn('memory_available_gb', resources)
        self.assertIn('disk_available_gb', resources)
        self.assertIn('cpu_free_cores', resources)
        
        # Check that values are reasonable
        self.assertGreater(resources['cpu_cores'], 0)
        self.assertGreaterEqual(resources['cpu_usage'], 0)
        self.assertLessEqual(resources['cpu_usage'], 100)
        self.assertGreater(resources['memory_available_gb'], 0)
        self.assertGreater(resources['disk_available_gb'], 0)
    
    def test_can_run_package(self):
        """Test package resource checking"""
        resources = get_available_resources()
        
        # Should be able to run package 0 (assuming system has minimal resources)
        can_run, checks = can_run_package(0, resources, self.packages_dir)
        
        # Check that checks dictionary has required keys
        self.assertIn('memory', checks)
        self.assertIn('disk', checks)
        self.assertIn('cpu', checks)
        
        # can_run should be boolean
        self.assertIsInstance(can_run, bool)
    
    def test_get_next_package_to_run(self):
        """Test intelligent package selection"""
        # This should select a package based on priority
        pkg_id, pkg_info = get_next_package_to_run(
            packages_dir=self.packages_dir,
            results_dir=self.results_dir
        )
        
        if pkg_id is not None:
            # Check that package ID is valid
            self.assertIsInstance(pkg_id, int)
            self.assertGreaterEqual(pkg_id, 0)
            
            # Check that package info has required fields
            self.assertIn('package_id', pkg_info)
            self.assertIn('estimated_time_hours', pkg_info)
            self.assertIn('estimated_memory_gb', pkg_info)
    
    def test_get_next_package_skips_completed(self):
        """Test that completed packages are skipped"""
        # Run package 0
        run_package(0, output_dir=self.results_dir, packages_dir=self.packages_dir)
        
        # Get next package
        pkg_id, pkg_info = get_next_package_to_run(
            packages_dir=self.packages_dir,
            results_dir=self.results_dir
        )
        
        # Should not return package 0
        if pkg_id is not None:
            self.assertNotEqual(pkg_id, 0)


class TestIntegration(unittest.TestCase):
    """Integration tests for the complete workflow"""
    
    def setUp(self):
        """Create temporary directory for test packages"""
        self.test_dir = tempfile.mkdtemp()
        self.packages_dir = os.path.join(self.test_dir, 'packages')
        self.results_dir = os.path.join(self.test_dir, 'results')
        os.makedirs(self.packages_dir)
        os.makedirs(self.results_dir)
    
    def tearDown(self):
        """Clean up temporary directory"""
        if os.path.exists(self.test_dir):
            shutil.rmtree(self.test_dir)
    
    def test_complete_workflow(self):
        """Test complete workflow: create, select, execute"""
        # Create packages
        create_sample_packages(n_packages=3, output_dir=self.packages_dir)
        
        # Select and execute packages
        executed = []
        for i in range(3):
            pkg_id, pkg_info = get_next_package_to_run(
                packages_dir=self.packages_dir,
                results_dir=self.results_dir
            )
            
            if pkg_id is None:
                break
            
            result = run_package(pkg_id, output_dir=self.results_dir, 
                               packages_dir=self.packages_dir)
            executed.append(pkg_id)
        
        # Should have executed some packages
        self.assertGreater(len(executed), 0)
        
        # All executed packages should have result files
        for pkg_id in executed:
            result_file = Path(self.results_dir) / f"results_package_{pkg_id:04d}.json"
            self.assertTrue(result_file.exists())


if __name__ == '__main__':
    unittest.main()
