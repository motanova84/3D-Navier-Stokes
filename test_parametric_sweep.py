#!/usr/bin/env python3
"""
Test suite for parametric sweep functionality
"""

import os
import sys
import json
import tempfile
import shutil
import unittest
from pathlib import Path


class TestParametricSweep(unittest.TestCase):
    """Test parametric sweep functionality"""
    
    def setUp(self):
        """Set up test environment"""
        self.test_dir = tempfile.mkdtemp()
        self.package_dir = os.path.join(self.test_dir, "test_packages")
        os.makedirs(self.package_dir, exist_ok=True)
    
    def tearDown(self):
        """Clean up test environment"""
        if os.path.exists(self.test_dir):
            shutil.rmtree(self.test_dir)
    
    def test_orchestrator_import(self):
        """Test that orchestrator can be imported"""
        try:
            import parametric_sweep_orchestrator
            self.assertTrue(hasattr(parametric_sweep_orchestrator, 'ParametricSweepOrchestrator'))
        except ImportError as e:
            self.fail(f"Failed to import orchestrator: {e}")
    
    def test_run_package_import(self):
        """Test that run_package can be imported"""
        try:
            import run_package
            self.assertTrue(hasattr(run_package, 'PackageRunner'))
        except ImportError as e:
            self.fail(f"Failed to import run_package: {e}")
    
    def test_intelligent_executor_import(self):
        """Test that intelligent_executor can be imported"""
        try:
            import intelligent_executor
            self.assertTrue(hasattr(intelligent_executor, 'IntelligentExecutor'))
        except ImportError as e:
            self.fail(f"Failed to import intelligent_executor: {e}")
    
    def test_orchestrator_package_generation(self):
        """Test package generation"""
        from parametric_sweep_orchestrator import ParametricSweepOrchestrator
        
        orchestrator = ParametricSweepOrchestrator(output_dir=self.package_dir)
        orchestrator.create_packages()
        
        # Check that packages were created
        self.assertTrue(len(orchestrator.packages) > 0)
        
        # Check that files exist
        self.assertTrue(os.path.exists(os.path.join(self.package_dir, "priority_summary.json")))
        self.assertTrue(os.path.exists(os.path.join(self.package_dir, "package_index.json")))
        self.assertTrue(os.path.exists(os.path.join(self.package_dir, "package_0000.json")))
    
    def test_package_structure(self):
        """Test that generated packages have correct structure"""
        from parametric_sweep_orchestrator import ParametricSweepOrchestrator
        
        orchestrator = ParametricSweepOrchestrator(output_dir=self.package_dir)
        orchestrator.create_packages()
        
        # Load first package
        with open(os.path.join(self.package_dir, "package_0000.json"), 'r') as f:
            package = json.load(f)
        
        # Check required fields
        required_fields = ['id', 'reynolds', 'grid_size', 'time_step', 'viscosity', 'priority', 'status']
        for field in required_fields:
            self.assertIn(field, package, f"Missing required field: {field}")
    
    def test_priority_levels(self):
        """Test that packages have valid priority levels"""
        from parametric_sweep_orchestrator import ParametricSweepOrchestrator
        
        orchestrator = ParametricSweepOrchestrator(output_dir=self.package_dir)
        orchestrator.create_packages()
        
        valid_priorities = ['HIGH', 'MEDIUM', 'LOW']
        for package in orchestrator.packages:
            self.assertIn(package['priority'], valid_priorities)
    
    def test_package_runner_creation(self):
        """Test that PackageRunner can be instantiated"""
        from run_package import PackageRunner
        
        runner = PackageRunner(package_dir=self.package_dir)
        self.assertEqual(runner.package_dir, self.package_dir)
    
    def test_intelligent_executor_creation(self):
        """Test that IntelligentExecutor can be instantiated"""
        from intelligent_executor import IntelligentExecutor
        
        executor = IntelligentExecutor(package_dir=self.package_dir)
        self.assertEqual(executor.package_dir, self.package_dir)
    
    def test_scripts_are_executable(self):
        """Test that main scripts are executable"""
        scripts = [
            'quickstart_parametric_sweep.sh',
            'batch_execution.sh',
            'parametric_sweep_orchestrator.py',
            'run_package.py',
            'intelligent_executor.py'
        ]
        
        for script in scripts:
            script_path = os.path.join(os.path.dirname(__file__), script)
            self.assertTrue(
                os.path.exists(script_path),
                f"Script not found: {script}"
            )
            # Check if file is executable (on Unix-like systems)
            if os.name != 'nt':  # Not Windows
                self.assertTrue(
                    os.access(script_path, os.X_OK),
                    f"Script not executable: {script}"
                )


def main():
    """Run tests"""
    # Change to repository directory
    repo_dir = os.path.dirname(os.path.abspath(__file__))
    os.chdir(repo_dir)
    
    # Run tests
    unittest.main(argv=[''], exit=False, verbosity=2)


if __name__ == "__main__":
    main()
