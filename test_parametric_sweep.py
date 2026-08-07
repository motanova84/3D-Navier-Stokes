#!/usr/bin/env python3
"""
Tests for Parametric Sweep Orchestrator and Package Runner

Validates the functionality of:
- Package creation and loading
- Priority assignment
- Computational cost estimation
- Package execution interface
"""

import sys
import os
import json
import shutil
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent))

from parametric_sweep_orchestrator import (
    load_package,
    assign_priority,
    estimate_computational_cost,
    create_example_packages
)


def test_create_example_packages():
    """Test creating example packages"""
    print("Testing create_example_packages...")
    
    test_dir = 'test_packages_temp'
    try:
        # Clean up if exists
        if Path(test_dir).exists():
            shutil.rmtree(test_dir)
        
        # Create packages
        package_ids = create_example_packages(
            output_dir=test_dir,
            n_packages=3,
            sims_per_package=5
        )
        
        # Verify packages were created
        assert len(package_ids) == 3, f"Expected 3 packages, got {len(package_ids)}"
        
        # Verify files exist
        for pkg_id in package_ids:
            pkg_file = Path(test_dir) / f'package_{pkg_id:04d}.json'
            assert pkg_file.exists(), f"Package file {pkg_file} not found"
            
            # Verify JSON is valid
            with open(pkg_file, 'r') as f:
                pkg = json.load(f)
                assert pkg['id'] == pkg_id, f"Package ID mismatch: {pkg['id']} != {pkg_id}"
                assert pkg['size'] == 5, f"Expected 5 simulations, got {pkg['size']}"
                assert len(pkg['parameters']) == 5, f"Expected 5 parameters, got {len(pkg['parameters'])}"
        
        print("✓ Package creation test passed")
        return True
        
    except Exception as e:
        print(f"✗ Package creation test failed: {e}")
        return False
        
    finally:
        # Clean up
        if Path(test_dir).exists():
            shutil.rmtree(test_dir)


def test_load_package():
    """Test loading a package"""
    print("\nTesting load_package...")
    
    test_dir = 'test_packages_temp'
    try:
        # Create test packages
        create_example_packages(
            output_dir=test_dir,
            n_packages=2,
            sims_per_package=5
        )
        
        # Test loading valid package
        package = load_package(0, packages_dir=test_dir)
        assert package['id'] == 0, "Package ID should be 0"
        assert package['size'] == 5, "Package size should be 5"
        assert 'parameters' in package, "Package should have parameters"
        assert 'created' in package, "Package should have created timestamp"
        
        # Test loading non-existent package
        try:
            load_package(99, packages_dir=test_dir)
            print("✗ Should have raised FileNotFoundError")
            return False
        except FileNotFoundError:
            pass  # Expected
        
        print("✓ Package loading test passed")
        return True
        
    except Exception as e:
        print(f"✗ Package loading test failed: {e}")
        return False
        
    finally:
        # Clean up
        if Path(test_dir).exists():
            shutil.rmtree(test_dir)


def test_assign_priority():
    """Test priority assignment"""
    print("\nTesting assign_priority...")
    
    try:
        # Test HIGH priority: critical frequency + high Reynolds
        high_priority_package = {
            'parameters': [
                {'f0': 141.7, 'Re': 15000, 'N': 128},
                {'f0': 142.0, 'Re': 12000, 'N': 64}
            ]
        }
        priority = assign_priority(high_priority_package)
        assert priority == "HIGH", f"Expected HIGH priority, got {priority}"
        
        # Test MEDIUM priority: intermediate parameters
        medium_priority_package = {
            'parameters': [
                {'f0': 150.0, 'Re': 5000, 'N': 64},
                {'f0': 100.0, 'Re': 2000, 'N': 32}
            ]
        }
        priority = assign_priority(medium_priority_package)
        assert priority == "MEDIUM", f"Expected MEDIUM priority, got {priority}"
        
        # Test LOW priority: low parameters
        low_priority_package = {
            'parameters': [
                {'f0': 50.0, 'Re': 500, 'N': 32},
                {'f0': 60.0, 'Re': 600, 'N': 32}
            ]
        }
        priority = assign_priority(low_priority_package)
        assert priority == "LOW", f"Expected LOW priority, got {priority}"
        
        # Test empty package
        empty_package = {'parameters': []}
        priority = assign_priority(empty_package)
        assert priority == "LOW", f"Empty package should have LOW priority, got {priority}"
        
        print("✓ Priority assignment test passed")
        return True
        
    except Exception as e:
        print(f"✗ Priority assignment test failed: {e}")
        return False


def test_estimate_computational_cost():
    """Test computational cost estimation"""
    print("\nTesting estimate_computational_cost...")
    
    try:
        # Test with typical parameters
        package = {
            'parameters': [
                {'f0': 141.7, 'Re': 5000, 'N': 64},
                {'f0': 150.0, 'Re': 10000, 'N': 128},
            ]
        }
        
        cost = estimate_computational_cost(package)
        
        # Verify all expected fields are present
        assert 'time_hours' in cost, "Missing time_hours"
        assert 'time_minutes' in cost, "Missing time_minutes"
        assert 'memory_gb' in cost, "Missing memory_gb"
        assert 'disk_gb' in cost, "Missing disk_gb"
        assert 'n_simulations' in cost, "Missing n_simulations"
        
        # Verify values are reasonable
        assert cost['n_simulations'] == 2, "Should have 2 simulations"
        assert cost['time_hours'] > 0, "Time should be positive"
        assert cost['memory_gb'] > 0, "Memory should be positive"
        assert cost['disk_gb'] > 0, "Disk should be positive"
        assert cost['time_minutes'] == cost['time_hours'] * 60, "Time conversion mismatch"
        
        # Test scaling: higher N should increase cost
        package_small = {
            'parameters': [{'f0': 100, 'Re': 1000, 'N': 32}]
        }
        package_large = {
            'parameters': [{'f0': 100, 'Re': 1000, 'N': 128}]
        }
        
        cost_small = estimate_computational_cost(package_small)
        cost_large = estimate_computational_cost(package_large)
        
        assert cost_large['time_hours'] > cost_small['time_hours'], \
            "Larger N should take more time"
        assert cost_large['memory_gb'] > cost_small['memory_gb'], \
            "Larger N should require more memory"
        
        print("✓ Cost estimation test passed")
        return True
        
    except Exception as e:
        print(f"✗ Cost estimation test failed: {e}")
        return False


def test_package_structure():
    """Test package JSON structure"""
    print("\nTesting package structure...")
    
    test_dir = 'test_packages_temp'
    try:
        # Create test package
        create_example_packages(
            output_dir=test_dir,
            n_packages=1,
            sims_per_package=3
        )
        
        # Load and verify structure
        package = load_package(0, packages_dir=test_dir)
        
        # Check required top-level fields
        required_fields = ['id', 'size', 'parameters', 'created']
        for field in required_fields:
            assert field in package, f"Missing required field: {field}"
        
        # Check parameter structure
        for i, params in enumerate(package['parameters']):
            required_param_fields = ['f0', 'Re', 'N', 'nu', 'M', 'a', 'alpha']
            for field in required_param_fields:
                assert field in params, f"Parameter {i} missing field: {field}"
            
            # Check value types and ranges
            assert isinstance(params['f0'], (int, float)), "f0 should be numeric"
            assert params['f0'] > 0, "f0 should be positive"
            assert isinstance(params['Re'], (int, float)), "Re should be numeric"
            assert params['Re'] > 0, "Re should be positive"
            assert isinstance(params['N'], int), "N should be integer"
            assert params['N'] > 0, "N should be positive"
        
        print("✓ Package structure test passed")
        return True
        
    except Exception as e:
        print(f"✗ Package structure test failed: {e}")
        return False
        
    finally:
        # Clean up
        if Path(test_dir).exists():
            shutil.rmtree(test_dir)


def run_all_tests():
    """Run all tests"""
    print("="*70)
    print("  PARAMETRIC SWEEP ORCHESTRATOR - TEST SUITE")
    print("="*70)
    
    tests = [
        test_create_example_packages,
        test_load_package,
        test_assign_priority,
        test_estimate_computational_cost,
        test_package_structure,
    ]
    
    results = []
    for test in tests:
        results.append(test())
    
    print("\n" + "="*70)
    print("  TEST SUMMARY")
    print("="*70)
    passed = sum(results)
    total = len(results)
    print(f"Passed: {passed}/{total}")
    
    if passed == total:
        print("✓ All tests passed!")
        return 0
    else:
        print(f"✗ {total - passed} test(s) failed")
        return 1


if __name__ == "__main__":
    sys.exit(run_all_tests())
