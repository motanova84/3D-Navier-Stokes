#!/usr/bin/env python3
"""
Tests for the batch execution system

Basic tests to validate the parametric sweep batch execution functionality
"""

import sys
import os
import json
import subprocess
from pathlib import Path
import shutil

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent))


def setup_test_environment():
    """Create a clean test environment"""
    print("Setting up test environment...")
    
    test_dirs = [
        'test_parametric_sweep_packages',
        'test_parametric_sweep_results',
        'test_parametric_sweep_logs'
    ]
    
    # Clean up any existing test directories
    for dir_name in test_dirs:
        if Path(dir_name).exists():
            shutil.rmtree(dir_name)
    
    # Create test package directory
    pkg_dir = Path('test_parametric_sweep_packages')
    pkg_dir.mkdir()
    
    # Create test priority summary
    priority_summary = {
        "HIGH": [
            {
                "package_id": 1,
                "priority": "HIGH",
                "description": "Test package 1",
                "parameters": {"Re": [100]}
            }
        ],
        "MEDIUM": [],
        "LOW": []
    }
    
    with open(pkg_dir / 'priority_summary.json', 'w') as f:
        json.dump(priority_summary, f, indent=2)
    
    # Create test package config
    package_config = {
        "package_id": 1,
        "Re": 100,
        "dt": 0.01,
        "T_final": 0.1,  # Short duration for testing
        "grid_size": [16, 16, 16],
        "priority": "HIGH"
    }
    
    with open(pkg_dir / 'package_0001.json', 'w') as f:
        json.dump(package_config, f, indent=2)
    
    print("✓ Test environment created")
    return True


def cleanup_test_environment():
    """Clean up test environment"""
    print("\nCleaning up test environment...")
    
    test_dirs = [
        'test_parametric_sweep_packages',
        'test_parametric_sweep_results',
        'test_parametric_sweep_logs'
    ]
    
    for dir_name in test_dirs:
        if Path(dir_name).exists():
            shutil.rmtree(dir_name)
    
    print("✓ Test environment cleaned up")


def test_run_package_import():
    """Test that run_package module can be imported"""
    print("\nTesting run_package import...")
    try:
        import run_package
        print("✓ run_package imported successfully")
        return True
    except Exception as e:
        print(f"✗ Import failed: {e}")
        return False


def test_monitor_import():
    """Test that parametric_sweep_monitor module can be imported"""
    print("\nTesting parametric_sweep_monitor import...")
    try:
        import parametric_sweep_monitor
        print("✓ parametric_sweep_monitor imported successfully")
        return True
    except Exception as e:
        print(f"✗ Import failed: {e}")
        return False


def test_run_single_package():
    """Test running a single package"""
    print("\nTesting single package execution...")
    
    try:
        result = subprocess.run(
            [
                'python3', 'run_package.py',
                '--package-id', '1',
                '--packages-dir', 'test_parametric_sweep_packages',
                '--output-dir', 'test_parametric_sweep_results'
            ],
            capture_output=True,
            text=True,
            timeout=30
        )
        
        if result.returncode == 0:
            # Check if output file was created
            output_file = Path('test_parametric_sweep_results/results_package_0001.json')
            if output_file.exists():
                # Verify output format
                with open(output_file, 'r') as f:
                    data = json.load(f)
                    
                if 'package_id' in data and 'results' in data and 'status' in data:
                    print("✓ Package executed successfully")
                    print(f"  Status: {data['status']}")
                    print(f"  Execution time: {data.get('execution_time', 'N/A')}s")
                    return True
                else:
                    print("✗ Output file has incorrect format")
                    return False
            else:
                print("✗ Output file not created")
                return False
        else:
            print(f"✗ Package execution failed with exit code {result.returncode}")
            print(f"  stderr: {result.stderr[:200]}")
            return False
            
    except Exception as e:
        print(f"✗ Test failed: {e}")
        return False


def test_monitor_script():
    """Test the monitoring script"""
    print("\nTesting monitoring script...")
    
    try:
        result = subprocess.run(
            ['python3', 'parametric_sweep_monitor.py'],
            capture_output=True,
            text=True,
            timeout=30,
            env={**os.environ, 'PACKAGES_DIR': 'test_parametric_sweep_packages'}
        )
        
        # The monitor script should handle missing directories gracefully
        if 'Analizando resultados' in result.stdout or result.returncode == 0:
            print("✓ Monitor script executed successfully")
            return True
        else:
            print(f"✗ Monitor script failed")
            print(f"  Exit code: {result.returncode}")
            return False
            
    except Exception as e:
        print(f"✗ Test failed: {e}")
        return False


def test_batch_script_exists():
    """Test that the batch execution script exists and is executable"""
    print("\nTesting batch execution script...")
    
    script_path = Path('batch_execution.sh')
    
    if not script_path.exists():
        print("✗ batch_execution.sh not found")
        return False
    
    if not os.access(script_path, os.X_OK):
        print("✗ batch_execution.sh is not executable")
        return False
    
    print("✓ batch_execution.sh exists and is executable")
    return True


def test_package_config_format():
    """Test that package configurations have correct format"""
    print("\nTesting package configuration format...")
    
    try:
        pkg_dir = Path('parametric_sweep_packages')
        if not pkg_dir.exists():
            print("⚠ parametric_sweep_packages directory not found (this is OK for testing)")
            return True
        
        priority_file = pkg_dir / 'priority_summary.json'
        if priority_file.exists():
            with open(priority_file, 'r') as f:
                priority_data = json.load(f)
            
            # Check structure
            required_keys = ['HIGH', 'MEDIUM', 'LOW']
            if all(key in priority_data for key in required_keys):
                print("✓ priority_summary.json has correct structure")
                
                # Check a few package files
                pkg_files = list(pkg_dir.glob('package_*.json'))
                if pkg_files:
                    sample_pkg = pkg_files[0]
                    with open(sample_pkg, 'r') as f:
                        pkg_data = json.load(f)
                    
                    if 'package_id' in pkg_data and 'priority' in pkg_data:
                        print(f"✓ Package files have correct structure (checked {sample_pkg.name})")
                        return True
                    else:
                        print(f"✗ Package file {sample_pkg.name} has incorrect structure")
                        return False
                else:
                    print("⚠ No package files found")
                    return True
            else:
                print("✗ priority_summary.json has incorrect structure")
                return False
        else:
            print("⚠ priority_summary.json not found (this is OK for testing)")
            return True
            
    except Exception as e:
        print(f"✗ Test failed: {e}")
        return False


def run_all_tests():
    """Run all tests"""
    print("="*70)
    print("  BATCH EXECUTION SYSTEM - TEST SUITE")
    print("="*70)
    
    tests = [
        ("Import run_package", test_run_package_import),
        ("Import monitor", test_monitor_import),
        ("Batch script exists", test_batch_script_exists),
        ("Package config format", test_package_config_format),
    ]
    
    results = []
    
    # Run basic tests first
    for name, test_func in tests:
        try:
            success = test_func()
            results.append((name, success))
        except Exception as e:
            print(f"✗ Test '{name}' crashed: {e}")
            results.append((name, False))
    
    # Run integration tests if basic tests pass
    if all(r[1] for r in results):
        print("\n" + "="*70)
        print("  INTEGRATION TESTS")
        print("="*70)
        
        setup_test_environment()
        
        integration_tests = [
            ("Run single package", test_run_single_package),
            ("Monitor script", test_monitor_script),
        ]
        
        for name, test_func in integration_tests:
            try:
                success = test_func()
                results.append((name, success))
            except Exception as e:
                print(f"✗ Test '{name}' crashed: {e}")
                results.append((name, False))
        
        cleanup_test_environment()
    
    # Summary
    print("\n" + "="*70)
    print("  TEST SUMMARY")
    print("="*70)
    
    passed = sum(1 for _, success in results if success)
    total = len(results)
    
    for name, success in results:
        status = "✓ PASS" if success else "✗ FAIL"
        print(f"  {status:8s} {name}")
    
    print("-"*70)
    print(f"  Results: {passed}/{total} tests passed")
    print("="*70)
    
    return passed == total


if __name__ == '__main__':
    success = run_all_tests()
    sys.exit(0 if success else 1)
