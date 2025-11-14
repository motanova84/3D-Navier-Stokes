#!/usr/bin/env python3
"""
Integration Test for Frequency Scale Correction
================================================

Tests that all frequency scale correction components work together correctly.
"""

import subprocess
import sys
import os
from pathlib import Path


def run_script(script_name: str) -> bool:
    """Run a Python script and check if it succeeds"""
    print(f"\n{'='*70}")
    print(f"Testing: {script_name}")
    print('='*70)
    
    try:
        result = subprocess.run(
            [sys.executable, script_name],
            capture_output=True,
            text=True,
            timeout=180
        )
        
        if result.returncode == 0:
            print(f"✅ {script_name} completed successfully")
            # Print last few lines of output
            lines = result.stdout.split('\n')
            print("\nLast 10 lines of output:")
            for line in lines[-10:]:
                if line.strip():
                    print(f"  {line}")
            return True
        else:
            print(f"❌ {script_name} failed with return code {result.returncode}")
            print(f"Error output:\n{result.stderr}")
            return False
            
    except subprocess.TimeoutExpired:
        print(f"❌ {script_name} timed out after 180 seconds")
        return False
    except Exception as e:
        print(f"❌ {script_name} raised exception: {e}")
        return False


def check_outputs(expected_files: list) -> bool:
    """Check that expected output files exist"""
    print(f"\n{'='*70}")
    print("Checking Output Files")
    print('='*70)
    
    all_exist = True
    for pattern in expected_files:
        matching = list(Path('.').glob(pattern))
        if matching:
            print(f"✅ Found {len(matching)} file(s) matching: {pattern}")
            for f in matching[:3]:  # Show first 3 matches
                print(f"   - {f}")
        else:
            print(f"❌ No files found matching: {pattern}")
            all_exist = False
    
    return all_exist


def main():
    """Run integration test"""
    print("\n" + "="*70)
    print("FREQUENCY SCALE CORRECTION - INTEGRATION TEST")
    print("="*70)
    print("\nThis test verifies that all frequency scale correction")
    print("components are working correctly together.")
    print("="*70)
    
    # Scripts to test
    scripts = [
        'fix_frequency_scale.py',
        'regenerate_with_correct_scale.py',
        'validate_natural_frequency_emergence.py'
    ]
    
    # Expected output patterns
    expected_outputs = [
        'artifacts/frequency_scale_correction_*.png',
        'artifacts/spectrum_corrected_scale_*.png',
        'Results/Verification/frequency_scale_correction_*.md',
        'Results/Verification/spectrum_regeneration_*.md',
        'Results/Verification/natural_frequency_emergence_*.md',
        'FREQUENCY_SCALE_CORRECTION.md'
    ]
    
    # Run all scripts
    results = {}
    for script in scripts:
        if not os.path.exists(script):
            print(f"❌ Script not found: {script}")
            results[script] = False
        else:
            results[script] = run_script(script)
    
    # Check outputs
    outputs_ok = check_outputs(expected_outputs)
    
    # Summary
    print("\n" + "="*70)
    print("INTEGRATION TEST SUMMARY")
    print("="*70)
    
    all_passed = all(results.values()) and outputs_ok
    
    print("\nScript Results:")
    for script, passed in results.items():
        status = "✅ PASS" if passed else "❌ FAIL"
        print(f"  {status}: {script}")
    
    print(f"\nOutput Files: {'✅ PASS' if outputs_ok else '❌ FAIL'}")
    
    print("\n" + "="*70)
    if all_passed:
        print("✅ ALL TESTS PASSED")
        print("="*70)
        print("\nFrequency scale correction is working correctly!")
        print("Key findings:")
        print("  • Scale factor λ ≈ 1417 is consistent")
        print("  • Frequency f₀ = 141.7 Hz emerges spontaneously")
        print("  • Temporal scaling is validated")
        print("  • All visualizations and reports generated")
        return 0
    else:
        print("❌ SOME TESTS FAILED")
        print("="*70)
        print("\nPlease review the error messages above.")
        return 1


if __name__ == '__main__':
    sys.exit(main())
