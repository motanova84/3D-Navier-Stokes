#!/usr/bin/env python3
"""Test that psi_nse_dns_complete.py generates expected outputs"""

import subprocess
import sys
import os
import json
import tempfile
from pathlib import Path

def test_outputs_generated():
    """Test that the script generates expected output files"""
    
    print("Testing output generation for psi_nse_dns_complete.py...")
    print("Running with reduced parameters (N=32, T=0.5s)...")
    
    # Create a temporary modified version with reduced parameters
    with tempfile.TemporaryDirectory() as tmpdir:
        tmpdir_path = Path(tmpdir)
        
        # Read original script
        with open('psi_nse_dns_complete.py', 'r') as f:
            script_content = f.read()
        
        # Modify parameters for quick test
        modified_content = script_content.replace(
            'N = 128  # resolución espacial',
            'N = 32  # resolución espacial'
        ).replace(
            'dt = 0.001  # paso temporal',
            'dt = 0.01  # paso temporal'
        ).replace(
            'T_max = 5.0  # tiempo total simulación',
            'T_max = 0.5  # tiempo total simulación'
        )
        
        # Write modified script
        test_script = tmpdir_path / 'test_script.py'
        with open(test_script, 'w') as f:
            f.write(modified_content)
        
        # Change to temp directory and run
        original_dir = os.getcwd()
        try:
            os.chdir(tmpdir)
            result = subprocess.run(
                [sys.executable, str(test_script)],
                capture_output=True,
                text=True,
                timeout=180
            )
            
            # Check if script completed successfully
            if result.returncode != 0:
                print("❌ Script failed to run:")
                print(result.stderr)
                return False
            
            print("✓ Script executed successfully")
            
            # Check for expected output files
            expected_files = {
                'psi_nse_dns_results.png': 'PNG visualization',
                'psi_nse_results.json': 'JSON results'
            }
            
            all_files_present = True
            for filename, description in expected_files.items():
                if os.path.exists(filename):
                    print(f"✓ {description} generated: {filename}")
                else:
                    print(f"❌ Missing {description}: {filename}")
                    all_files_present = False
            
            # Validate JSON content if present
            if os.path.exists('psi_nse_results.json'):
                try:
                    with open('psi_nse_results.json', 'r') as f:
                        results = json.load(f)
                    
                    required_keys = [
                        'parameters', 'detected_frequency_Hz', 
                        'final_energy', 'final_enstrophy',
                        'max_energy', 'blow_up_detected'
                    ]
                    
                    missing_keys = [k for k in required_keys if k not in results]
                    if missing_keys:
                        print(f"❌ JSON missing keys: {missing_keys}")
                        all_files_present = False
                    else:
                        print(f"✓ JSON contains all required keys")
                        print(f"  - Final energy: {results['final_energy']:.6f}")
                        print(f"  - Max energy: {results['max_energy']:.6e}")
                        print(f"  - Blow-up detected: {results['blow_up_detected']}")
                        print(f"  - Detected frequency: {results['detected_frequency_Hz']:.2f} Hz")
                        
                        # Verify no blow-up
                        if not results['blow_up_detected']:
                            print("✓ System stable (no blow-up)")
                        else:
                            print("❌ Blow-up detected (unexpected)")
                            all_files_present = False
                            
                except json.JSONDecodeError as e:
                    print(f"❌ Invalid JSON: {e}")
                    all_files_present = False
            
            return all_files_present
            
        finally:
            os.chdir(original_dir)

if __name__ == '__main__':
    print("="*70)
    print("PSI-NSE DNS OUTPUT VALIDATION TEST")
    print("="*70)
    print()
    
    success = test_outputs_generated()
    
    print()
    print("="*70)
    if success:
        print("✅ ALL TESTS PASSED")
        print("="*70)
        sys.exit(0)
    else:
        print("❌ TESTS FAILED")
        print("="*70)
        sys.exit(1)
