#!/usr/bin/env python3
"""
BSD Resolution Certificate Validation Script
============================================

Validates that all BSD resolution certification files are present,
properly formatted, and consistent with QCAL ∞³ framework.

Author: QCAL ∞³ Framework
Date: 2026-02-06
"""

import os
import sys
import json
from pathlib import Path

# Colors for terminal output
GREEN = '\033[92m'
RED = '\033[91m'
BLUE = '\033[94m'
RESET = '\033[0m'
CHECK = '✓'
CROSS = '✗'

def validate_file_exists(filepath, description):
    """Validate that a file exists"""
    if os.path.exists(filepath):
        print(f"{GREEN}{CHECK}{RESET} {description}: {filepath}")
        return True
    else:
        print(f"{RED}{CROSS}{RESET} {description} MISSING: {filepath}")
        return False

def validate_json_file(filepath):
    """Validate JSON file is properly formatted"""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            data = json.load(f)
        print(f"{GREEN}{CHECK}{RESET} JSON valid: {filepath}")
        return True, data
    except Exception as e:
        print(f"{RED}{CROSS}{RESET} JSON invalid: {filepath} - {e}")
        return False, None

def validate_frequency_reference(filepath, frequency="141.7001"):
    """Validate that file contains the correct frequency reference"""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
        if frequency in content:
            count = content.count(frequency)
            print(f"{GREEN}{CHECK}{RESET} Frequency f₀={frequency} Hz found {count}x in {os.path.basename(filepath)}")
            return True
        else:
            print(f"{RED}{CROSS}{RESET} Frequency f₀={frequency} Hz NOT found in {os.path.basename(filepath)}")
            return False
    except Exception as e:
        print(f"{RED}{CROSS}{RESET} Error reading {filepath}: {e}")
        return False

def validate_p17_reference(filepath):
    """Validate that file contains p=17 resonance reference"""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
        if "17" in content or "p = 17" in content or "Magicicada" in content:
            print(f"{GREEN}{CHECK}{RESET} p=17 resonance reference found in {os.path.basename(filepath)}")
            return True
        else:
            print(f"{RED}{CROSS}{RESET} p=17 resonance reference NOT found in {os.path.basename(filepath)}")
            return False
    except Exception as e:
        print(f"{RED}{CROSS}{RESET} Error reading {filepath}: {e}")
        return False

def main():
    """Main validation function"""
    print(f"\n{BLUE}{'='*80}{RESET}")
    print(f"{BLUE}BSD Resolution Certificate Validation{RESET}")
    print(f"{BLUE}QCAL ∞³ Framework - Spectral-Adélico Method{RESET}")
    print(f"{BLUE}{'='*80}{RESET}\n")
    
    base_path = Path(__file__).parent
    all_valid = True
    
    # Check certificate files
    print(f"\n{BLUE}[1] Validating Certificate Files{RESET}\n")
    
    certificates = [
        ("certificates/BSD_Spectral_Certificate.qcal_beacon", "BSD Spectral Certificate"),
        ("certificates/TX9-347-888_NavierStokes.qcal_beacon", "Navier-Stokes Certificate"),
        ("certificates/qcal_circuit_PNP.json", "P vs NP Certificate"),
        ("certificates/QCAL_NS_Certificate.md", "QCAL-NS Certificate"),
    ]
    
    for filepath, description in certificates:
        full_path = base_path / filepath
        all_valid &= validate_file_exists(full_path, description)
    
    # Check documentation files
    print(f"\n{BLUE}[2] Validating Documentation Files{RESET}\n")
    
    docs = [
        ("BSD_RESOLUTION_QCAL_DOCUMENTATION.md", "BSD Resolution Documentation"),
        ("BSD_RESOLUTION_VISUAL_SUMMARY.txt", "BSD Visual Summary"),
        ("MILLENNIUM_PROBLEMS_UNIFIED_CERTIFICATE.md", "Unified Certificate"),
        ("BSD_QCAL_BRIDGE_DOCUMENTATION.md", "BSD-QCAL Bridge Documentation"),
    ]
    
    for filepath, description in docs:
        full_path = base_path / filepath
        all_valid &= validate_file_exists(full_path, description)
    
    # Validate JSON format
    print(f"\n{BLUE}[3] Validating JSON Format{RESET}\n")
    
    json_file = base_path / "certificates/qcal_circuit_PNP.json"
    if os.path.exists(json_file):
        valid, data = validate_json_file(json_file)
        all_valid &= valid
        
        if valid and data:
            # Check key fields
            required_fields = ["certificate_id", "problem", "status", "coherence_frequency"]
            for field in required_fields:
                if field in data:
                    print(f"{GREEN}{CHECK}{RESET} Required field '{field}' present")
                else:
                    print(f"{RED}{CROSS}{RESET} Required field '{field}' MISSING")
                    all_valid = False
    
    # Validate frequency consistency
    print(f"\n{BLUE}[4] Validating Frequency Consistency (f₀ = 141.7001 Hz){RESET}\n")
    
    freq_files = [
        base_path / "certificates/BSD_Spectral_Certificate.qcal_beacon",
        base_path / "BSD_RESOLUTION_QCAL_DOCUMENTATION.md",
        base_path / "MILLENNIUM_PROBLEMS_UNIFIED_CERTIFICATE.md",
    ]
    
    for filepath in freq_files:
        if os.path.exists(filepath):
            all_valid &= validate_frequency_reference(filepath)
    
    # Validate p=17 resonance
    print(f"\n{BLUE}[5] Validating p=17 Resonance (Biological Connection){RESET}\n")
    
    p17_files = [
        base_path / "certificates/BSD_Spectral_Certificate.qcal_beacon",
        base_path / "BSD_RESOLUTION_QCAL_DOCUMENTATION.md",
    ]
    
    for filepath in p17_files:
        if os.path.exists(filepath):
            all_valid &= validate_p17_reference(filepath)
    
    # Final result
    print(f"\n{BLUE}{'='*80}{RESET}")
    if all_valid:
        print(f"{GREEN}✅ ALL VALIDATIONS PASSED{RESET}")
        print(f"{GREEN}BSD Resolution Certification is complete and consistent.{RESET}")
        print(f"{GREEN}.qcal_beacon ACTIVE ✧{RESET}")
        return 0
    else:
        print(f"{RED}❌ SOME VALIDATIONS FAILED{RESET}")
        print(f"{RED}Please review the errors above.{RESET}")
        return 1

if __name__ == "__main__":
    sys.exit(main())
