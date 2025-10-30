#!/usr/bin/env python3
"""
Example: Third-Party Verification Workflow

This script demonstrates how a third party can verify the proof certificates
without needing to trust the repository maintainers or perform manual checks.

Usage:
    python3 examples/verify_third_party.py
"""

import sys
import os
from pathlib import Path

# Add Scripts directory to path for importing verification functions
repo_root = Path(__file__).parent.parent
scripts_dir = repo_root / "Scripts"
sys.path.insert(0, str(scripts_dir))

# Change to repo root for consistent file resolution
os.chdir(repo_root)

from verify_proof_certificates import (
    load_certificate,
    verify_lean4_proofs,
    verify_dns_data,
    verify_master_hash,
    print_certificate_info
)


def main():
    """Demonstrate third-party verification workflow."""
    print("=" * 70)
    print("EXAMPLE: THIRD-PARTY VERIFICATION WORKFLOW")
    print("=" * 70)
    print()
    print("This example demonstrates how a third party can verify proof")
    print("certificates without requiring trust or manual intervention.")
    print()
    
    # Step 1: Locate certificate
    repo_root = Path(__file__).parent.parent
    cert_path = repo_root / "Results" / "Lean4_Certificates" / "proof_certificate_latest.json"
    
    if not cert_path.exists():
        print("❌ Certificate not found!")
        print("Please generate certificates first:")
        print("  python3 Scripts/generate_proof_certificates.py")
        return False
    
    print("Step 1: Load Certificate")
    print("-" * 70)
    certificate = load_certificate(cert_path)
    print(f"✅ Loaded certificate: {cert_path.name}")
    print()
    
    # Step 2: Inspect certificate metadata
    print("Step 2: Inspect Certificate Metadata")
    print("-" * 70)
    print_certificate_info(certificate)
    print()
    
    # Step 3: Verify Lean4 proofs
    print("Step 3: Verify Lean4 Proof Files")
    print("-" * 70)
    lean4_success, lean4_errors = verify_lean4_proofs(
        repo_root,
        certificate.get("lean4_proofs", {})
    )
    print()
    
    # Step 4: Verify DNS data
    print("Step 4: Verify DNS Verification Data")
    print("-" * 70)
    dns_success, dns_errors = verify_dns_data(
        repo_root,
        certificate.get("dns_verification", {})
    )
    print()
    
    # Step 5: Verify master hashes
    print("Step 5: Verify Master Hash Consistency")
    print("-" * 70)
    lean4_master_ok = verify_master_hash(certificate, "lean4_proofs")
    dns_master_ok = verify_master_hash(certificate, "dns_verification")
    
    if lean4_master_ok:
        print("   ✅ Lean4 master hash verified")
    else:
        print("   ❌ Lean4 master hash mismatch")
    
    if dns_master_ok:
        print("   ✅ DNS master hash verified")
    else:
        print("   ❌ DNS master hash mismatch")
    print()
    
    # Final result
    all_success = lean4_success and dns_success and lean4_master_ok and dns_master_ok
    
    print("=" * 70)
    print("VERIFICATION RESULT")
    print("=" * 70)
    
    if all_success:
        print()
        print("✅ SUCCESS: All verifications passed!")
        print()
        print("What this means:")
        print("  • All Lean4 source files match the certificate hashes")
        print("  • All DNS data files match the certificate hashes")
        print("  • Master hashes are consistent")
        print("  • The proofs have not been modified since certificate generation")
        print()
        print("You can trust these results without requiring:")
        print("  • Manual file inspection")
        print("  • Trust in repository maintainers")
        print("  • Knowledge of the build system")
        print()
        print("The cryptographic hashes provide mathematical certainty.")
    else:
        print()
        print("❌ FAILURE: Some verifications failed!")
        print()
        print("This could indicate:")
        print("  • Files have been modified since certificate generation")
        print("  • Certificate is from a different git commit")
        print("  • File corruption or tampering")
        print()
        if lean4_errors or dns_errors:
            print("Errors:")
            for error in lean4_errors + dns_errors:
                print(error)
    
    print("=" * 70)
    return all_success


if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)
