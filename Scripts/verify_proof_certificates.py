#!/usr/bin/env python3
"""
Verify proof certificates for third-party validation.

This script verifies cryptographic certificates without requiring manual changes:
- Validates SHA256 hashes of Lean4 source files
- Validates SHA256 hashes of compiled artifacts
- Validates DNS verification data integrity
- Checks certificate consistency and completeness

Usage:
    python3 Scripts/verify_proof_certificates.py [certificate_path]
    
If no certificate path is provided, uses the latest certificate.
"""

import os
import json
import hashlib
import sys
from pathlib import Path
from typing import Dict, List, Tuple, Any


def compute_sha256(filepath: Path) -> str:
    """Compute SHA256 hash of a file."""
    sha256_hash = hashlib.sha256()
    try:
        with open(filepath, "rb") as f:
            for byte_block in iter(lambda: f.read(4096), b""):
                sha256_hash.update(byte_block)
        return sha256_hash.hexdigest()
    except Exception as e:
        return f"ERROR: {str(e)}"


def load_certificate(cert_path: Path) -> Dict[str, Any]:
    """Load certificate from JSON file."""
    with open(cert_path, 'r') as f:
        return json.load(f)


def verify_file_hashes(
    repo_root: Path,
    file_hashes: Dict[str, Dict[str, Any]],
    description: str
) -> Tuple[int, int, List[str]]:
    """
    Verify file hashes against certificate.
    
    Returns:
        Tuple of (verified_count, failed_count, error_messages)
    """
    verified = 0
    failed = 0
    errors = []
    
    print(f"   Verifying {len(file_hashes)} {description}...")
    
    for rel_path, file_info in file_hashes.items():
        file_path = repo_root / rel_path
        expected_hash = file_info["sha256"]
        
        if not file_path.exists():
            errors.append(f"   ❌ Missing: {rel_path}")
            failed += 1
            continue
        
        actual_hash = compute_sha256(file_path)
        
        if actual_hash.startswith("ERROR"):
            errors.append(f"   ❌ Error reading {rel_path}: {actual_hash}")
            failed += 1
            continue
        
        if actual_hash == expected_hash:
            verified += 1
        else:
            errors.append(f"   ❌ Hash mismatch: {rel_path}")
            errors.append(f"      Expected: {expected_hash}")
            errors.append(f"      Got:      {actual_hash}")
            failed += 1
    
    return verified, failed, errors


def verify_lean4_proofs(
    repo_root: Path,
    cert_data: Dict[str, Any]
) -> Tuple[bool, List[str]]:
    """Verify Lean4 proof certificates."""
    print("\n🔍 Verifying Lean4 proof certificates...")
    
    if not cert_data:
        print("   ⚠️  No Lean4 certificate data found")
        return True, []  # Not an error if not present
    
    source_files = cert_data.get("source_files", {})
    compiled_files = cert_data.get("compiled_artifacts", {})
    
    # Verify source files
    src_verified, src_failed, src_errors = verify_file_hashes(
        repo_root, source_files, "Lean4 source files"
    )
    
    # Verify compiled artifacts (optional - may not exist)
    if compiled_files:
        art_verified, art_failed, art_errors = verify_file_hashes(
            repo_root, compiled_files, "compiled artifacts"
        )
    else:
        art_verified, art_failed, art_errors = 0, 0, []
        print("   ℹ️  No compiled artifacts in certificate (skipping)")
    
    # Report results
    all_errors = src_errors + art_errors
    total_verified = src_verified + art_verified
    total_failed = src_failed + art_failed
    
    print(f"   ✅ Verified: {total_verified} files")
    if total_failed > 0:
        print(f"   ❌ Failed: {total_failed} files")
    
    success = total_failed == 0
    return success, all_errors


def verify_dns_data(
    repo_root: Path,
    cert_data: Dict[str, Any]
) -> Tuple[bool, List[str]]:
    """Verify DNS verification data certificates."""
    print("\n🔍 Verifying DNS verification certificates...")
    
    if not cert_data:
        print("   ⚠️  No DNS certificate data found")
        return True, []  # Not an error if not present
    
    data_files = cert_data.get("data_files", {})
    
    if not data_files:
        print("   ℹ️  No DNS data files in certificate (skipping)")
        return True, []
    
    # Verify data files
    verified, failed, errors = verify_file_hashes(
        repo_root, data_files, "DNS data files"
    )
    
    print(f"   ✅ Verified: {verified} files")
    if failed > 0:
        print(f"   ❌ Failed: {failed} files")
    
    success = failed == 0
    return success, errors


def verify_master_hash(cert_data: Dict[str, Any], cert_type: str) -> bool:
    """Verify master hash consistency."""
    if cert_type not in cert_data:
        return True  # Skip if not present
    
    data = cert_data[cert_type]
    files = data.get("source_files", {}) or data.get("data_files", {})
    master_hash = data.get("master_source_hash") or data.get("master_data_hash")
    
    if not files or not master_hash:
        return True
    
    # Recompute master hash
    all_hashes = "".join(sorted([v["sha256"] for v in files.values()]))
    computed_hash = hashlib.sha256(all_hashes.encode()).hexdigest()
    
    return computed_hash == master_hash


def print_certificate_info(cert: Dict[str, Any]):
    """Print certificate metadata."""
    print("\n📋 Certificate Information:")
    print(f"   Version: {cert.get('certificate_version', 'unknown')}")
    print(f"   Generated: {cert.get('generated', 'unknown')}")
    print(f"   Repository: {cert.get('repository', 'unknown')}")
    
    env = cert.get('environment', {})
    if env:
        print(f"   Lean version: {env.get('lean_version', 'unknown')}")
        git_info = env.get('git_info', {})
        if git_info:
            print(f"   Git commit: {git_info.get('commit_hash', 'unknown')[:12]}")
            print(f"   Git branch: {git_info.get('branch', 'unknown')}")


def main():
    """Main verification entry point."""
    print("=" * 70)
    print("VERIFIABLE PROOF CERTIFICATE VERIFICATION")
    print("3D Navier-Stokes Verification Framework")
    print("=" * 70)
    
    repo_root = Path(__file__).parent.parent
    os.chdir(repo_root)
    
    # Determine certificate path
    if len(sys.argv) > 1:
        cert_path = Path(sys.argv[1])
    else:
        cert_path = repo_root / "Results" / "Lean4_Certificates" / "proof_certificate_latest.json"
    
    if not cert_path.exists():
        print(f"\n❌ Certificate not found: {cert_path}")
        print("\nUsage:")
        print("  python3 Scripts/verify_proof_certificates.py [certificate_path]")
        print("\nOr generate certificates first:")
        print("  python3 Scripts/generate_proof_certificates.py")
        sys.exit(1)
    
    print(f"\n📄 Loading certificate: {cert_path.name}")
    
    # Load certificate
    try:
        certificate = load_certificate(cert_path)
    except Exception as e:
        print(f"\n❌ Error loading certificate: {str(e)}")
        sys.exit(1)
    
    # Print certificate info
    print_certificate_info(certificate)
    
    # Verify components
    all_success = True
    all_errors = []
    
    # 1. Verify Lean4 proofs
    lean4_success, lean4_errors = verify_lean4_proofs(
        repo_root,
        certificate.get("lean4_proofs", {})
    )
    all_success = all_success and lean4_success
    all_errors.extend(lean4_errors)
    
    # 2. Verify DNS data
    dns_success, dns_errors = verify_dns_data(
        repo_root,
        certificate.get("dns_verification", {})
    )
    all_success = all_success and dns_success
    all_errors.extend(dns_errors)
    
    # 3. Verify master hashes
    print("\n🔍 Verifying master hashes...")
    lean4_master_ok = verify_master_hash(certificate, "lean4_proofs")
    dns_master_ok = verify_master_hash(certificate, "dns_verification")
    
    if lean4_master_ok:
        print("   ✅ Lean4 master hash verified")
    else:
        print("   ❌ Lean4 master hash mismatch")
        all_success = False
    
    if dns_master_ok:
        print("   ✅ DNS master hash verified")
    else:
        print("   ❌ DNS master hash mismatch")
        all_success = False
    
    # Print summary
    print("\n" + "=" * 70)
    print("VERIFICATION SUMMARY")
    print("=" * 70)
    
    if all_success:
        print("\n✅ ALL VERIFICATIONS PASSED")
        print("\nThe proof certificates are valid and all file hashes match.")
        print("This confirms the integrity of the Lean4 proofs and DNS verification data.")
    else:
        print("\n❌ VERIFICATION FAILED")
        print("\nSome checks did not pass. Details:")
        for error in all_errors:
            print(error)
    
    print("\n" + "=" * 70)
    
    sys.exit(0 if all_success else 1)


if __name__ == "__main__":
    main()
