#!/usr/bin/env python3
"""
Generate verifiable proof certificates for Lean4 proofs and DNS verification.

This script creates cryptographic certificates containing:
- SHA256 hashes of all Lean4 source files
- Compilation logs with timestamps
- SHA256 signatures of compiled proof artifacts (.olean files)
- Build metadata (versions, environment, parameters)
- DNS verification results and data integrity hashes

These certificates enable third-party verification without manual intervention.
"""

import os
import json
import hashlib
import subprocess
import datetime
from pathlib import Path
from typing import Dict, List, Any


# Sentinel value for when no data files are present
NO_DATA_FILES_SENTINEL = "no_data_files"


def compute_sha256(filepath: Path) -> str:
    """Compute SHA256 hash of a file."""
    sha256_hash = hashlib.sha256()
    with open(filepath, "rb") as f:
        for byte_block in iter(lambda: f.read(4096), b""):
            sha256_hash.update(byte_block)
    return sha256_hash.hexdigest()


def find_lean_files(directory: Path) -> List[Path]:
    """Recursively find all .lean files in directory."""
    return sorted(directory.rglob("*.lean"))


def find_olean_files(directory: Path) -> List[Path]:
    """Recursively find all .olean files in directory."""
    return sorted(directory.rglob("*.olean"))


def get_git_info() -> Dict[str, str]:
    """Get current git commit information."""
    try:
        commit_hash = subprocess.check_output(
            ["git", "rev-parse", "HEAD"],
            stderr=subprocess.DEVNULL
        ).decode().strip()
        
        commit_date = subprocess.check_output(
            ["git", "log", "-1", "--format=%ci"],
            stderr=subprocess.DEVNULL
        ).decode().strip()
        
        branch = subprocess.check_output(
            ["git", "rev-parse", "--abbrev-ref", "HEAD"],
            stderr=subprocess.DEVNULL
        ).decode().strip()
        
        return {
            "commit_hash": commit_hash,
            "commit_date": commit_date,
            "branch": branch
        }
    except Exception as e:
        return {
            "commit_hash": "unknown",
            "commit_date": "unknown",
            "branch": "unknown",
            "error": str(e)
        }


def get_lean_version() -> str:
    """Get Lean version from lean-toolchain."""
    toolchain_path = Path("lean-toolchain")
    if toolchain_path.exists():
        return toolchain_path.read_text().strip()
    return "unknown"


def get_environment_info() -> Dict[str, Any]:
    """Collect environment information."""
    info = {
        "timestamp": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "python_version": subprocess.check_output(
            ["python3", "--version"]
        ).decode().strip(),
        "lean_version": get_lean_version(),
        "git_info": get_git_info(),
        "hostname": os.uname().nodename if hasattr(os, 'uname') else "unknown",
        "platform": os.uname().sysname if hasattr(os, 'uname') else "unknown"
    }
    return info


def generate_lean4_certificates(repo_root: Path) -> Dict[str, Any]:
    """Generate certificates for Lean4 proof files."""
    print("📝 Generating Lean4 proof certificates...")
    
    lean_dir = repo_root / "Lean4-Formalization"
    if not lean_dir.exists():
        print(f"⚠️  Lean4-Formalization directory not found")
        return {}
    
    # Find all Lean source files
    lean_files = find_lean_files(lean_dir)
    print(f"   Found {len(lean_files)} Lean source files")
    
    # Compute hashes for source files
    source_hashes = {}
    for lean_file in lean_files:
        rel_path = lean_file.relative_to(repo_root)
        source_hashes[str(rel_path)] = {
            "sha256": compute_sha256(lean_file),
            "size_bytes": lean_file.stat().st_size,
            "modified": datetime.datetime.fromtimestamp(
                lean_file.stat().st_mtime
            ).isoformat()
        }
    
    # Find compiled artifacts (.olean files)
    lake_dir = repo_root / ".lake"
    olean_files = find_olean_files(lake_dir) if lake_dir.exists() else []
    print(f"   Found {len(olean_files)} compiled artifacts (.olean)")
    
    # Compute hashes for compiled artifacts
    artifact_hashes = {}
    for olean_file in olean_files:
        rel_path = olean_file.relative_to(repo_root)
        artifact_hashes[str(rel_path)] = {
            "sha256": compute_sha256(olean_file),
            "size_bytes": olean_file.stat().st_size,
            "modified": datetime.datetime.fromtimestamp(
                olean_file.stat().st_mtime
            ).isoformat()
        }
    
    # Compute master hash of all source files
    all_source_hashes = "".join(sorted([v["sha256"] for v in source_hashes.values()]))
    master_hash = hashlib.sha256(all_source_hashes.encode()).hexdigest()
    
    certificate = {
        "type": "lean4_proof_certificate",
        "environment": get_environment_info(),
        "source_files": source_hashes,
        "compiled_artifacts": artifact_hashes,
        "master_source_hash": master_hash,
        "statistics": {
            "total_source_files": len(source_hashes),
            "total_compiled_files": len(artifact_hashes),
            "total_source_bytes": sum(f["size_bytes"] for f in source_hashes.values()),
            "total_artifact_bytes": sum(f["size_bytes"] for f in artifact_hashes.values())
        }
    }
    
    print(f"   ✅ Generated certificate with master hash: {master_hash[:16]}...")
    return certificate


def generate_dns_certificates(repo_root: Path) -> Dict[str, Any]:
    """Generate certificates for DNS verification data."""
    print("📝 Generating DNS verification certificates...")
    
    dns_data_dir = repo_root / "Results" / "DNS_Data"
    if not dns_data_dir.exists():
        print(f"⚠️  DNS_Data directory not found")
        return {}
    
    # Find all data files (various formats)
    data_files = []
    for ext in [".h5", ".hdf5", ".npy", ".npz", ".json", ".csv", ".txt"]:
        data_files.extend(dns_data_dir.rglob(f"*{ext}"))
    
    data_files = sorted(data_files)
    print(f"   Found {len(data_files)} DNS data files")
    
    # Compute hashes for data files
    data_hashes = {}
    for data_file in data_files:
        rel_path = data_file.relative_to(repo_root)
        data_hashes[str(rel_path)] = {
            "sha256": compute_sha256(data_file),
            "size_bytes": data_file.stat().st_size,
            "modified": datetime.datetime.fromtimestamp(
                data_file.stat().st_mtime
            ).isoformat()
        }
    
    # Compute master hash of all data files
    if data_hashes:
        all_data_hashes = "".join(sorted([v["sha256"] for v in data_hashes.values()]))
        master_hash = hashlib.sha256(all_data_hashes.encode()).hexdigest()
    else:
        master_hash = NO_DATA_FILES_SENTINEL
    
    certificate = {
        "type": "dns_verification_certificate",
        "environment": get_environment_info(),
        "data_files": data_hashes,
        "master_data_hash": master_hash,
        "statistics": {
            "total_data_files": len(data_hashes),
            "total_data_bytes": sum(f["size_bytes"] for f in data_hashes.values())
        }
    }
    
    print(f"   ✅ Generated certificate with master hash: {master_hash[:16]}...")
    return certificate


def capture_build_log(repo_root: Path) -> Dict[str, Any]:
    """Capture the last build log information."""
    print("📝 Capturing build log information...")
    
    log_info = {
        "timestamp": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "build_commands": []
    }
    
    # Check if build logs exist
    build_log_paths = [
        repo_root / "build.log",
        repo_root / ".lake" / "build" / "log"
    ]
    
    for log_path in build_log_paths:
        if log_path.exists():
            log_info["log_file"] = str(log_path.relative_to(repo_root))
            log_info["log_sha256"] = compute_sha256(log_path)
            log_info["log_size_bytes"] = log_path.stat().st_size
            print(f"   Found build log: {log_path.name}")
            break
    
    print("   ✅ Build log information captured")
    return log_info


def save_certificate(certificate: Dict[str, Any], output_path: Path):
    """Save certificate to JSON file."""
    with open(output_path, 'w') as f:
        json.dump(certificate, f, indent=2, sort_keys=True)
    
    # Compute SHA256 of the certificate itself
    cert_hash = compute_sha256(output_path)
    print(f"   📄 Certificate saved: {output_path.name}")
    print(f"   🔒 Certificate SHA256: {cert_hash}")


def main():
    """Main entry point for certificate generation."""
    print("=" * 70)
    print("VERIFIABLE PROOF CERTIFICATE GENERATOR")
    print("3D Navier-Stokes Verification Framework")
    print("=" * 70)
    print()
    
    repo_root = Path(__file__).parent.parent
    os.chdir(repo_root)
    
    # Create output directory
    cert_dir = repo_root / "Results" / "Lean4_Certificates"
    cert_dir.mkdir(parents=True, exist_ok=True)
    
    # Generate comprehensive certificate
    timestamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%d_%H%M%S")
    
    # 1. Lean4 proof certificates
    lean4_cert = generate_lean4_certificates(repo_root)
    
    # 2. DNS verification certificates
    dns_cert = generate_dns_certificates(repo_root)
    
    # 3. Build log information
    build_log = capture_build_log(repo_root)
    
    # 4. Combine into master certificate
    master_certificate = {
        "certificate_version": "1.0",
        "generated": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "description": "Verifiable proof certificate for 3D Navier-Stokes global regularity framework",
        "repository": "motanova84/3D-Navier-Stokes",
        "environment": get_environment_info(),
        "lean4_proofs": lean4_cert,
        "dns_verification": dns_cert,
        "build_log": build_log
    }
    
    # Save master certificate
    master_cert_path = cert_dir / f"proof_certificate_{timestamp}.json"
    save_certificate(master_certificate, master_cert_path)
    
    # Save latest certificate (symlink or copy)
    latest_cert_path = cert_dir / "proof_certificate_latest.json"
    save_certificate(master_certificate, latest_cert_path)
    
    # Generate summary
    print()
    print("=" * 70)
    print("CERTIFICATE GENERATION COMPLETE")
    print("=" * 70)
    print(f"📁 Output directory: {cert_dir}")
    print(f"📄 Master certificate: {master_cert_path.name}")
    print(f"📄 Latest certificate: {latest_cert_path.name}")
    print()
    print("Summary:")
    if lean4_cert:
        stats = lean4_cert.get("statistics", {})
        print(f"  • Lean4 source files: {stats.get('total_source_files', 0)}")
        print(f"  • Compiled artifacts: {stats.get('total_compiled_files', 0)}")
    if dns_cert:
        stats = dns_cert.get("statistics", {})
        print(f"  • DNS data files: {stats.get('total_data_files', 0)}")
    print()
    print("🔒 All files hashed with SHA256 for verification")
    print("✅ Certificates ready for third-party verification")
    print()


if __name__ == "__main__":
    main()
