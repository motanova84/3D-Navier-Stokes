#!/usr/bin/env python3
"""
Inspect proof certificate contents in a human-readable format.

Usage:
    python3 Scripts/inspect_certificate.py [certificate_path]
    
If no path is provided, inspects the latest certificate.
"""

import sys
import json
from pathlib import Path
from typing import Dict, Any


def format_size(bytes_size: int) -> str:
    """Format byte size in human-readable format."""
    for unit in ['B', 'KB', 'MB', 'GB']:
        if bytes_size < 1024.0:
            return f"{bytes_size:.1f} {unit}"
        bytes_size /= 1024.0
    return f"{bytes_size:.1f} TB"


def print_section(title: str, char: str = "="):
    """Print formatted section header."""
    print(f"\n{char * 70}")
    print(title)
    print(char * 70)


def inspect_environment(env: Dict[str, Any]):
    """Print environment information."""
    print_section("ENVIRONMENT INFORMATION", "-")
    print(f"Timestamp:      {env.get('timestamp', 'unknown')}")
    print(f"Python Version: {env.get('python_version', 'unknown')}")
    print(f"Lean Version:   {env.get('lean_version', 'unknown')}")
    print(f"Platform:       {env.get('platform', 'unknown')}")
    print(f"Hostname:       {env.get('hostname', 'unknown')}")
    
    git_info = env.get('git_info', {})
    if git_info:
        print(f"\nGit Information:")
        print(f"  Commit:  {git_info.get('commit_hash', 'unknown')[:12]}...")
        print(f"  Branch:  {git_info.get('branch', 'unknown')}")
        print(f"  Date:    {git_info.get('commit_date', 'unknown')}")


def inspect_lean4_proofs(lean4_data: Dict[str, Any]):
    """Print Lean4 proof information."""
    print_section("LEAN4 FORMAL PROOFS", "-")
    
    source_files = lean4_data.get('source_files', {})
    compiled_files = lean4_data.get('compiled_artifacts', {})
    stats = lean4_data.get('statistics', {})
    master_hash = lean4_data.get('master_source_hash', 'N/A')
    
    print(f"\nSource Files:     {len(source_files)} files")
    print(f"Compiled Files:   {len(compiled_files)} files")
    print(f"Total Size:       {format_size(stats.get('total_source_bytes', 0))}")
    print(f"Master Hash:      {master_hash[:32]}...")
    
    if source_files:
        print(f"\nSource File Details:")
        # Sort by path for consistent display
        for path in sorted(source_files.keys())[:10]:  # Show first 10
            info = source_files[path]
            size = format_size(info.get('size_bytes', 0))
            hash_short = info.get('sha256', '')[:12]
            print(f"  {path}")
            print(f"    SHA256: {hash_short}... | Size: {size}")
        
        if len(source_files) > 10:
            print(f"  ... and {len(source_files) - 10} more files")


def inspect_dns_data(dns_data: Dict[str, Any]):
    """Print DNS verification information."""
    print_section("DNS VERIFICATION DATA", "-")
    
    data_files = dns_data.get('data_files', {})
    stats = dns_data.get('statistics', {})
    master_hash = dns_data.get('master_data_hash', 'N/A')
    
    print(f"\nData Files:       {len(data_files)} files")
    print(f"Total Size:       {format_size(stats.get('total_data_bytes', 0))}")
    print(f"Master Hash:      {master_hash[:32] if master_hash != 'no_data_files' else master_hash}...")
    
    if data_files:
        print(f"\nData File Details:")
        for path in sorted(data_files.keys())[:10]:  # Show first 10
            info = data_files[path]
            size = format_size(info.get('size_bytes', 0))
            hash_short = info.get('sha256', '')[:12]
            print(f"  {path}")
            print(f"    SHA256: {hash_short}... | Size: {size}")
        
        if len(data_files) > 10:
            print(f"  ... and {len(data_files) - 10} more files")
    else:
        print("\nNo DNS data files in certificate.")


def inspect_build_log(build_data: Dict[str, Any]):
    """Print build log information."""
    print_section("BUILD INFORMATION", "-")
    
    print(f"Timestamp:  {build_data.get('timestamp', 'unknown')}")
    
    if 'log_file' in build_data:
        print(f"Log File:   {build_data['log_file']}")
        print(f"Log Hash:   {build_data.get('log_sha256', 'N/A')[:32]}...")
        print(f"Log Size:   {format_size(build_data.get('log_size_bytes', 0))}")
    else:
        print("No build log available.")


def main():
    """Main entry point."""
    print("=" * 70)
    print("PROOF CERTIFICATE INSPECTOR")
    print("=" * 70)
    
    # Determine certificate path
    repo_root = Path(__file__).parent.parent
    
    if len(sys.argv) > 1:
        cert_path = Path(sys.argv[1])
    else:
        cert_path = repo_root / "Results" / "Lean4_Certificates" / "proof_certificate_latest.json"
    
    if not cert_path.exists():
        print(f"\n❌ Certificate not found: {cert_path}")
        print("\nUsage:")
        print("  python3 Scripts/inspect_certificate.py [certificate_path]")
        sys.exit(1)
    
    print(f"\nInspecting: {cert_path}")
    
    # Load certificate
    try:
        with open(cert_path, 'r') as f:
            certificate = json.load(f)
    except Exception as e:
        print(f"\n❌ Error loading certificate: {str(e)}")
        sys.exit(1)
    
    # Print basic information
    print_section("CERTIFICATE METADATA")
    print(f"Version:      {certificate.get('certificate_version', 'unknown')}")
    print(f"Generated:    {certificate.get('generated', 'unknown')}")
    print(f"Repository:   {certificate.get('repository', 'unknown')}")
    print(f"Description:  {certificate.get('description', 'N/A')}")
    
    # Inspect components
    if 'environment' in certificate:
        inspect_environment(certificate['environment'])
    
    if 'lean4_proofs' in certificate:
        inspect_lean4_proofs(certificate['lean4_proofs'])
    
    if 'dns_verification' in certificate:
        inspect_dns_data(certificate['dns_verification'])
    
    if 'build_log' in certificate:
        inspect_build_log(certificate['build_log'])
    
    # Summary
    print_section("VERIFICATION INSTRUCTIONS")
    print("\nTo verify this certificate:")
    print(f"  python3 Scripts/verify_proof_certificates.py {cert_path.name}")
    print("\nFor more information:")
    print("  See Documentation/VERIFICATION_CERTIFICATES.md")
    print()


if __name__ == "__main__":
    main()
