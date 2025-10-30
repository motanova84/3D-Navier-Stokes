# Lean4 Proof Certificates

This directory contains verifiable cryptographic certificates for Lean4 formal proofs and DNS verification data.

## What are Proof Certificates?

Proof certificates are JSON files containing SHA256 cryptographic hashes of:
- All Lean4 source files (.lean)
- Compiled proof artifacts (.olean files)
- DNS verification data files
- Build logs and session metadata
- Environment information (versions, git commits, timestamps)

These certificates enable **automated third-party verification** without requiring manual intervention or trust in the repository maintainers.

## Quick Start

### Verify Certificates (Third-Party Verifiers)

```bash
# From repository root
python3 Scripts/verify_proof_certificates.py
```

This automatically verifies all file hashes against the latest certificate.

### Generate New Certificates (Repository Maintainers)

```bash
# Build and generate certificates
bash Scripts/build_lean_proofs_with_certificates.sh

# Or generate separately
python3 Scripts/generate_proof_certificates.py
```

## Certificate Files

- **`proof_certificate_latest.json`**: Always points to the most recent certificate
- **`proof_certificate_YYYYMMDD_HHMMSS.json`**: Timestamped certificates for historical tracking

## Certificate Structure

```json
{
  "certificate_version": "1.0",
  "generated": "2025-10-30T23:17:54.888908+00:00",
  "repository": "motanova84/3D-Navier-Stokes",
  "environment": {
    "lean_version": "leanprover/lean4:stable",
    "git_info": {
      "commit_hash": "...",
      "branch": "..."
    }
  },
  "lean4_proofs": {
    "source_files": {
      "Lean4-Formalization/MainTheorem.lean": {
        "sha256": "fc21b237b5cbccb5...",
        "size_bytes": 2281,
        "modified": "2025-10-30T23:11:24.873600"
      },
      ...
    },
    "master_source_hash": "54c203987fa9f806..."
  },
  "dns_verification": {
    "data_files": { ... },
    "master_data_hash": "..."
  }
}
```

## Verification Process

The verification script:

1. ✅ Loads the certificate JSON
2. ✅ Computes SHA256 hash of each Lean4 source file
3. ✅ Compares computed hashes with certificate values
4. ✅ Verifies compiled artifacts (.olean files)
5. ✅ Verifies DNS data files
6. ✅ Validates master hashes for consistency
7. ✅ Reports any mismatches or errors

## Continuous Integration

Certificates are automatically generated on every CI build:
- Generated after successful Lean4 compilation
- Verified for integrity
- Uploaded as GitHub Actions artifacts

Download certificates from:
- GitHub Actions → Workflow run → Artifacts → `proof-certificates`

## Security

- **Algorithm**: SHA256 (256-bit cryptographic hash)
- **Purpose**: Ensures file integrity and detects modifications
- **Master Hash**: Combined hash of all individual hashes for single fingerprint
- **Verification**: Compare independently computed hashes with certificate

## Documentation

Complete guide: [../../Documentation/VERIFICATION_CERTIFICATES.md](../../Documentation/VERIFICATION_CERTIFICATES.md)

## Status

✅ Certificate system active and operational
✅ Automated generation in CI/CD pipeline
✅ Third-party verification enabled

Last updated: 2025-10-30
