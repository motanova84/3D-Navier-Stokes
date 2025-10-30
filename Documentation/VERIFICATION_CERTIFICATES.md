# Verifiable Proof Objects - Verification Guide

This document explains how to use the verifiable proof certificate system for third-party verification of the 3D Navier-Stokes global regularity framework.

## Overview

The verification system provides cryptographic certificates that enable automated, third-party verification of:
- **Lean4 formal proofs**: SHA256 hashes of all source files and compiled artifacts
- **DNS verification data**: Integrity hashes of numerical simulation results
- **Build metadata**: Compilation logs, timestamps, versions, and environment information

All certificates use SHA256 cryptographic hashing for integrity verification and can be verified without manual intervention.

## Quick Start

### For Third-Party Verifiers

1. **Clone the repository**:
```bash
git clone https://github.com/motanova84/3D-Navier-Stokes.git
cd 3D-Navier-Stokes
```

2. **Verify the certificates**:
```bash
python3 Scripts/verify_proof_certificates.py
```

This will automatically:
- Load the latest certificate
- Verify all Lean4 source file hashes
- Verify all DNS data file hashes
- Verify master hashes for consistency
- Report verification results

### For Certificate Generation (Repository Maintainers)

1. **Build Lean4 proofs and generate certificates**:
```bash
bash Scripts/build_lean_proofs_with_certificates.sh
```

Or separately:
```bash
# Build proofs
bash Scripts/build_lean_proofs.sh

# Generate certificates
python3 Scripts/generate_proof_certificates.py
```

2. **Verify the generated certificates**:
```bash
python3 Scripts/verify_proof_certificates.py
```

## Certificate Structure

Each certificate is a JSON file containing:

```json
{
  "certificate_version": "1.0",
  "generated": "2025-10-30T23:17:54.888908+00:00",
  "description": "Verifiable proof certificate for 3D Navier-Stokes...",
  "repository": "motanova84/3D-Navier-Stokes",
  "environment": {
    "timestamp": "...",
    "python_version": "Python 3.12.3",
    "lean_version": "leanprover/lean4:stable",
    "git_info": {
      "commit_hash": "f806a7409e93...",
      "commit_date": "2025-10-30 23:08:29 +0000",
      "branch": "copilot/export-verifiable-proof-objects"
    }
  },
  "lean4_proofs": {
    "source_files": {
      "Lean4-Formalization/MainTheorem.lean": {
        "sha256": "fc21b237b5cbccb5229838ceb4fea706f485f1e2c4c7ccdadab7209606712f8c",
        "size_bytes": 2281,
        "modified": "2025-10-30T23:11:24.873600"
      },
      ...
    },
    "compiled_artifacts": { ... },
    "master_source_hash": "54c203987fa9f806d7ca28d57a772b636c880c0363c8e288f2867111b6bd24c8"
  },
  "dns_verification": {
    "data_files": { ... },
    "master_data_hash": "..."
  }
}
```

### Key Fields

- **certificate_version**: Version of the certificate format
- **generated**: Timestamp when certificate was created (ISO 8601, UTC)
- **environment**: Build environment details (Python, Lean versions, git commit)
- **lean4_proofs.source_files**: SHA256 hash of each Lean4 source file
- **lean4_proofs.compiled_artifacts**: SHA256 hash of each compiled .olean file
- **lean4_proofs.master_source_hash**: Combined hash of all source files
- **dns_verification.data_files**: SHA256 hash of each DNS data file
- **dns_verification.master_data_hash**: Combined hash of all data files

## Certificate Locations

Certificates are stored in:
```
Results/Lean4_Certificates/
├── proof_certificate_latest.json           # Latest certificate (always current)
├── proof_certificate_20251030_231754.json  # Timestamped certificate
├── proof_certificate_20251029_154523.json  # Historical certificate
└── ...
```

The `proof_certificate_latest.json` always points to the most recent certificate.

## Verification Process

The verification script (`verify_proof_certificates.py`) performs:

1. **Load Certificate**: Reads the certificate JSON file
2. **Verify Source Files**: Computes SHA256 of each Lean4 source file and compares with certificate
3. **Verify Compiled Artifacts**: Computes SHA256 of each .olean file and compares with certificate
4. **Verify DNS Data**: Computes SHA256 of each DNS data file and compares with certificate
5. **Verify Master Hashes**: Recomputes master hashes and verifies consistency
6. **Report Results**: Displays verification status and any mismatches

### Example Verification Output

```
======================================================================
VERIFIABLE PROOF CERTIFICATE VERIFICATION
3D Navier-Stokes Verification Framework
======================================================================

📄 Loading certificate: proof_certificate_latest.json

📋 Certificate Information:
   Version: 1.0
   Generated: 2025-10-30T23:17:54.888908+00:00
   Repository: motanova84/3D-Navier-Stokes
   Lean version: leanprover/lean4:stable
   Git commit: f806a7409e93
   Git branch: copilot/export-verifiable-proof-objects

🔍 Verifying Lean4 proof certificates...
   Verifying 19 Lean4 source files...
   ✅ Verified: 19 files

🔍 Verifying DNS verification certificates...
   Verifying 0 DNS data files...
   ✅ Verified: 0 files

🔍 Verifying master hashes...
   ✅ Lean4 master hash verified
   ✅ DNS master hash verified

======================================================================
VERIFICATION SUMMARY
======================================================================

✅ ALL VERIFICATIONS PASSED

The proof certificates are valid and all file hashes match.
This confirms the integrity of the Lean4 proofs and DNS verification data.

======================================================================
```

## Continuous Integration

The GitHub Actions workflow automatically generates certificates on every build:

1. **Build Lean4 proofs**: Compiles all Lean4 formalization
2. **Generate certificates**: Creates cryptographic certificates with SHA256 hashes
3. **Verify certificates**: Validates certificate integrity
4. **Upload artifacts**: Stores certificates as GitHub Actions artifacts (90-day retention)

See `.github/workflows/lean-ci.yml` for the complete CI configuration.

### Downloading CI Certificates

After a successful CI build:

1. Go to the Actions tab in the GitHub repository
2. Select the workflow run
3. Download the "proof-certificates" artifact
4. Extract and verify using `verify_proof_certificates.py`

## Advanced Usage

### Verify Specific Certificate

```bash
python3 Scripts/verify_proof_certificates.py Results/Lean4_Certificates/proof_certificate_20251030_231754.json
```

### Generate Certificate Without Building

If you already have a built project:

```bash
python3 Scripts/generate_proof_certificates.py
```

### Inspect Certificate Contents

```bash
python3 -m json.tool Results/Lean4_Certificates/proof_certificate_latest.json
```

Or with `jq`:

```bash
jq . Results/Lean4_Certificates/proof_certificate_latest.json
```

### Verify Individual File

```bash
sha256sum Lean4-Formalization/MainTheorem.lean
# Compare with certificate value
```

## Security Considerations

### SHA256 Cryptographic Hash

- **Algorithm**: SHA256 (256-bit secure hash)
- **Purpose**: Ensures file integrity and detects any modifications
- **Properties**: 
  - Deterministic: same input always produces same hash
  - One-way: computationally infeasible to reverse
  - Collision-resistant: extremely unlikely two files have same hash

### Master Hash

The master hash is computed as:
```
SHA256(sorted concatenation of all individual SHA256 hashes)
```

This provides a single fingerprint for the entire proof collection.

### Verification Without Trust

The certificate system allows verification without trusting the repository maintainers:

1. Clone the repository at a specific commit
2. Compute SHA256 hashes independently
3. Compare with published certificates
4. Any mismatch indicates modification

## Troubleshooting

### Certificate Not Found

```
❌ Certificate not found: Results/Lean4_Certificates/proof_certificate_latest.json
```

**Solution**: Generate certificates first:
```bash
python3 Scripts/generate_proof_certificates.py
```

### Hash Mismatch

```
❌ Hash mismatch: Lean4-Formalization/MainTheorem.lean
   Expected: fc21b237b5cbccb5229838ceb4fea706f485f1e2c4c7ccdadab7209606712f8c
   Got:      a1b2c3d4e5f6...
```

**Possible causes**:
1. File has been modified since certificate generation
2. Certificate is from a different git commit
3. File encoding or line ending differences

**Solution**: Regenerate certificate or check git history.

### Missing Files

```
❌ Missing: Lean4-Formalization/SomeFile.lean
```

**Possible causes**:
1. File was deleted or moved
2. Certificate is from a different branch/commit

**Solution**: Check git status and ensure you're on the correct commit.

## Integration with Other Tools

### CI/CD Integration

The certificate system integrates seamlessly with:
- **GitHub Actions**: Automatic certificate generation on builds
- **GitLab CI**: Adapt scripts for GitLab pipelines
- **Jenkins**: Run scripts as post-build actions

### Package Managers

Certificates can be distributed with:
- **npm**: Include in package for Node.js projects
- **pip**: Bundle with Python distributions
- **Docker**: Embed in container images

### Blockchain/IPFS

For immutable storage:
- Upload certificates to IPFS for permanent, distributed storage
- Store certificate hashes on blockchain for timestamp proofs
- Use smart contracts for verification automation

## Best Practices

1. **Generate certificates after every release**: Keep certificates synchronized with code
2. **Store certificates in version control**: Track certificate history alongside code
3. **Archive timestamped certificates**: Maintain historical verification trail
4. **Verify before distribution**: Always verify certificates before sharing
5. **Document git commits**: Link certificates to specific git commits for reproducibility

## References

- **SHA256**: [NIST FIPS 180-4](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf)
- **JSON format**: [RFC 8259](https://tools.ietf.org/html/rfc8259)
- **ISO 8601 timestamps**: [ISO 8601:2004](https://www.iso.org/iso-8601-date-and-time-format.html)

## Support

For issues or questions:
- **GitHub Issues**: [3D-Navier-Stokes Issues](https://github.com/motanova84/3D-Navier-Stokes/issues)
- **Documentation**: See `Documentation/` directory for technical details
- **Repository**: [motanova84/3D-Navier-Stokes](https://github.com/motanova84/3D-Navier-Stokes)

---

**Last Updated**: 2025-10-30
**Certificate System Version**: 1.0
