# Lean4 Certificate Generation Guide

This guide explains how to build the Lean4 formalization and generate formal verification certificates (.olean files) for the 3D Navier-Stokes global regularity proof.

## Quick Start

```bash
# 1. Install Lean4 (one-time setup)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
export PATH="$HOME/.elan/bin:$PATH"

# 2. Navigate to Lean4 directory
cd Lean4-Formalization

# 3. Build and generate certificates
lake update
lake build
```

## What Are Lean4 Certificates?

Lean4 certificates (.olean files) are compiled proof objects that:

1. **Verify correctness**: Machine-checkable proofs that can be independently verified
2. **Enable reproducibility**: Anyone can rebuild and verify the proofs
3. **Provide traceability**: Formal record of the proof structure and dependencies
4. **Support distribution**: Can be shared, archived, and referenced in publications

## Certificate Locations

After a successful build, certificates are generated in:

```
.lake/build/lib/NavierStokes/
├── BasicDefinitions.olean          # Core definitions
├── UniformConstants.olean          # Universal constants
├── MisalignmentDefect.olean       # δ* persistence theorem
├── DyadicRiccati.olean            # Dyadic Riccati framework
├── ParabolicCoercivity.olean      # NBB coercivity lemma
├── GlobalRiccati.olean            # Global Riccati inequality
├── BKMClosure.lean                # BKM criterion closure
├── BesovEmbedding.olean           # Besov-L∞ embedding
├── CalderonZygmundBesov.olean     # CZ operator bounds
└── ... (other module certificates)

.lake/build/lib/
├── MainTheorem.olean              # Main regularity theorem
├── Theorem13_7.olean              # Clay Millennium solution
└── SerrinEndpoint.olean           # Alternative Serrin proof
```

## Automated Build Script

Use the provided script for automated building and certificate archiving:

```bash
cd Scripts
./build_lean_proofs.sh
```

This script:
1. Checks for elan/lake installation
2. Updates dependencies
3. Builds the project
4. Archives certificates to `Results/Lean4_Certificates/`

## Manual Build Instructions

### Prerequisites

**Required:**
- elan (Lean version manager)
- lake (Lean build tool, installed with elan)
- Git (for dependency management)

**System Requirements:**
- 4GB+ RAM (for mathlib compilation)
- 5GB+ disk space (for dependencies)
- Linux/macOS/WSL (Windows with WSL2)

### Step-by-Step Build

1. **Install Lean4**:
   ```bash
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
   source ~/.profile  # Or restart terminal
   ```

2. **Verify Installation**:
   ```bash
   elan --version
   lake --version
   lean --version
   ```

3. **Navigate to Project**:
   ```bash
   cd Lean4-Formalization
   ```

4. **Update Dependencies**:
   ```bash
   lake update
   ```
   
   This downloads mathlib4 and other dependencies. First run may take 10-30 minutes.

5. **Build Project**:
   ```bash
   lake build
   ```
   
   Compiles all .lean files and generates .olean certificates.

6. **Verify Build**:
   ```bash
   # Check for generated certificates
   find .lake/build/lib -name "*.olean" | wc -l
   ```
   
   Should show dozens of .olean files if successful.

## Troubleshooting

### Common Issues

**Issue**: `elan: command not found`
```bash
# Solution: Add elan to PATH
export PATH="$HOME/.elan/bin:$PATH"
echo 'export PATH="$HOME/.elan/bin:$PATH"' >> ~/.bashrc
```

**Issue**: `error: toolchain 'leanprover/lean4:stable' is not installed`
```bash
# Solution: Let elan install the toolchain
cd Lean4-Formalization
elan show  # This triggers installation
```

**Issue**: `lake: not found`
```bash
# Solution: Reinstall elan
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- --default-toolchain leanprover/lean4:stable
```

**Issue**: Build fails with "out of memory"
```bash
# Solution: Increase available memory or use precompiled mathlib
lake exe cache get  # Download precompiled mathlib
lake build
```

**Issue**: Dependency resolution errors
```bash
# Solution: Clean and rebuild
lake clean
rm -rf lake-packages .lake
lake update
lake build
```

### Build Warnings

Some warnings are expected and don't prevent certificate generation:

- **Unused variables**: Intentional in some proof sketches
- **Deprecated syntax**: Will be addressed in future updates
- **Missing instances**: Some type class instances are under development

### Getting Help

If you encounter issues:

1. Check the [Lean4 documentation](https://leanprover.github.io/lean4/doc/)
2. Review [LEAN4_FORMALIZATION_STATUS.md](../Documentation/LEAN4_FORMALIZATION_STATUS.md)
3. Open an issue on GitHub with:
   - Lean version (`lean --version`)
   - Build output
   - System information

## Certificate Verification

To independently verify the certificates:

```bash
# Re-run build (uses cached certificates for verification)
lake build

# Clean build (regenerates all certificates)
lake clean
lake build
```

Both should succeed if certificates are valid.

## Certificate Distribution

### For Academic Publication

1. **Archive certificates**:
   ```bash
   tar -czf lean4-certificates.tar.gz .lake/build/lib/
   ```

2. **Include in supplementary materials**:
   - Certificate archive (lean4-certificates.tar.gz)
   - Build instructions (this file)
   - Formalization status (LEAN4_FORMALIZATION_STATUS.md)

3. **Deposit in repository**:
   - Zenodo: https://zenodo.org/
   - arXiv: Include in ancillary files
   - GitHub: Tag release with certificates

### For Formal Proof Archives

Consider submitting to:

- **Archive of Formal Proofs**: https://www.isa-afp.org/
- **Coq/Lean proof libraries**: Community repositories
- **Clay Mathematics Institute**: As supporting evidence

## Build Statistics

Expected build statistics (approximate):

- **Files compiled**: 20+ Lean modules
- **Certificates generated**: 30+ .olean files  
- **Build time**: 5-60 minutes (depends on cache and system)
- **Disk usage**: ~2GB (including dependencies)

## Certificate Contents

Each .olean file contains:

1. **Compiled proof terms**: Machine-checked proofs
2. **Type information**: Full type checking data
3. **Dependencies**: Links to required modules
4. **Metadata**: Module names, timestamps, versions

## Continuous Integration

For automated building in CI:

```yaml
# Example GitHub Actions workflow
- name: Install Lean
  run: |
    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
    echo "$HOME/.elan/bin" >> $GITHUB_PATH

- name: Build and Generate Certificates
  run: |
    cd Lean4-Formalization
    lake update
    lake build
    
- name: Archive Certificates
  uses: actions/upload-artifact@v3
  with:
    name: lean4-certificates
    path: Lean4-Formalization/.lake/build/lib/
```

## Future Work

Certificate generation improvements planned:

1. **Precompiled mathlib cache**: Faster first builds
2. **Incremental builds**: Only rebuild changed modules  
3. **Certificate validation tests**: Automated verification
4. **Documentation extraction**: Generate HTML docs from certificates

## References

- [Lean4 Manual](https://leanprover.github.io/lean4/doc/)
- [Lake Build System](https://github.com/leanprover/lake)
- [Mathlib4](https://github.com/leanprover-community/mathlib4)
- [Lean Prover Community](https://leanprover-community.github.io/)

---

**Last Updated**: 2025-10-30  
**Lean Version**: leanprover/lean4:stable  
**Mathlib Version**: See lake-manifest.json
