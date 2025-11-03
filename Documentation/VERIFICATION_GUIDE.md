# End-to-End Verification Guide

This guide explains how to use the end-to-end verification scripts for the 3D Navier-Stokes framework.

## Table of Contents

1. [Overview](#overview)
2. [Quick Start](#quick-start)
3. [Script Reference](#script-reference)
4. [Verification Chain](#verification-chain)
5. [CI/CD Integration](#cicd-integration)
6. [Troubleshooting](#troubleshooting)
7. [Examples](#examples)

---

## Overview

The verification framework provides three main scripts:

1. **`run_all_formal_verifications.sh`** - Complete end-to-end verification
2. **`run_regression_tests.sh`** - Regression testing for CI/CD
3. **`quick_verify.sh`** - Fast checks for development

These scripts ensure reproducibility and validate the entire proof chain from basic definitions to the main theorem.

---

## Quick Start

### For Development

```bash
# Quick check during development (< 1 minute)
./Scripts/quick_verify.sh

# Full verification in quick mode (5-10 minutes)
./Scripts/run_all_formal_verifications.sh --quick

# Skip DNS tests for faster iteration
./Scripts/run_all_formal_verifications.sh --skip-dns
```

### For Testing

```bash
# Complete verification (may take 30+ minutes)
./Scripts/run_all_formal_verifications.sh

# Regression testing
./Scripts/run_regression_tests.sh

# Strict regression testing (no warnings allowed)
./Scripts/run_regression_tests.sh --strict
```

### For CI/CD

```bash
# Create baseline for regression testing
./Scripts/run_regression_tests.sh --save-baseline

# Check against baseline
./Scripts/run_regression_tests.sh --baseline Results/Regression/baseline.json

# Full verification in regression mode
./Scripts/run_all_formal_verifications.sh --regression
```

---

## Script Reference

### run_all_formal_verifications.sh

Complete end-to-end verification from basic definitions to main theorem.

**Usage:**
```bash
./Scripts/run_all_formal_verifications.sh [OPTIONS]
```

**Options:**
- `--skip-lean` - Skip Lean4 formal verification
- `--skip-python` - Skip Python computational verification
- `--skip-dns` - Skip DNS verification (recommended for quick tests)
- `--quick` - Quick mode with reduced test coverage
- `--regression` - Strict validation mode (fails on any incomplete proofs)
- `--help` - Display help message

**Exit Codes:**
- `0` - All verifications passed
- `1` - Lean4 verification failed
- `2` - Python verification failed
- `3` - DNS verification failed
- `4` - Regression tests failed
- `5` - Setup/configuration error

**Execution Phases:**
1. **Phase 1: Environment Setup** - Validates Python, Lean4, dependencies
2. **Phase 2: Lean4 Verification** - Builds formal proofs, checks for `sorry`
3. **Phase 3: Python Verification** - Runs all test suites
4. **Phase 4: DNS Verification** - Executes numerical simulations
5. **Phase 5: Integration Tests** - Validates proof chain integrity
6. **Phase 6: Report Generation** - Creates comprehensive report

**Output:**
- Verification report: `Results/Verification/verification_report_<timestamp>.md`
- Detailed logs: `Results/Verification/logs/`

---

### run_regression_tests.sh

Regression testing designed for CI/CD pipelines to detect breaking changes.

**Usage:**
```bash
./Scripts/run_regression_tests.sh [OPTIONS]
```

**Options:**
- `--baseline FILE` - Compare against baseline results (JSON)
- `--save-baseline` - Save current results as new baseline
- `--strict` - Fail on any warnings
- `--help` - Display help message

**Exit Codes:**
- `0` - All regression tests passed
- `1` - Regressions detected
- `2` - New failures introduced
- `3` - Performance regression detected

**Tests Performed:**
1. Lean4 build regression
2. Python test suite regression
3. Proof completeness check (no `sorry`)
4. Code structure integrity
5. Dependency chain validation
6. Performance benchmarks

**Output:**
- Results JSON: `Results/Regression/results_<timestamp>.json`
- Baseline: `Results/Regression/baseline.json`

---

### quick_verify.sh

Fast verification for development workflow.

**Usage:**
```bash
./Scripts/quick_verify.sh
```

**Checks Performed:**
1. Python syntax validation
2. Import checks
3. Quick test run (one suite)
4. Lean syntax check (if available)
5. File structure validation

**Time:** < 1 minute

---

## Verification Chain

The complete verification follows this dependency structure:

```
Environment Setup
    ↓
BasicDefinitions.lean (NS equations, function spaces)
    ↓
FunctionalSpaces.lean (Sobolev, Besov spaces)
    ↓
EnergyEstimates.lean + VorticityControl.lean
    ↓
MisalignmentDefect.lean (QCAL framework)
    ↓
BKMCriterion.lean (Beale-Kato-Majda)
    ↓
MainTheorem.lean (Global regularity)
    ↓
Python Tests (Computational validation)
    ↓
DNS Verification (Numerical simulation)
```

### Key Components

**Lean4 Formal Verification:**
- Proves theorems from first principles
- Type-checked mathematical statements
- Validates logical consistency

**Python Computational Verification:**
- `test_verification.py` (29 tests) - Core framework
- `test_unified_bkm.py` (19 tests) - BKM approach
- `test_unconditional.py` (11 tests) - Unconditional results

**DNS Verification:**
- Direct Numerical Simulation
- Parameter sweeps (Reynolds number, frequency)
- Vorticity and energy monitoring

---

## CI/CD Integration

### GitHub Actions

The repository includes a comprehensive GitHub Actions workflow at `.github/workflows/verification.yml`.

**Workflow Jobs:**
1. **quick-verification** - Fast sanity checks
2. **lean4-verification** - Formal proof building
3. **python-verification** - Test matrix (Python 3.9-3.12)
4. **full-verification** - Complete end-to-end verification
5. **regression-testing** - Detect regressions on PRs
6. **summary** - Generate status summary

**Triggered on:**
- Push to `main`, `master`, or `develop`
- Pull requests
- Daily schedule (2 AM UTC)
- Manual dispatch

**Artifacts:**
- Verification reports (30 days retention)
- Verification logs (7 days retention)
- Regression results (30 days retention)

### Setting Up CI

1. **First-time setup:**
   ```bash
   # Generate baseline
   ./Scripts/run_regression_tests.sh --save-baseline
   
   # Commit baseline
   git add Results/Regression/baseline.json
   git commit -m "Add regression baseline"
   git push
   ```

2. **Workflow will automatically:**
   - Run verification on every push/PR
   - Update baseline on main branch
   - Generate reports and artifacts

---

## Troubleshooting

### Common Issues

#### "Python3 not found"
```bash
# Install Python 3.9 or higher
sudo apt-get update
sudo apt-get install python3 python3-pip
```

#### "Lake not found" (Lean4)
```bash
# Install Lean4
./Scripts/setup_lean.sh

# Or manually:
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

#### "Module not found" (Python)
```bash
# Install dependencies
pip install -r requirements.txt

# Or minimal set:
pip install numpy scipy
```

#### DNS verification takes too long
```bash
# Skip DNS tests
./Scripts/run_all_formal_verifications.sh --skip-dns

# Or use quick mode
./Scripts/run_all_formal_verifications.sh --quick
```

#### Some tests fail
```bash
# Check specific test output
python3 test_verification.py -v

# View logs
ls -lh Results/Verification/logs/

# Note: Some pre-existing test failures may be expected during development
```

### Debug Mode

For detailed debugging:

```bash
# Enable bash debug output
bash -x Scripts/run_all_formal_verifications.sh

# Check logs
tail -f Results/Verification/logs/verification_<timestamp>.log

# View specific phase logs
cat Results/Verification/logs/lean_build_<timestamp>.log
cat Results/Verification/logs/test_verification_<timestamp>.log
```

---

## Examples

### Example 1: Daily Development Workflow

```bash
# Start development session
cd 3D-Navier-Stokes

# Make changes to Lean files or Python code
vim Lean4-Formalization/NavierStokes/NewFeature.lean

# Quick verification (< 1 minute)
./Scripts/quick_verify.sh

# If quick check passes, run focused tests
python3 test_verification.py

# Before committing, run full verification without DNS
./Scripts/run_all_formal_verifications.sh --skip-dns --quick
```

### Example 2: Pre-commit Verification

```bash
# Full verification before major commit
./Scripts/run_all_formal_verifications.sh

# Check the report
cat Results/Verification/verification_report_*.md

# If all passes, commit
git add .
git commit -m "Add new feature"
git push
```

### Example 3: Release Testing

```bash
# Complete verification with all components
./Scripts/run_all_formal_verifications.sh --regression

# Save as baseline for future
./Scripts/run_regression_tests.sh --save-baseline

# Archive results
tar -czf verification-release-v1.0.tar.gz Results/Verification/
```

### Example 4: Regression Testing in CI

```bash
# In CI pipeline (GitHub Actions)
./Scripts/run_regression_tests.sh \
  --baseline Results/Regression/baseline.json \
  --strict

# If baseline doesn't exist, create it
if [ ! -f "Results/Regression/baseline.json" ]; then
  ./Scripts/run_regression_tests.sh --save-baseline
fi
```

### Example 5: Performance Monitoring

```bash
# Run with timing
time ./Scripts/run_all_formal_verifications.sh --quick

# Compare performance
./Scripts/run_regression_tests.sh --baseline Results/Regression/baseline.json

# Check performance data
cat Results/Regression/results_*/performance.json
```

### Example 6: Selective Verification

```bash
# Only Lean4 verification
./Scripts/run_all_formal_verifications.sh --skip-python --skip-dns

# Only Python tests
./Scripts/run_all_formal_verifications.sh --skip-lean --skip-dns

# Only integration checks
./Scripts/run_all_formal_verifications.sh --skip-lean --skip-python --skip-dns
```

---

## Best Practices

### For Developers

1. **Run quick checks frequently**
   ```bash
   ./Scripts/quick_verify.sh
   ```

2. **Use skip flags during iteration**
   ```bash
   ./Scripts/run_all_formal_verifications.sh --skip-dns
   ```

3. **Full verification before pushing**
   ```bash
   ./Scripts/run_all_formal_verifications.sh --quick
   ```

### For Maintainers

1. **Update baseline after verified changes**
   ```bash
   ./Scripts/run_regression_tests.sh --save-baseline
   git add Results/Regression/baseline.json
   git commit -m "Update regression baseline"
   ```

2. **Review verification reports regularly**
   ```bash
   ls -lt Results/Verification/verification_report_*.md | head -5
   ```

3. **Monitor for incomplete proofs**
   ```bash
   ./Scripts/check_no_sorry.sh
   ```

### For CI/CD

1. **Use quick mode for PR checks**
   ```yaml
   - run: ./Scripts/run_all_formal_verifications.sh --quick --skip-dns
   ```

2. **Full verification on main branch**
   ```yaml
   - run: ./Scripts/run_all_formal_verifications.sh --regression
   ```

3. **Archive artifacts**
   ```yaml
   - uses: actions/upload-artifact@v4
     with:
       name: verification-report
       path: Results/Verification/
   ```

---

## Additional Resources

- **Main README**: [../README.md](../README.md)
- **Theory Documentation**: [../Documentation/THEORY.md](../Documentation/THEORY.md)
- **Installation Guide**: [../Documentation/INSTALL.md](../Documentation/INSTALL.md)
- **Lean4 Documentation**: https://leanprover.github.io/
- **Issue Tracker**: https://github.com/motanova84/3D-Navier-Stokes/issues

---

## Support

If you encounter issues:

1. Check the troubleshooting section above
2. Review verification logs in `Results/Verification/logs/`
3. Open an issue: https://github.com/motanova84/3D-Navier-Stokes/issues

---

**Last Updated:** 2025-10-30

*This guide is part of the 3D Navier-Stokes verification framework.*
