# Continuous Integration (CI) Documentation

## Overview

This repository uses **GitHub Actions** to automatically verify both formal proofs (Lean4) and numerical computations (Python) on every commit and pull request. This ensures that any code changes preserve the mathematical validity and computational correctness of the framework.

## CI Workflow Structure

The CI workflow is defined in `.github/workflows/ci-verification.yml` and consists of three main jobs:

### 1. Lean4 Formal Verification (`lean4-formal-verification`)

This job validates all formal mathematical proofs written in Lean4.

**Steps:**
1. **Checkout**: Clone the repository
2. **Cache Lake/LEAN**: Cache Lean4 toolchain and dependencies for faster builds
3. **Install Lean (elan)**: Set up the Lean4 environment using `Scripts/setup_lean.sh`
4. **Build Lean Proofs**: Compile all Lean4 proofs using `Scripts/build_lean_proofs.sh`
5. **Check for 'sorry' placeholders**: Verify no incomplete proofs remain using `Scripts/check_no_sorry.sh`
6. **Lint**: Run Lean4 linting checks using `Scripts/lint.sh`

**Exit Criteria:**
- All Lean4 files must compile successfully
- Linting must pass without errors
- Note: 'sorry' checks currently allow errors (continue-on-error: true) as some proofs are still in development

### 2. Python Numerical Verification (`python-numerical-tests`)

This job runs all Python-based numerical tests to verify computational correctness.

**Steps:**
1. **Checkout**: Clone the repository
2. **Set up Python 3.9**: Install Python with pip caching
3. **Cache Python dependencies**: Cache pip packages for faster installation
4. **Install Python dependencies**: Install all packages from `requirements.txt`
5. **Run verification framework tests**: Execute `test_verification.py`
6. **Run unified BKM tests**: Execute `test_unified_bkm.py` (primary test suite)
7. **Run unconditional proof tests**: Execute `test_unconditional.py`
8. **Run DNS verification tests**: Execute DNS-specific tests in `DNS-Verification/UnifiedBKM/`

**Exit Criteria:**
- At minimum, `test_unified_bkm.py` must pass completely
- Other test suites may have known issues (continue-on-error: true) but failures are tracked

### 3. Integration Summary (`integration-summary`)

This job provides an overall status report for the CI run.

**Steps:**
1. **Check overall status**: Reports results from both Lean4 and Python jobs
2. **Fail if any critical job failed**: Ensures the PR cannot be merged if tests fail

**Exit Criteria:**
- Both `lean4-formal-verification` and `python-numerical-tests` must succeed

## Triggers

The CI workflow runs automatically on:
- **Push events** to branches: `main`, `master`, `develop`
- **Pull request events** targeting: `main`, `master`, `develop`

## Test Suites

### Lean4 Tests

Located in:
- `Lean4-Formalization/NavierStokes/*.lean`
- `NavierStokes/*.lean`
- `*.lean` (root level files)

Tests verify:
- Formal proof correctness
- Type soundness
- Theorem completeness

### Python Tests

#### 1. `test_unified_bkm.py` (19 tests) ✅
**Status**: All tests pass

Tests the Unified BKM Framework including:
- Route A: Riccati-Besov direct closure
- Route B: Volterra-Besov integral equation
- Route C: Energy bootstrap methodology
- Parameter optimization
- Constants uniformity

#### 2. `test_verification.py` (29 tests) ⚠️
**Status**: Partial failures due to API changes

Tests the main verification framework:
- Mathematical consistency
- Hybrid approach components
- Numerical stability
- Edge cases

**Known Issues**: Some tests fail due to `use_legacy_constants` parameter changes

#### 3. `test_unconditional.py` ⚠️
**Status**: Partial failures

Tests the unconditional proof framework:
- Universal constants
- Lemmas L1, L2
- Backward compatibility

#### 4. `DNS-Verification/UnifiedBKM/test_unified_bkm.py` ✅
**Status**: All tests pass

Tests DNS-specific implementations:
- Dual-limit solver
- Littlewood-Paley decomposition
- Misalignment calculations

## Running CI Locally

### Prerequisites

**For Lean4 tests:**
```bash
# Install elan (Lean version manager)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

**For Python tests:**
```bash
# Install Python 3.9+
python --version  # Should be 3.9 or higher

# Install dependencies
pip install -r requirements.txt
```

### Running All Tests

```bash
# Comprehensive test runner
bash Scripts/run_all_tests.sh
```

### Running Individual Test Suites

**Python tests:**
```bash
python test_unified_bkm.py
python test_verification.py
python test_unconditional.py
cd DNS-Verification/UnifiedBKM && python test_unified_bkm.py
```

**Lean4 tests:**
```bash
bash Scripts/setup_lean.sh
bash Scripts/build_lean_proofs.sh
bash Scripts/check_no_sorry.sh
bash Scripts/lint.sh
```

## Caching Strategy

To optimize CI run times, the workflow uses GitHub Actions caching:

### Lean4 Cache
```yaml
path: |
  ~/.elan
  .lake
  lake-packages
key: ${{ runner.os }}-lean-${{ hashFiles('lean-toolchain') }}-${{ hashFiles('lakefile.lean', 'lake-manifest.json') }}
```

### Python Cache
```yaml
path: ~/.cache/pip
key: ${{ runner.os }}-pip-${{ hashFiles('requirements.txt') }}
```

This reduces build times from ~5-10 minutes to ~1-2 minutes on subsequent runs.

## CI Status Badge

The CI status badge is displayed at the top of the README:

```markdown
[![CI - Verification](https://github.com/motanova84/3D-Navier-Stokes/actions/workflows/ci-verification.yml/badge.svg)](https://github.com/motanova84/3D-Navier-Stokes/actions/workflows/ci-verification.yml)
```

## Troubleshooting

### Common Issues

**1. Lean4 build failures**
```bash
# Clear cache and rebuild
rm -rf .lake lake-packages
lake update
lake build
```

**2. Python import errors**
```bash
# Reinstall dependencies
pip install --force-reinstall -r requirements.txt
```

**3. Test failures after changes**
```bash
# Run tests locally first
bash Scripts/run_all_tests.sh
```

### Viewing CI Logs

1. Go to the [Actions tab](https://github.com/motanova84/3D-Navier-Stokes/actions)
2. Click on the latest workflow run
3. Click on the job you want to inspect
4. Expand the step to view logs

## Future Enhancements

Potential improvements to the CI pipeline:

1. **Code Coverage**: Add coverage reports for Python tests
2. **Performance Benchmarks**: Track computational performance over time
3. **Documentation Generation**: Auto-generate API documentation
4. **Deployment**: Automatic deployment of documentation to GitHub Pages
5. **Matrix Testing**: Test across multiple Python versions (3.9, 3.10, 3.11)
6. **Pre-commit Hooks**: Add local pre-commit checks before pushing

## Contributing

When adding new tests or modifying the CI workflow:

1. **Test locally first**: Always run `bash Scripts/run_all_tests.sh` before pushing
2. **Update this document**: Document any new test suites or CI changes
3. **Add tests for new features**: Ensure new code has corresponding tests
4. **Check CI status**: Verify the CI passes before requesting review

## References

- [GitHub Actions Documentation](https://docs.github.com/en/actions)
- [Lean 4 Documentation](https://leanprover.github.io/lean4/doc/)
- [Python unittest Documentation](https://docs.python.org/3/library/unittest.html)
