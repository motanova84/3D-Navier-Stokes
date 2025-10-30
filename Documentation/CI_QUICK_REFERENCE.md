# CI/CD Quick Reference

## Quick Commands

### Run All Tests Locally
```bash
bash Scripts/run_all_tests.sh
```

### Run Individual Test Suites
```bash
# Python tests
python test_unified_bkm.py          # Primary suite (19 tests)
python test_verification.py         # Verification tests (29 tests)
python test_unconditional.py        # Unconditional proof tests

# DNS tests
cd DNS-Verification/UnifiedBKM && python test_unified_bkm.py
```

### Lean4 Tests
```bash
bash Scripts/setup_lean.sh          # First time setup
bash Scripts/build_lean_proofs.sh   # Build all proofs
bash Scripts/check_no_sorry.sh      # Check for incomplete proofs
bash Scripts/lint.sh                # Lint check
```

### Validate Workflows
```bash
bash Scripts/validate_workflows.sh
```

## CI Status

View CI status: [GitHub Actions](https://github.com/motanova84/3D-Navier-Stokes/actions)

## CI Jobs

| Job | Purpose | Critical |
|-----|---------|----------|
| `lean4-formal-verification` | Compiles Lean4 proofs | ✅ Yes |
| `python-numerical-tests` | Runs Python tests | ✅ Yes |
| `integration-summary` | Overall status | ✅ Yes |

## Test Status Summary

| Test Suite | Tests | Status | Critical |
|------------|-------|--------|----------|
| `test_unified_bkm.py` | 19 | ✅ Pass | ✅ Yes |
| `test_verification.py` | 29 | ⚠️ Partial | ⚠️ No |
| `test_unconditional.py` | ~15 | ⚠️ Partial | ⚠️ No |
| `DNS/.../test_unified_bkm.py` | 21 | ✅ Pass | ✅ Yes |

## Troubleshooting

### CI Failed - What to Do?

1. **Check CI logs**: Click "Details" on failed check
2. **Run tests locally**: `bash Scripts/run_all_tests.sh`
3. **Fix issues**: Make corrections
4. **Push again**: CI will re-run automatically

### Common Issues

**Import errors**:
```bash
pip install -r requirements.txt
```

**Lean4 build errors**:
```bash
rm -rf .lake lake-packages
lake update
lake build
```

**Test failures**:
- Check test output for specific error
- Verify mathematical invariants maintained
- Check for API compatibility issues

## Pre-commit Checklist

Before pushing code:

- [ ] Run `bash Scripts/run_all_tests.sh`
- [ ] Ensure at least primary tests pass
- [ ] Update documentation if needed
- [ ] Write clear commit message
- [ ] Check workflow is valid (if modified)

## Documentation

- **Full CI/CD docs**: [Documentation/CI_CD.md](CI_CD.md)
- **Contributing guide**: [CONTRIBUTING.md](../CONTRIBUTING.md)
- **Main README**: [README.md](../README.md)

## Support

- **Issues**: [GitHub Issues](https://github.com/motanova84/3D-Navier-Stokes/issues)
- **Discussions**: [GitHub Discussions](https://github.com/motanova84/3D-Navier-Stokes/discussions)
