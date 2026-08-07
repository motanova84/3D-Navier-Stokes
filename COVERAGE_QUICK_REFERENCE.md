# Test Coverage Quick Reference

## Overview

This guide provides quick instructions for running and interpreting test coverage reports for the 3D Navier-Stokes verification framework.

## Quick Start

### Run All Coverage Reports
```bash
./Scripts/run_all_coverage.sh
```

### Python Coverage Only
```bash
./Scripts/run_python_coverage.sh
```

### Lean4 Coverage Only
```bash
./Scripts/run_lean_coverage.sh
```

## Interpreting Results

### Python Coverage

**Terminal Output:**
```
Name                                      Stmts   Miss   Cover   Missing
------------------------------------------------------------------------
verification_framework/final_proof.py      287    196  31.71%   29-30, 99-102, ...
verification_framework/__init__.py           6      0 100.00%
------------------------------------------------------------------------
TOTAL                                     1308   1012  22.63%
```

**Columns:**
- `Stmts`: Total statements in the file
- `Miss`: Statements not covered by tests
- `Cover`: Percentage coverage
- `Missing`: Line numbers not covered

**HTML Report:**
- Open `coverage_html_report/index.html` in a browser
- Interactive view with color-coded source files
- Red lines: not executed
- Green lines: executed

### Lean4 Coverage

**Terminal Output:**
```
Module: BKMCriterion
  - Definitions/Theorems: 3
  - Proofs: 3
  - Axioms: 0
```

**Metrics:**
- `Definitions/Theorems`: Count of formal statements
- `Proofs`: Count of completed proofs
- `Axioms`: Count of axiomatized statements (should minimize)

## Coverage Goals

### Python
| Module Category | Target Coverage | Priority |
|----------------|-----------------|----------|
| verification_framework | ≥90% | Critical |
| DualLimitSolver | ≥85% | High |
| UnifiedBKM | ≥85% | High |
| Benchmarking | ≥75% | Medium |
| Visualization | ≥60% | Low |

### Lean4
- **No `sorry` statements:** 100% proof completeness
- **Minimize axioms:** Prove rather than axiomatize where possible
- **Test coverage:** Examples and counterexamples for all theorems

## CI/CD Integration

Coverage runs automatically on:
- Every push to main/master/develop branches
- Every pull request

**Check Results:**
- GitHub Actions → "Test Coverage" workflow
- Coverage summary in PR comments
- Codecov dashboard for trends

## Troubleshooting

### Common Issues

**Problem:** Coverage fails with "invalid character" error
```
Couldn't parse 'file.py' as Python source: "invalid character '₀'"
```
**Solution:** Add the file to the omit list in `.coveragerc` or `Scripts/run_python_coverage.sh`

**Problem:** Test failures skew coverage results
**Solution:** Fix failing tests first. Coverage is most meaningful when tests pass.

**Problem:** Lean coverage shows "lake not installed"
**Solution:** Run `bash Scripts/setup_lean.sh` to install Lean4, or review static analysis output

### Getting Help

1. Review `COVERAGE_REPORT.md` for detailed documentation
2. Check test logs: `coverage_reports/*.log`
3. Review CI/CD workflow: `.github/workflows/coverage.yml`

## File Locations

### Generated Reports
- `coverage_html_report/` - Python HTML report
- `coverage.xml` - Python XML report (for CI)
- `coverage_reports/` - Log files from coverage runs

### Configuration
- `.coveragerc` - Python coverage configuration
- `.github/workflows/coverage.yml` - CI/CD workflow

### Scripts
- `Scripts/run_python_coverage.sh` - Python coverage runner
- `Scripts/run_lean_coverage.sh` - Lean4 coverage analyzer
- `Scripts/run_all_coverage.sh` - Master coverage script

### Documentation
- `COVERAGE_REPORT.md` - Comprehensive coverage analysis
- `COVERAGE_QUICK_REFERENCE.md` - This file

## Best Practices

### For Developers

1. **Run coverage before committing:**
   ```bash
   ./Scripts/run_python_coverage.sh
   ```

2. **Review your changes:**
   - Check HTML report for your modified files
   - Ensure new code has test coverage
   - Add tests for uncovered lines

3. **Write testable code:**
   - Keep functions small and focused
   - Minimize side effects
   - Use dependency injection for testability

### For Reviewers

1. **Check coverage in PRs:**
   - Review coverage report in PR comments
   - Ensure new features have tests
   - Flag significant coverage drops

2. **Validate critical paths:**
   - Core algorithms should have high coverage
   - Edge cases should be tested
   - Error handling should be covered

### For Test Authors

1. **Focus on critical paths:**
   - Test main functionality first
   - Add edge cases and error conditions
   - Include regression tests

2. **Use descriptive test names:**
   ```python
   def test_riccati_coefficient_negative_at_high_frequencies(self):
       """Test that α_j < 0 for j ≥ j_d"""
   ```

3. **Document test coverage:**
   - Explain what each test verifies
   - Note any limitations or assumptions
   - Link to relevant theory in comments

## Advanced Usage

### Filter Coverage by Module
```bash
python -m coverage report --include="verification_framework/*"
```

### Generate Coverage for Specific Tests
```bash
python -m coverage run -m unittest test_verification.TestFinalProof
python -m coverage report
```

### Compare Coverage Over Time
```bash
# Run coverage and save
./Scripts/run_python_coverage.sh
cp coverage.xml coverage_baseline.xml

# Make changes...

# Run coverage again
./Scripts/run_python_coverage.sh

# Compare (requires coverage-diff tool)
coverage-diff coverage_baseline.xml coverage.xml
```

## Module Contribution Summary

### Python Modules

**verification_framework/** - Core proof framework
- Implements mathematical theorems
- Validates universal constants
- Orchestrates proof steps

**DNS-Verification/DualLimitSolver/** - Numerical solver
- Three-route BKM framework
- Dual-limit scaling optimization
- Real-time monitoring

**DNS-Verification/UnifiedBKM/** - High-level framework
- Route A: Riccati-Besov closure
- Route B: Volterra integral equation
- Route C: Energy bootstrap

### Lean4 Modules

**NavierStokes/** - Formal verification
- BasicDefinitions: Core mathematical objects
- BKMCriterion: Main regularity theorem
- CalderonZygmundBesov: Key inequality
- RiccatiBesov: Damping analysis
- UnifiedBKM: Top-level theorem

See `COVERAGE_REPORT.md` for detailed module contributions.

## References

- Python Coverage: https://coverage.readthedocs.io/
- Lean4 Documentation: https://lean-lang.org/
- Testing Best Practices: See `Documentation/`

---

**Last Updated:** 2025-10-30  
**Version:** 1.0
