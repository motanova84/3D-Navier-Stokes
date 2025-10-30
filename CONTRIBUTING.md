# Contributing to 3D Navier-Stokes Verification Framework

Thank you for your interest in contributing to this project! This document provides guidelines for contributing to the formal and computational verification of the 3D Navier-Stokes equations.

## Table of Contents

- [Getting Started](#getting-started)
- [Development Workflow](#development-workflow)
- [Testing Requirements](#testing-requirements)
- [Continuous Integration](#continuous-integration)
- [Code Standards](#code-standards)
- [Submitting Changes](#submitting-changes)

## Getting Started

### Prerequisites

**For Python Development:**
- Python 3.9 or higher
- pip package manager
- Virtual environment (recommended)

**For Lean4 Formal Proofs:**
- [elan](https://github.com/leanprover/elan) (Lean version manager)
- Lean 4 (installed via elan)

### Setup Development Environment

1. **Clone the repository:**
   ```bash
   git clone https://github.com/motanova84/3D-Navier-Stokes.git
   cd 3D-Navier-Stokes
   ```

2. **Install Python dependencies:**
   ```bash
   pip install -r requirements.txt
   ```

3. **Install Lean4 (optional, for formal proofs):**
   ```bash
   bash Scripts/setup_lean.sh
   ```

## Development Workflow

### 1. Create a Branch

Create a feature branch for your changes:
```bash
git checkout -b feature/your-feature-name
```

### 2. Make Changes

Make your changes to the codebase, following the [Code Standards](#code-standards).

### 3. Test Locally

**IMPORTANT:** Always test your changes locally before pushing:

```bash
# Run all Python tests
bash Scripts/run_all_tests.sh

# Run specific test suite
python test_unified_bkm.py
python test_verification.py
python test_unconditional.py

# Build Lean4 proofs (if applicable)
bash Scripts/build_lean_proofs.sh
```

### 4. Commit Changes

Write clear, descriptive commit messages:
```bash
git add .
git commit -m "Add feature: brief description of changes"
```

### 5. Push and Create Pull Request

```bash
git push origin feature/your-feature-name
```

Then create a pull request on GitHub.

## Testing Requirements

### Python Tests

All Python code changes must:
1. **Pass existing tests**: Run `bash Scripts/run_all_tests.sh`
2. **Include new tests**: Add tests for new functionality
3. **Maintain test coverage**: Don't reduce coverage

**Test Structure:**
- Unit tests: Test individual functions and classes
- Integration tests: Test component interactions
- Numerical tests: Verify mathematical correctness

**Writing Tests:**
```python
import unittest

class TestYourFeature(unittest.TestCase):
    def setUp(self):
        # Initialize test fixtures
        pass
    
    def test_your_functionality(self):
        # Test your code
        result = your_function()
        self.assertTrue(result)
```

### Lean4 Proofs

All Lean4 changes must:
1. **Compile successfully**: Run `bash Scripts/build_lean_proofs.sh`
2. **Not introduce 'sorry'**: No incomplete proofs
3. **Pass linting**: Run `bash Scripts/lint.sh`

## Continuous Integration

### CI Pipeline

The repository uses GitHub Actions for automated testing. The CI pipeline runs on:
- Every push to `main`, `master`, `develop` branches
- Every pull request to these branches

**CI Jobs:**
1. **Lean4 Formal Verification**: Compiles and validates Lean4 proofs
2. **Python Numerical Tests**: Runs all Python test suites
3. **Integration Summary**: Reports overall status

### CI Requirements for PRs

Before your PR can be merged:
- ✅ Lean4 formal verification must pass
- ✅ Python numerical tests must pass (at least `test_unified_bkm.py`)
- ✅ No new 'sorry' placeholders in Lean4 code
- ✅ Code passes linting checks

### Viewing CI Results

1. Go to your PR on GitHub
2. Scroll to the bottom to see CI status checks
3. Click "Details" to view logs if tests fail
4. Fix any failures and push new commits

## Code Standards

### Python Style

- Follow [PEP 8](https://www.python.org/dev/peps/pep-0008/) style guide
- Use descriptive variable and function names
- Add docstrings to all classes and functions
- Keep functions focused and modular

**Example:**
```python
def compute_riccati_coefficient(j: int, params: dict) -> float:
    """
    Compute the Riccati coefficient for frequency level j.
    
    Args:
        j: Frequency level (integer)
        params: Dictionary containing physical parameters
        
    Returns:
        float: Riccati coefficient α_j
    """
    # Implementation
    pass
```

### Lean4 Style

- Follow Lean 4 naming conventions
- Document complex proofs with comments
- Break large proofs into lemmas
- Use meaningful theorem names

**Example:**
```lean
/-- Global Riccati inequality with universal constants -/
theorem global_riccati_universal (ν : ℝ) (c_star C_str : ℝ) :
  ∃ γ > 0, ∀ t, 
    deriv (‖ω t‖_{B⁰_{∞,1}}) ≤ -γ * ‖ω t‖_{B⁰_{∞,1}}^2 + K :=
by
  -- Proof
  sorry
```

### Documentation

- Update README.md if adding new features
- Add comments for complex algorithms
- Update relevant documentation in `Documentation/`
- Include examples for new functionality

## Submitting Changes

### Pull Request Process

1. **Ensure tests pass locally**
2. **Write a clear PR description:**
   - What changes were made
   - Why they were made
   - How to test them
   - Any known issues

3. **Reference related issues:**
   - Use `Fixes #123` to close issues automatically

4. **Request review:**
   - Tag appropriate reviewers
   - Respond to feedback promptly

### PR Description Template

```markdown
## Description
Brief description of changes

## Type of Change
- [ ] Bug fix
- [ ] New feature
- [ ] Documentation update
- [ ] Performance improvement
- [ ] Test addition

## Testing
- [ ] All existing tests pass
- [ ] New tests added (if applicable)
- [ ] Tested locally

## Checklist
- [ ] Code follows project style guidelines
- [ ] Documentation updated
- [ ] CI passes
```

## Types of Contributions

### 1. Bug Fixes

- Report bugs via GitHub Issues
- Include minimal reproducible example
- Propose fixes via PR

### 2. New Features

- Discuss major changes in an issue first
- Ensure feature aligns with project goals
- Include comprehensive tests
- Update documentation

### 3. Documentation

- Improve clarity and completeness
- Add examples
- Fix typos and formatting
- Translate documentation (if applicable)

### 4. Performance Improvements

- Profile before and after changes
- Document performance gains
- Ensure correctness is maintained

### 5. Test Additions

- Increase test coverage
- Add edge case tests
- Improve test clarity

## Community Guidelines

- Be respectful and constructive
- Help others learn and grow
- Provide detailed feedback
- Acknowledge contributions

## Getting Help

- **Questions**: Open a GitHub Discussion
- **Bugs**: Open a GitHub Issue
- **Security**: Email maintainers privately

## License

By contributing, you agree that your contributions will be licensed under the MIT License.

## References

- [Continuous Integration Documentation](Documentation/CI_CD.md)
- [Project README](README.md)
- [GitHub Actions Documentation](https://docs.github.com/en/actions)

---

Thank you for contributing to the 3D Navier-Stokes Verification Framework!
