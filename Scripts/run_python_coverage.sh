#!/bin/bash
# Script to run Python tests with coverage analysis

set -e

echo "================================================"
echo "Python Test Coverage Analysis"
echo "================================================"
echo ""

# Navigate to repository root
cd "$(dirname "$0")/.."

# Ensure coverage is installed
if ! python -m coverage --version > /dev/null 2>&1; then
    echo "Installing coverage..."
    pip install coverage --quiet
fi

echo "Running tests with coverage..."
echo ""

# Run coverage for all test files
python -m coverage erase

# Run tests with coverage
python -m coverage run -m unittest discover -s . -p "test_*.py" -v

echo ""
echo "Generating coverage reports..."
echo ""

# Files with unicode characters (subscripts like ₀) that coverage can't parse
# These files contain mathematical notation in variable names and are excluded
# to prevent parsing errors. They are still tested indirectly through their APIs.
OMIT_FILES="*psi_ns_solver.py,*misalignment_calc.py,*riccati_monitor.py,*convergence_tests.py,*besov_norms.py,*kolmogorov_scale.py"

# Generate terminal report
python -m coverage report -m --omit="$OMIT_FILES"

# Generate HTML report
python -m coverage html --omit="$OMIT_FILES"

# Generate XML report (for CI/CD)
python -m coverage xml --omit="$OMIT_FILES"

echo ""
echo "================================================"
echo "Coverage report saved to:"
echo "  - Terminal output above"
echo "  - HTML: coverage_html_report/index.html"
echo "  - XML: coverage.xml"
echo "================================================"
