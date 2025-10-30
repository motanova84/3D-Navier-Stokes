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

# Generate terminal report
python -m coverage report -m

# Generate HTML report
python -m coverage html

# Generate XML report (for CI/CD)
python -m coverage xml

echo ""
echo "================================================"
echo "Coverage report saved to:"
echo "  - Terminal output above"
echo "  - HTML: coverage_html_report/index.html"
echo "  - XML: coverage.xml"
echo "================================================"
