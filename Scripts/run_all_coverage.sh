#!/bin/bash
# Master script to run comprehensive test coverage analysis
# for both Python and Lean4 components

set -e

SCRIPT_DIR="$(dirname "$0")"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

echo "========================================================"
echo "  Comprehensive Test Coverage Analysis"
echo "  3D Navier-Stokes Global Regularity Framework"
echo "========================================================"
echo ""
echo "Repository: $REPO_ROOT"
echo "Date: $(date)"
echo ""

# Create reports directory
REPORTS_DIR="$REPO_ROOT/coverage_reports"
mkdir -p "$REPORTS_DIR"

echo "========================================================"
echo "PART 1: Python Test Coverage"
echo "========================================================"
echo ""

cd "$REPO_ROOT"
bash "$SCRIPT_DIR/run_python_coverage.sh" | tee "$REPORTS_DIR/python_coverage.log"

echo ""
echo "========================================================"
echo "PART 2: Lean4 Formalization Coverage"
echo "========================================================"
echo ""

bash "$SCRIPT_DIR/run_lean_coverage.sh" | tee "$REPORTS_DIR/lean_coverage.log"

echo ""
echo "========================================================"
echo "Coverage Analysis Complete"
echo "========================================================"
echo ""
echo "Reports saved to: $REPORTS_DIR/"
echo "  - Python coverage: $REPORTS_DIR/python_coverage.log"
echo "  - Lean4 coverage: $REPORTS_DIR/lean_coverage.log"
echo "  - Python HTML: coverage_html_report/index.html"
echo "  - Comprehensive report: COVERAGE_REPORT.md"
echo ""
echo "Next steps:"
echo "  1. Review COVERAGE_REPORT.md for detailed analysis"
echo "  2. Check coverage_html_report/index.html for Python details"
echo "  3. Review module contributions in COVERAGE_REPORT.md"
echo ""
echo "========================================================"
