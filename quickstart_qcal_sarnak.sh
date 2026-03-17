#!/bin/bash
# Quick Start Guide for QCAL-Sarnak ∞³ Framework

echo "============================================================"
echo "QCAL-Sarnak ∞³ Framework - Quick Start"
echo "============================================================"
echo ""

# Check Python dependencies
echo "Checking Python dependencies..."
if ! python3 -c "import numpy" 2>/dev/null; then
    echo "Installing Python dependencies..."
    pip install -q numpy matplotlib scipy
fi
echo "✅ Python dependencies OK"
echo ""

# Run computational validation
echo "============================================================"
echo "Running Computational Validation"
echo "============================================================"
python3 qcal_sarnak_validation.py
echo ""

# Run tests
echo "============================================================"
echo "Running Tests"
echo "============================================================"
python3 test_qcal_sarnak_validation.py
echo ""

# Summary
echo "============================================================"
echo "Quick Start Complete"
echo "============================================================"
echo ""
echo "For more information, see:"
echo "  - QCAL_SARNAK_README.md - Detailed documentation"
echo "  - QCAL_SARNAK_IMPLEMENTATION_SUMMARY.md - Implementation summary"
echo ""
echo "Lean4 modules:"
echo "  - QCAL/ErdosUlam.lean - Infinite sets with rational distances"
echo "  - QCAL/SarnakPrinciple.lean - Möbius orthogonality"
echo "  - QCAL/NLSEquation.lean - Modified NLS equation"
echo ""
echo "To build Lean4 code (requires Lake):"
echo "  lake build QCAL"
echo ""
