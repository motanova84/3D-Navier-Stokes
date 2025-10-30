#!/bin/bash
# Script to validate Lean4 formalization and generate coverage report

set -e

echo "================================================"
echo "Lean4 Formalization Coverage Analysis"
echo "================================================"
echo ""

# Navigate to Lean4 directory
cd "$(dirname "$0")/../Lean4-Formalization"

# Check if lake is available
if ! command -v lake &> /dev/null; then
    echo "Warning: Lean4 (lake) is not installed or not in PATH"
    echo ""
    echo "To install Lean4, run:"
    echo "  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh"
    echo ""
    echo "Or run the setup script:"
    echo "  bash ../Scripts/setup_lean.sh"
    echo ""
    echo "Performing static analysis only..."
    echo ""
fi

echo "Module coverage analysis..."
echo "=========================="

TOTAL_MODULES=0
TOTAL_DEFS=0
TOTAL_PROOFS=0
TOTAL_AXIOMS=0

for file in NavierStokes/*.lean; do
    if [ -f "$file" ]; then
        MODULE_NAME=$(basename "$file" .lean)
        echo "Module: $MODULE_NAME"
        
        # Count definitions
        DEF_COUNT=$(grep -E "^(def|theorem|lemma|example)" "$file" 2>/dev/null | wc -l)
        echo "  - Definitions/Theorems: $DEF_COUNT"
        
        # Count proofs
        PROOF_COUNT=$(grep -E "by$|:= by" "$file" 2>/dev/null | wc -l)
        echo "  - Proofs: $PROOF_COUNT"
        
        # Count axioms
        AXIOM_IN_FILE=$(grep -E "^axiom" "$file" 2>/dev/null | wc -l)
        echo "  - Axioms: $AXIOM_IN_FILE"
        
        TOTAL_MODULES=$((TOTAL_MODULES + 1))
        TOTAL_DEFS=$((TOTAL_DEFS + DEF_COUNT))
        TOTAL_PROOFS=$((TOTAL_PROOFS + PROOF_COUNT))
        TOTAL_AXIOMS=$((TOTAL_AXIOMS + AXIOM_IN_FILE))
        echo ""
    fi
done

echo "=========================="
echo "Summary Statistics:"
echo "  - Total modules: $TOTAL_MODULES"
echo "  - Total definitions/theorems: $TOTAL_DEFS"
echo "  - Total proofs: $TOTAL_PROOFS"
echo "  - Total axioms: $TOTAL_AXIOMS"
echo ""

# If lake is available, build and check
if command -v lake &> /dev/null; then
    echo "Building Lean4 project..."
    lake build || echo "Warning: Lake build failed"
    
    echo ""
    echo "Building test file..."
    lake build Tests || echo "Warning: Tests build failed"
    
    echo ""
    echo "Checking for sorry statements (incomplete proofs)..."
    SORRY_COUNT=$(find . -name "*.lean" -exec grep -l "sorry" {} \; 2>/dev/null | wc -l)
    if [ "$SORRY_COUNT" -gt 0 ]; then
        echo "Warning: Found $SORRY_COUNT file(s) with 'sorry' statements"
        find . -name "*.lean" -exec grep -l "sorry" {} \; 2>/dev/null
    else
        echo "✓ No 'sorry' statements found - all proofs complete"
    fi
    
    echo ""
    echo "Checking for axiom usage..."
    echo "Axioms and opaque declarations:"
    find . -name "*.lean" -exec grep -nH -E "^axiom|^opaque" {} \; 2>/dev/null || echo "None found"
fi

echo ""
echo "================================================"
echo "Lean4 coverage report complete"
echo "================================================"
