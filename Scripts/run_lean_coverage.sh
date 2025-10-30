#!/bin/bash
# Script to validate Lean4 formalization and generate coverage report

set -e

echo "================================================"
echo "Lean4 Formalization Coverage Analysis"
echo "================================================"
echo ""

# Navigate to Lean4 directory
cd "$(dirname "$0")/../Lean4-Formalization"

echo "Building Lean4 project..."
lake build

echo ""
echo "Running Lean4 tests..."
lake build Tests

echo ""
echo "Checking for sorry statements (incomplete proofs)..."
SORRY_COUNT=$(find . -name "*.lean" -exec grep -l "sorry" {} \; | wc -l)
if [ "$SORRY_COUNT" -gt 0 ]; then
    echo "Warning: Found $SORRY_COUNT file(s) with 'sorry' statements"
    find . -name "*.lean" -exec grep -l "sorry" {} \;
else
    echo "✓ No 'sorry' statements found - all proofs complete"
fi

echo ""
echo "Checking for axiom usage..."
AXIOM_COUNT=$(find . -name "*.lean" -exec grep -E "^axiom|^opaque" {} \; | wc -l)
echo "Found $AXIOM_COUNT axiom/opaque declarations"
if [ "$AXIOM_COUNT" -gt 0 ]; then
    echo "Axioms and opaque declarations:"
    find . -name "*.lean" -exec grep -nH -E "^axiom|^opaque" {} \;
fi

echo ""
echo "Module coverage analysis..."
echo "=========================="

TOTAL_MODULES=0
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
        echo ""
    fi
done

echo "=========================="
echo "Total modules analyzed: $TOTAL_MODULES"
echo ""
echo "================================================"
echo "Lean4 coverage report complete"
echo "================================================"
