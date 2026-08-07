#!/usr/bin/env bash
#===============================================================================
# quick_verify.sh
# 
# Quick verification script for rapid testing during development
# Runs essential checks without full DNS simulations
# 
# Usage:
#   ./Scripts/quick_verify.sh
#
# Exit codes:
#   0: Quick verification passed
#   1: Quick verification failed
#===============================================================================

set -euo pipefail

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

echo -e "${BLUE}╔════════════════════════════════════════════════╗${NC}"
echo -e "${BLUE}║  Quick Verification - Essential Checks        ║${NC}"
echo -e "${BLUE}╚════════════════════════════════════════════════╝${NC}"
echo ""

cd "${PROJECT_ROOT}"

# Check 1: Python syntax
echo -n "Checking Python syntax... "
if python3 -m py_compile test_verification.py test_unified_bkm.py 2>/dev/null; then
    echo -e "${GREEN}✓${NC}"
else
    echo -e "${RED}✗${NC}"
    exit 1
fi

# Check 2: Import checks
echo -n "Checking Python imports... "
if python3 -c "import verification_framework; import numpy; import scipy" 2>/dev/null; then
    echo -e "${GREEN}✓${NC}"
else
    echo -e "${YELLOW}⚠${NC} (some imports missing, installing...)"
    pip install -q numpy scipy 2>/dev/null || true
fi

# Check 3: Quick test run (just one test file)
echo -n "Running quick test suite... "
if timeout 30 python3 test_verification.py 2>&1 | grep -q "OK"; then
    echo -e "${GREEN}✓${NC}"
else
    echo -e "${RED}✗${NC}"
    echo "Run full test suite for details: python3 test_verification.py"
    exit 1
fi

# Check 4: Lean syntax check (if available)
if command -v lean &> /dev/null; then
    echo -n "Checking Lean syntax... "
    export PATH="$HOME/.elan/bin:$PATH"
    if lean --version > /dev/null 2>&1; then
        # Just check one file for quick validation
        if lean Lean4-Formalization/MainTheorem.lean --no-build 2>/dev/null; then
            echo -e "${GREEN}✓${NC}"
        else
            echo -e "${YELLOW}⚠${NC} (use 'lake build' for full check)"
        fi
    fi
else
    echo -e "${YELLOW}Lean not installed, skipping Lean checks${NC}"
fi

# Check 5: File structure
echo -n "Checking file structure... "
missing=0
for file in "Scripts/run_all_formal_verifications.sh" "README.md" "lakefile.lean"; do
    if [ ! -f "${file}" ]; then
        missing=1
    fi
done

if [ $missing -eq 0 ]; then
    echo -e "${GREEN}✓${NC}"
else
    echo -e "${RED}✗${NC}"
    exit 1
fi

echo ""
echo -e "${GREEN}✅ Quick verification passed!${NC}"
echo ""
echo "For full verification, run: ./Scripts/run_all_formal_verifications.sh --quick"
exit 0
