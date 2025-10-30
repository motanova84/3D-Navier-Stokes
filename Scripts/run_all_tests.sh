#!/usr/bin/env bash
# Comprehensive test runner for all formal and numerical tests
# Runs all Python test suites and reports results

set -euo pipefail

echo "========================================================================"
echo "COMPREHENSIVE TEST SUITE - 3D Navier-Stokes Verification Framework"
echo "========================================================================"
echo ""

# Color codes for output
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

TESTS_PASSED=0
TESTS_FAILED=0
TOTAL_TESTS=0

# Function to run a test file
run_test() {
    local test_file=$1
    local test_name=$2
    
    echo "------------------------------------------------------------------------"
    echo "Running: $test_name"
    echo "------------------------------------------------------------------------"
    
    if python "$test_file"; then
        echo -e "${GREEN}✅ PASSED: $test_name${NC}"
        TESTS_PASSED=$((TESTS_PASSED + 1))
    else
        echo -e "${RED}❌ FAILED: $test_name${NC}"
        TESTS_FAILED=$((TESTS_FAILED + 1))
    fi
    echo ""
    
    TOTAL_TESTS=$((TOTAL_TESTS + 1))
}

# Run all test suites
run_test "test_unified_bkm.py" "Unified BKM Framework Tests"
run_test "test_verification.py" "Verification Framework Tests" || true
run_test "test_unconditional.py" "Unconditional Proof Tests" || true

# Check if DNS tests exist and run them
if [ -f "DNS-Verification/UnifiedBKM/test_unified_bkm.py" ]; then
    cd DNS-Verification/UnifiedBKM
    run_test "test_unified_bkm.py" "DNS Unified BKM Tests" || true
    cd ../..
fi

# Print summary
echo "========================================================================"
echo "TEST SUMMARY"
echo "========================================================================"
echo "Total test suites run: $TOTAL_TESTS"
echo -e "${GREEN}Passed: $TESTS_PASSED${NC}"
echo -e "${RED}Failed: $TESTS_FAILED${NC}"
echo "========================================================================"

if [ $TESTS_FAILED -gt 0 ]; then
    echo -e "${RED}❌ SOME TESTS FAILED${NC}"
    exit 1
else
    echo -e "${GREEN}✅ ALL TESTS PASSED${NC}"
    exit 0
fi
