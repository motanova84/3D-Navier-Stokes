#!/bin/bash
# Build script for PsiNSE formal verification
# This script should be run in the formal_verification/lean4/ directory
# 
# Prerequisites:
# - Lean 4 toolchain installed (via elan)
# - Lake build tool available

set -e

echo "==================================="
echo "PsiNSE Formal Verification Build"
echo "==================================="

# Navigate to the formal_verification/lean4 directory
cd "$(dirname "$0")"

# Check if lean4 and lake are available
if ! command -v lean &> /dev/null; then
    echo "ERROR: lean is not installed."
    echo "Please install Lean 4 via elan:"
    echo "  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh"
    exit 1
fi

if ! command -v lake &> /dev/null; then
    echo "ERROR: lake is not installed."
    echo "Lake should be installed with Lean 4."
    exit 1
fi

echo "Step 1: Updating dependencies..."
lake update

echo ""
echo "Step 2: Building PsiNSE library..."
lake build

echo ""
echo "Step 3: Running verification..."
lean --make PsiNSE_CompleteLemmas_WithInfrastructure.lean

echo ""
echo "==================================="
echo "Build completed successfully!"
echo "==================================="
