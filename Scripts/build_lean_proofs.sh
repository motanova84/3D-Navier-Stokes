#!/usr/bin/env bash
# Build Lean4 proofs and generate certificates
# This script automates the process of building the Lean4 formalization
# and generating .olean certificate files.

set -e  # Exit on error

echo "========================================================================"
echo "  Lean4 Navier-Stokes Formalization - Build and Certificate Generator"
echo "========================================================================"
echo ""

# Setup PATH for elan/lake
export PATH="$HOME/.elan/bin:$PATH"

# Check if elan is installed
if ! command -v elan &> /dev/null; then
    echo "[ERROR] elan (Lean version manager) is not installed."
    echo ""
    echo "To install elan, run:"
    echo "  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh"
    echo ""
    exit 1
fi

echo "[✓] Found elan and lake"
echo ""

# Navigate to Lean4-Formalization directory
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
LEAN_DIR="$PROJECT_ROOT/Lean4-Formalization"

cd "$LEAN_DIR" || exit 1
echo "[✓] Changed to directory: $LEAN_DIR"
echo ""

# Show Lean version
echo "Lean version:"
lean --version || echo "Lean not yet initialized"
echo ""

# Update dependencies
echo "[*] Updating dependencies..."
lake update
echo "[✓] Dependencies updated"
echo ""

# Build the project
echo "[*] Building Lean4 formalization..."
echo "    This may take several minutes on first build (downloading mathlib)..."
echo ""
lake build

if [ $? -eq 0 ]; then
    echo ""
    echo "[✓] Build successful!"
    echo ""
    
    # Check for generated .olean files
    OLEAN_DIR=".lake/build/lib"
    if [ -d "$OLEAN_DIR" ]; then
        echo "Certificate files (.olean) generated:"
        echo ""
        find "$OLEAN_DIR" -name "*.olean" | head -20
        OLEAN_COUNT=$(find "$OLEAN_DIR" -name "*.olean" | wc -l)
        echo ""
        echo "Total: $OLEAN_COUNT certificate files"
        echo ""
        
        # Create certificates archive
        CERT_DIR="$PROJECT_ROOT/Results/Lean4_Certificates"
        mkdir -p "$CERT_DIR"
        
        echo "[*] Archiving certificates..."
        tar -czf "$CERT_DIR/lean4-certificates-$(date +%Y%m%d-%H%M%S).tar.gz" \
            -C "$OLEAN_DIR" .
        
        echo "[✓] Certificates archived to: $CERT_DIR"
        echo ""
    fi
    
    echo "========================================================================"
    echo "  BUILD SUCCESSFUL - Formal verification complete!"
    echo "========================================================================"
    echo ""
    
else
    echo ""
    echo "[✗] Build failed!"
    echo ""
    exit 1
fi
