#!/usr/bin/env bash
# Build Lean4 proofs and generate verifiable certificates
# This script extends the original build process to automatically generate
# cryptographic certificates for third-party verification

set -euxo pipefail
export PATH="$HOME/.elan/bin:$PATH"

echo "======================================================================"
echo "BUILDING LEAN4 PROOFS WITH CERTIFICATE GENERATION"
echo "======================================================================"
echo ""

# Build the project
echo "🔨 Building Lean4 project..."
lake update
lake build 2>&1 | tee build.log

echo ""
echo "✅ Build complete"
echo ""

# Generate verification certificates
echo "🔒 Generating proof certificates..."
python3 Scripts/generate_proof_certificates.py

echo ""
echo "======================================================================"
echo "BUILD AND CERTIFICATE GENERATION COMPLETE"
echo "======================================================================"
echo ""
echo "Next steps:"
echo "  1. Review certificates in Results/Lean4_Certificates/"
echo "  2. Verify certificates: python3 Scripts/verify_proof_certificates.py"
echo "  3. Share certificates for third-party verification"
echo ""
