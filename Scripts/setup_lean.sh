#!/bin/bash
# Setup script for Lean4 environment

set -e

echo "🚀 Setting up Lean4 environment for Clay Millennium verification..."

# Check for elan (Lean version manager)
if ! command -v elan &> /dev/null; then
    echo "📦 Installing elan (Lean version manager)..."
    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
    source ~/.profile
else
    echo "✅ elan already installed"
fi

# Check for lake (Lean build tool)
if ! command -v lake &> /dev/null; then
    echo "📦 Installing lake..."
    elan install stable
else
    echo "✅ lake already installed"
fi

# Navigate to Lean4-Formalization directory
cd Lean4-Formalization

# Initialize lake project if needed
if [ ! -f "lakefile.lean" ]; then
    echo "📝 Copying lakefile.lean from Configuration..."
    cp ../Configuration/lakefile.lean .
fi

# Update dependencies
echo "📦 Updating Lean dependencies..."
lake update

# Build the project
echo "🔨 Building Lean project..."
lake build

echo "✅ Lean4 environment setup complete!"
echo ""
echo "📁 Project structure:"
find . -name "*.lean" -type f | head -10

echo ""
echo "🎯 Next steps:"
echo "1. Run DNS verification: ./Scripts/run_dns_verification.sh"
echo "2. Build Lean proofs: ./Scripts/build_lean_proofs.sh"
echo "3. Generate Clay report: ./Scripts/generate_clay_report.sh"
