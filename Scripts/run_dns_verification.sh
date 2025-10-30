#!/bin/bash
# DNS verification pipeline for Clay Millennium submission

set -e

echo "🔬 Starting DNS verification for Clay Millennium Problem..."

# Setup Python environment
if [ ! -d "venv" ]; then
    echo "📦 Creating Python virtual environment..."
    python3 -m venv venv
fi

source venv/bin/activate

echo "📦 Installing Python dependencies..."
pip install -q -r Configuration/requirements.txt

# Create results directories
mkdir -p Results/DNS_Data
mkdir -p Results/ClaySubmission

# Run DNS verification
echo ""
echo "🌊 Running DNS verification..."
echo "Parameters:"
echo "  - Reynolds numbers: 100, 500, 1000"
echo "  - Frequencies: 100, 200, 500 Hz"
echo "  - Grid: 64³ (reduced for testing)"
echo ""

python3 DNS-Verification/DualLimitSolver/psi_ns_solver.py

echo ""
echo "✅ DNS verification complete!"
echo "📊 Results saved to Results/DNS_Data/"
echo ""
echo "🎯 Next steps:"
echo "1. Review verification results"
echo "2. Run convergence tests"
echo "3. Generate Clay report: ./Scripts/generate_clay_report.sh"
