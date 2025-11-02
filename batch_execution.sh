#!/bin/bash
# ═══════════════════════════════════════════════════════════════
#   BATCH EXECUTION SCRIPT
#   
#   Execute multiple packages in batch mode with priority filtering
# ═══════════════════════════════════════════════════════════════

set -e

# Default values
PRIORITY=""
PACKAGE_DIR="parametric_sweep_packages"
DRY_RUN=false
MAX_PACKAGES=""

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Print usage
usage() {
    echo "Usage: $0 [OPTIONS]"
    echo ""
    echo "Options:"
    echo "  --priority PRIORITY    Run only packages with given priority (HIGH, MEDIUM, LOW)"
    echo "  --max-packages N       Maximum number of packages to run"
    echo "  --package-dir DIR      Package directory (default: parametric_sweep_packages)"
    echo "  --dry-run             Dry run mode (no actual simulations)"
    echo "  -h, --help            Show this help message"
    echo ""
    echo "Examples:"
    echo "  $0 --priority HIGH                  # Run all HIGH priority packages"
    echo "  $0 --priority MEDIUM --max-packages 5   # Run up to 5 MEDIUM priority packages"
    echo "  $0 --dry-run                        # Test run without executing simulations"
    exit 1
}

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --priority)
            PRIORITY="$2"
            shift 2
            ;;
        --max-packages)
            MAX_PACKAGES="$2"
            shift 2
            ;;
        --package-dir)
            PACKAGE_DIR="$2"
            shift 2
            ;;
        --dry-run)
            DRY_RUN=true
            shift
            ;;
        -h|--help)
            usage
            ;;
        *)
            echo "Unknown option: $1"
            usage
            ;;
    esac
done

# Print header
echo ""
echo "═══════════════════════════════════════════════════════════════"
echo "  BATCH EXECUTION"
echo "═══════════════════════════════════════════════════════════════"
echo ""

# Check if package directory exists
if [ ! -d "$PACKAGE_DIR" ]; then
    echo -e "${RED}❌ Package directory not found: $PACKAGE_DIR${NC}"
    echo "   Run 'make generate-packages' first"
    exit 1
fi

# Build command options
CMD_OPTS="--package-dir $PACKAGE_DIR"
if [ -n "$PRIORITY" ]; then
    CMD_OPTS="$CMD_OPTS --priority $PRIORITY"
    echo -e "${BLUE}Priority filter:${NC} $PRIORITY"
fi

if [ "$DRY_RUN" = true ]; then
    CMD_OPTS="$CMD_OPTS --dry-run"
    echo -e "${YELLOW}⚠️  DRY RUN MODE${NC}"
fi

echo ""

# Counter
count=0

# Run packages
while true; do
    # Check if we've hit the max
    if [ -n "$MAX_PACKAGES" ] && [ "$count" -ge "$MAX_PACKAGES" ]; then
        echo ""
        echo -e "${GREEN}✓ Reached maximum package limit ($MAX_PACKAGES)${NC}"
        break
    fi
    
    # Try to run next package
    echo "─────────────────────────────────────────────────────────────"
    echo "Attempting to run package $((count + 1))..."
    echo ""
    
    if python3 run_package.py --next $CMD_OPTS; then
        count=$((count + 1))
        echo ""
        echo -e "${GREEN}✓ Package $count completed${NC}"
    else
        # Check if it failed or just no more packages
        if [ $? -eq 0 ]; then
            echo ""
            echo -e "${GREEN}✓ No more pending packages${NC}"
        else
            echo ""
            echo -e "${RED}❌ Package execution failed${NC}"
        fi
        break
    fi
    
    echo ""
done

# Print summary
echo ""
echo "═══════════════════════════════════════════════════════════════"
echo "  BATCH EXECUTION COMPLETE"
echo "═══════════════════════════════════════════════════════════════"
echo ""
echo -e "${GREEN}Packages executed: $count${NC}"
echo ""

# Show progress
echo "Current progress:"
python3 parametric_sweep_monitor.py --package-dir "$PACKAGE_DIR"

exit 0
