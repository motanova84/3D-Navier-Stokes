#!/bin/bash
# batch_execution.sh
# Batch execution script for parameter sweep packages

set -euo pipefail

# Default values
MODE="sequential"
PRIORITY="ALL"
MAX_PARALLEL=1
PACKAGE_DIR="parametric_sweep_packages"

# Color codes
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m' # No Color

# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --mode)
            MODE="$2"
            shift 2
            ;;
        --priority)
            PRIORITY="$2"
            shift 2
            ;;
        --max-parallel)
            MAX_PARALLEL="$2"
            shift 2
            ;;
        --package-dir)
            PACKAGE_DIR="$2"
            shift 2
            ;;
        --help)
            echo "Usage: $0 [OPTIONS]"
            echo ""
            echo "Options:"
            echo "  --mode MODE              Execution mode: sequential or parallel (default: sequential)"
            echo "  --priority PRIORITY      Priority filter: HIGH, MEDIUM, LOW, or ALL (default: ALL)"
            echo "  --max-parallel N         Maximum parallel jobs for parallel mode (default: 1)"
            echo "  --package-dir DIR        Package directory (default: parametric_sweep_packages)"
            echo "  --help                   Show this help message"
            exit 0
            ;;
        *)
            echo "Unknown option: $1"
            echo "Use --help for usage information"
            exit 1
            ;;
    esac
done

# Display banner
echo -e "${BLUE}╔═══════════════════════════════════════════════════════════════╗${NC}"
echo -e "${BLUE}║  BATCH EXECUTION - PARAMETRIC SWEEP                          ║${NC}"
echo -e "${BLUE}╚═══════════════════════════════════════════════════════════════╝${NC}"
echo ""
echo "Configuration:"
echo "  Mode: $MODE"
echo "  Priority: $PRIORITY"
echo "  Max Parallel: $MAX_PARALLEL"
echo "  Package Directory: $PACKAGE_DIR"
echo ""

# Check if package directory exists
if [ ! -d "$PACKAGE_DIR" ]; then
    echo -e "${RED}❌ Error: Package directory not found: $PACKAGE_DIR${NC}"
    echo "Run 'python3 parametric_sweep_orchestrator.py' first to generate packages."
    exit 1
fi

# Get list of packages to run based on priority
get_packages_by_priority() {
    local priority=$1
    local packages=()
    
    for package_file in "$PACKAGE_DIR"/package_*.json; do
        if [ -f "$package_file" ] && [[ "$package_file" =~ package_[0-9]+\.json$ ]]; then
            # Extract package priority and status
            pkg_priority=$(python3 -c "import json; pkg=json.load(open('$package_file')); print(pkg.get('priority', ''))" 2>/dev/null)
            pkg_status=$(python3 -c "import json; pkg=json.load(open('$package_file')); print(pkg.get('status', ''))" 2>/dev/null)
            pkg_id=$(python3 -c "import json; pkg=json.load(open('$package_file')); print(pkg.get('id', ''))" 2>/dev/null)
            
            # Filter by priority and status (only if all fields exist)
            if [ -n "$pkg_priority" ] && [ -n "$pkg_status" ] && [ -n "$pkg_id" ]; then
                if [ "$pkg_status" = "pending" ]; then
                    if [ "$priority" = "ALL" ] || [ "$pkg_priority" = "$priority" ]; then
                        packages+=("$pkg_id")
                    fi
                fi
            fi
        fi
    done
    
    echo "${packages[@]}"
}

# Sequential execution
run_sequential() {
    local packages=($1)
    local total=${#packages[@]}
    local current=0
    
    echo -e "${YELLOW}📋 Running $total packages sequentially...${NC}"
    echo ""
    
    for pkg_id in "${packages[@]}"; do
        current=$((current + 1))
        echo -e "${BLUE}[$current/$total] Running package $pkg_id...${NC}"
        
        if python3 run_package.py --package-id "$pkg_id"; then
            echo -e "${GREEN}✅ Package $pkg_id completed${NC}"
        else
            echo -e "${RED}❌ Package $pkg_id failed${NC}"
        fi
        echo ""
    done
    
    echo -e "${GREEN}✅ Sequential execution completed!${NC}"
}

# Parallel execution
run_parallel() {
    local packages=($1)
    local max_parallel=$2
    local total=${#packages[@]}
    
    echo -e "${YELLOW}📋 Running $total packages in parallel (max $max_parallel simultaneous)...${NC}"
    echo ""
    
    local pids=()
    local current=0
    
    for pkg_id in "${packages[@]}"; do
        current=$((current + 1))
        
        # Wait if we've reached max parallel jobs
        while [ ${#pids[@]} -ge $max_parallel ]; do
            # Check for completed jobs
            for i in "${!pids[@]}"; do
                if ! kill -0 "${pids[$i]}" 2>/dev/null; then
                    wait "${pids[$i]}"
                    unset 'pids[$i]'
                fi
            done
            pids=("${pids[@]}")  # Reindex array
            sleep 1
        done
        
        # Start new job
        echo -e "${BLUE}[$current/$total] Starting package $pkg_id...${NC}"
        (python3 run_package.py --package-id "$pkg_id" > "$PACKAGE_DIR/logs/package_${pkg_id}.log" 2>&1) &
        pids+=($!)
    done
    
    # Wait for all remaining jobs
    echo -e "${YELLOW}⏳ Waiting for remaining jobs to complete...${NC}"
    for pid in "${pids[@]}"; do
        wait "$pid"
    done
    
    echo -e "${GREEN}✅ Parallel execution completed!${NC}"
}

# Create logs directory
mkdir -p "$PACKAGE_DIR/logs"

# Get packages to run
PACKAGES=$(get_packages_by_priority "$PRIORITY")

if [ -z "$PACKAGES" ]; then
    echo -e "${YELLOW}⚠️  No pending packages found with priority: $PRIORITY${NC}"
    exit 0
fi

# Run based on mode
if [ "$MODE" = "sequential" ]; then
    run_sequential "$PACKAGES"
elif [ "$MODE" = "parallel" ]; then
    run_parallel "$PACKAGES" "$MAX_PARALLEL"
else
    echo -e "${RED}❌ Error: Invalid mode: $MODE${NC}"
    echo "Valid modes: sequential, parallel"
    exit 1
fi

echo ""
echo -e "${GREEN}╔═══════════════════════════════════════════════════════════════╗${NC}"
echo -e "${GREEN}║  BATCH EXECUTION COMPLETED                                    ║${NC}"
echo -e "${GREEN}╚═══════════════════════════════════════════════════════════════╝${NC}"
