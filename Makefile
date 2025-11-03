# ═══════════════════════════════════════════════════════════════
#   MAKEFILE - PARAMETRIC SWEEP ORCHESTRATION
#   
#   Convenient commands for parametric sweep execution
# ═══════════════════════════════════════════════════════════════

.PHONY: help setup generate-packages list-packages monitor clean
.PHONY: run-next run-package run-batch-high run-batch-medium run-batch-all
.PHONY: run-continuous run-opportunistic test-system

PACKAGE_DIR := parametric_sweep_packages
PYTHON := python3

# Default target
help:
	@echo ""
	@echo "═══════════════════════════════════════════════════════════════"
	@echo "  PARAMETRIC SWEEP ORCHESTRATION - Available Commands"
	@echo "═══════════════════════════════════════════════════════════════"
	@echo ""
	@echo "📦 SETUP & GENERATION:"
	@echo "  make setup              - Initial setup (create directories)"
	@echo "  make generate-packages  - Generate simulation packages"
	@echo "  make list-packages      - List all packages"
	@echo ""
	@echo "▶️  EXECUTION:"
	@echo "  make run-next           - Run next pending package"
	@echo "  make run-package ID=N   - Run specific package by ID"
	@echo "  make run-batch-high     - Run all HIGH priority packages"
	@echo "  make run-batch-medium   - Run all MEDIUM priority packages"
	@echo "  make run-batch-all      - Run all pending packages"
	@echo ""
	@echo "🔄 CONTINUOUS EXECUTION:"
	@echo "  make run-continuous     - Run continuously for 24h"
	@echo "  make run-opportunistic  - Run in opportunistic mode"
	@echo ""
	@echo "📊 MONITORING:"
	@echo "  make monitor            - Show progress report"
	@echo "  make detailed-report    - Generate detailed markdown report"
	@echo ""
	@echo "🧪 TESTING:"
	@echo "  make test-system        - Test system with dry run"
	@echo ""
	@echo "🧹 CLEANUP:"
	@echo "  make clean              - Remove all packages and results"
	@echo "  make clean-results      - Remove only results (keep packages)"
	@echo ""

# Setup
setup:
	@echo "🔧 Setting up parametric sweep system..."
	@mkdir -p $(PACKAGE_DIR)
	@mkdir -p $(PACKAGE_DIR)/results
	@echo "✓ Directories created"

# Generate packages
generate-packages:
	@echo "📦 Generating simulation packages..."
	@$(PYTHON) parametric_sweep_orchestrator.py --output-dir $(PACKAGE_DIR)

# List packages
list-packages:
	@$(PYTHON) parametric_sweep_orchestrator.py --list --output-dir $(PACKAGE_DIR)

list-packages-high:
	@$(PYTHON) parametric_sweep_orchestrator.py --list --priority HIGH --output-dir $(PACKAGE_DIR)

list-packages-medium:
	@$(PYTHON) parametric_sweep_orchestrator.py --list --priority MEDIUM --output-dir $(PACKAGE_DIR)

list-packages-low:
	@$(PYTHON) parametric_sweep_orchestrator.py --list --priority LOW --output-dir $(PACKAGE_DIR)

# Run single package
run-next:
	@$(PYTHON) run_package.py --next --package-dir $(PACKAGE_DIR)

run-next-high:
	@$(PYTHON) run_package.py --next --priority HIGH --package-dir $(PACKAGE_DIR)

run-package:
ifndef ID
	@echo "❌ Error: Package ID not specified"
	@echo "Usage: make run-package ID=0"
	@exit 1
endif
	@$(PYTHON) run_package.py --package-id $(ID) --package-dir $(PACKAGE_DIR)

# Batch execution
run-batch-high:
	@./batch_execution.sh --priority HIGH --package-dir $(PACKAGE_DIR)

run-batch-medium:
	@./batch_execution.sh --priority MEDIUM --package-dir $(PACKAGE_DIR)

run-batch-low:
	@./batch_execution.sh --priority LOW --package-dir $(PACKAGE_DIR)

run-batch-all:
	@./batch_execution.sh --package-dir $(PACKAGE_DIR)

# Continuous execution
run-continuous:
	@$(PYTHON) intelligent_executor.py --continuous 24 --package-dir $(PACKAGE_DIR)

run-continuous-high:
	@$(PYTHON) intelligent_executor.py --continuous 24 --priority HIGH --package-dir $(PACKAGE_DIR)

run-continuous-hours:
ifndef HOURS
	@echo "❌ Error: Hours not specified"
	@echo "Usage: make run-continuous-hours HOURS=12"
	@exit 1
endif
	@$(PYTHON) intelligent_executor.py --continuous $(HOURS) --package-dir $(PACKAGE_DIR)

# Opportunistic execution
run-opportunistic:
	@$(PYTHON) intelligent_executor.py --opportunistic --package-dir $(PACKAGE_DIR)

run-opportunistic-high:
	@$(PYTHON) intelligent_executor.py --opportunistic --priority HIGH --package-dir $(PACKAGE_DIR)

# Monitoring
monitor:
	@$(PYTHON) parametric_sweep_monitor.py --package-dir $(PACKAGE_DIR)

detailed-report:
	@$(PYTHON) parametric_sweep_monitor.py --detailed --package-dir $(PACKAGE_DIR)

watch-progress:
	@while true; do \
		clear; \
		$(PYTHON) parametric_sweep_monitor.py --package-dir $(PACKAGE_DIR); \
		sleep 10; \
	done

# Testing
test-system:
	@echo "🧪 Testing system with dry run..."
	@echo ""
	@echo "1. Generating packages..."
	@$(PYTHON) parametric_sweep_orchestrator.py --output-dir $(PACKAGE_DIR)
	@echo ""
	@echo "2. Running test package (dry run)..."
	@$(PYTHON) run_package.py --package-id 0 --dry-run --package-dir $(PACKAGE_DIR)
	@echo ""
	@echo "3. Checking progress..."
	@$(PYTHON) parametric_sweep_monitor.py --package-dir $(PACKAGE_DIR)
	@echo ""
	@echo "✓ System test complete!"

# Cleanup
clean:
	@echo "🧹 Removing all packages and results..."
	@rm -rf $(PACKAGE_DIR)
	@echo "✓ Cleanup complete"

clean-results:
	@echo "🧹 Removing results (keeping packages)..."
	@rm -rf $(PACKAGE_DIR)/results
	@mkdir -p $(PACKAGE_DIR)/results
	@echo "✓ Results cleared"

# Quick start workflow
quickstart: setup generate-packages
	@echo ""
	@echo "═══════════════════════════════════════════════════════════════"
	@echo "  ✓ QUICKSTART COMPLETE"
	@echo "═══════════════════════════════════════════════════════════════"
	@echo ""
	@echo "Next steps:"
	@echo "  1. Run a test:         make test-system"
	@echo "  2. Execute packages:   make run-batch-high"
	@echo "  3. Monitor progress:   make monitor"
	@echo ""
