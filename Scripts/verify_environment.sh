#!/bin/bash
# Script de Verificación de Integridad del Entorno
# Environment Integrity Verification Script
# 
# Verifica que el entorno coincida con ENV.lock para garantizar reproducibilidad
# Verifies that the environment matches ENV.lock to ensure reproducibility

set -e

# Colores para output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

echo -e "${BLUE}============================================${NC}"
echo -e "${BLUE}Environment Integrity Verification${NC}"
echo -e "${BLUE}Verificación de Integridad del Entorno${NC}"
echo -e "${BLUE}============================================${NC}"
echo ""

# Get script directory
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
PROJECT_ROOT="$( cd "$SCRIPT_DIR/.." && pwd )"
ENV_LOCK="$PROJECT_ROOT/ENV.lock"

if [ ! -f "$ENV_LOCK" ]; then
    echo -e "${RED}❌ ERROR: ENV.lock not found at $ENV_LOCK${NC}"
    exit 1
fi

echo -e "${GREEN}✓${NC} Found ENV.lock"

# 1. Verify Python version
echo ""
echo -e "${BLUE}[1/5] Checking Python version...${NC}"
PYTHON_VERSION=$(python --version 2>&1 | awk '{print $2}')
PYTHON_MAJOR=$(echo $PYTHON_VERSION | cut -d. -f1)
PYTHON_MINOR=$(echo $PYTHON_VERSION | cut -d. -f2)

if [ "$PYTHON_MAJOR" -eq 3 ] && [ "$PYTHON_MINOR" -ge 9 ]; then
    echo -e "${GREEN}✓${NC} Python $PYTHON_VERSION (required: 3.9+)"
else
    echo -e "${RED}❌ Python $PYTHON_VERSION (required: 3.9+)${NC}"
    exit 1
fi

# 2. Verify Python packages
echo ""
echo -e "${BLUE}[2/5] Checking Python packages...${NC}"

# Extract package versions from ENV.lock
REQUIRED_PACKAGES=(
    "numpy==2.4.0"
    "scipy==1.16.3"
    "matplotlib==3.10.8"
    "sympy==1.14.0"
    "psutil==7.2.1"
    "PyPDF2==3.0.1"
)

MISSING_PACKAGES=()
VERSION_MISMATCH=()

for pkg_spec in "${REQUIRED_PACKAGES[@]}"; do
    pkg_name=$(echo $pkg_spec | cut -d= -f1)
    required_version=$(echo $pkg_spec | cut -d= -f3)
    
    # Check if package is installed
    if pip show "$pkg_name" >/dev/null 2>&1; then
        installed_version=$(pip show "$pkg_name" | grep "^Version:" | awk '{print $2}')
        if [ "$installed_version" == "$required_version" ]; then
            echo -e "${GREEN}✓${NC} $pkg_name $installed_version"
        else
            echo -e "${YELLOW}⚠${NC}  $pkg_name $installed_version (expected: $required_version)"
            VERSION_MISMATCH+=("$pkg_name")
        fi
    else
        echo -e "${RED}❌${NC} $pkg_name (not installed)"
        MISSING_PACKAGES+=("$pkg_name")
    fi
done

# 3. Verify Lean toolchain
echo ""
echo -e "${BLUE}[3/5] Checking Lean toolchain...${NC}"

LEAN_TOOLCHAIN="$PROJECT_ROOT/lean-toolchain"
if [ -f "$LEAN_TOOLCHAIN" ]; then
    REQUIRED_LEAN=$(cat "$LEAN_TOOLCHAIN")
    echo -e "${GREEN}✓${NC} lean-toolchain exists: $REQUIRED_LEAN"
    
    # Check if elan is installed
    if command -v elan >/dev/null 2>&1; then
        echo -e "${GREEN}✓${NC} elan (Lean installer) is available"
    else
        echo -e "${YELLOW}⚠${NC}  elan not found (needed for Lean verification)"
    fi
else
    echo -e "${RED}❌${NC} lean-toolchain not found"
fi

# 4. Verify Lake manifest
echo ""
echo -e "${BLUE}[4/5] Checking Lake manifest...${NC}"

LAKE_MANIFEST="$PROJECT_ROOT/lake-manifest.json"
if [ -f "$LAKE_MANIFEST" ]; then
    # Check if jq is available for JSON parsing
    if command -v jq >/dev/null 2>&1; then
        MANIFEST_VERSION=$(jq -r '.version' "$LAKE_MANIFEST" 2>/dev/null || echo "unknown")
        PACKAGES_COUNT=$(jq -r '.packages | length' "$LAKE_MANIFEST" 2>/dev/null || echo "0")
        echo -e "${GREEN}✓${NC} lake-manifest.json (version: $MANIFEST_VERSION, packages: $PACKAGES_COUNT)"
    else
        echo -e "${GREEN}✓${NC} lake-manifest.json exists"
        echo -e "${YELLOW}⚠${NC}  Install jq for detailed verification"
    fi
else
    echo -e "${RED}❌${NC} lake-manifest.json not found"
fi

# 5. Verify .gitignore
echo ""
echo -e "${BLUE}[5/5] Checking .gitignore configuration...${NC}"

GITIGNORE="$PROJECT_ROOT/.gitignore"
if [ -f "$GITIGNORE" ]; then
    # Check for important entries
    IMPORTANT_ENTRIES=(
        "__pycache__"
        "*.pyc"
        ".lake/"
        "*.h5"
        "artifacts/"
    )
    
    for entry in "${IMPORTANT_ENTRIES[@]}"; do
        if grep -q "$entry" "$GITIGNORE"; then
            echo -e "${GREEN}✓${NC} .gitignore contains: $entry"
        else
            echo -e "${YELLOW}⚠${NC}  .gitignore missing: $entry"
        fi
    done
else
    echo -e "${RED}❌${NC} .gitignore not found"
fi

# Summary
echo ""
echo -e "${BLUE}============================================${NC}"
echo -e "${BLUE}Verification Summary / Resumen${NC}"
echo -e "${BLUE}============================================${NC}"
echo ""

WARNINGS=0
ERRORS=0

if [ ${#MISSING_PACKAGES[@]} -gt 0 ]; then
    echo -e "${RED}Missing Packages (${#MISSING_PACKAGES[@]}):${NC}"
    for pkg in "${MISSING_PACKAGES[@]}"; do
        echo "  - $pkg"
    done
    ERRORS=$((ERRORS + 1))
    echo ""
fi

if [ ${#VERSION_MISMATCH[@]} -gt 0 ]; then
    echo -e "${YELLOW}Version Mismatches (${#VERSION_MISMATCH[@]}):${NC}"
    for pkg in "${VERSION_MISMATCH[@]}"; do
        echo "  - $pkg"
    done
    WARNINGS=$((WARNINGS + 1))
    echo ""
fi

# Final status
if [ $ERRORS -gt 0 ]; then
    echo -e "${RED}❌ VERIFICATION FAILED${NC}"
    echo ""
    echo "To fix missing packages, run:"
    echo "  pip install -r ENV.lock"
    echo ""
    exit 1
elif [ $WARNINGS -gt 0 ]; then
    echo -e "${YELLOW}⚠ VERIFICATION PASSED WITH WARNINGS${NC}"
    echo ""
    echo "Environment is functional but has version mismatches."
    echo "For exact reproducibility, run:"
    echo "  pip install -r ENV.lock"
    echo ""
    exit 0
else
    echo -e "${GREEN}✅ VERIFICATION PASSED${NC}"
    echo ""
    echo "Environment matches ENV.lock specifications."
    echo "Results should be reproducible."
    echo ""
    exit 0
fi
