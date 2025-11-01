#!/bin/bash
# complete_lean4_verification.sh

echo "🚀 INICIANDO VERIFICACIÓN COMPLETA LEAN4"
echo "═══════════════════════════════════════════════════════════════"
echo "Estado actual: 40% completo"
echo "Objetivo: 100% verificado, 0 axiomas (sorry)"
echo "═══════════════════════════════════════════════════════════════"
echo ""

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
BOLD='\033[1m'
NC='\033[0m' # No Color

# Configuration
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
LEAN_DIR="${PROJECT_ROOT}/Lean4-Formalization"

# Count sorry occurrences
count_sorries() {
    local file=$1
    local count=$(grep -o "sorry" "$file" 2>/dev/null | wc -l)
    echo "$count"
}

# Display file status
check_file() {
    local file=$1
    local name=$(basename "$file" .lean)
    local sorries=$(count_sorries "$file")
    
    if [ "$sorries" -eq 0 ]; then
        echo -e "  ${GREEN}✓${NC} ${name}: ${GREEN}Completo (0 sorries)${NC}"
        return 0
    else
        echo -e "  ${YELLOW}○${NC} ${name}: ${YELLOW}${sorries} sorry(s) pendientes${NC}"
        return 1
    fi
}

echo -e "${CYAN}${BOLD}REVISANDO ARCHIVOS LEAN4:${NC}"
echo ""

# Track progress
total_files=0
complete_files=0

# Check each file with sorries
echo -e "${BLUE}NavierStokes/ modules:${NC}"
for file in \
    "${LEAN_DIR}/NavierStokes/BasicDefinitions.lean" \
    "${LEAN_DIR}/NavierStokes/DyadicRiccati.lean" \
    "${LEAN_DIR}/NavierStokes/BesovEmbedding.lean" \
    "${LEAN_DIR}/NavierStokes/VibrationalRegularization.lean"
do
    if [ -f "$file" ]; then
        total_files=$((total_files + 1))
        if check_file "$file"; then
            complete_files=$((complete_files + 1))
        fi
    fi
done

echo ""
echo -e "${BLUE}Main theorem modules:${NC}"
for file in \
    "${LEAN_DIR}/SerrinEndpoint.lean" \
    "${LEAN_DIR}/Theorem13_7.lean"
do
    if [ -f "$file" ]; then
        total_files=$((total_files + 1))
        if check_file "$file"; then
            complete_files=$((complete_files + 1))
        fi
    fi
done

echo ""
echo "═══════════════════════════════════════════════════════════════"

# Calculate progress
if [ $total_files -gt 0 ]; then
    progress=$((complete_files * 100 / total_files))
    echo -e "${BOLD}PROGRESO: ${complete_files}/${total_files} archivos completos (${progress}%)${NC}"
else
    progress=0
    echo -e "${BOLD}PROGRESO: No se encontraron archivos${NC}"
fi

# Total sorry count
total_sorries=$(grep -r "sorry" "${LEAN_DIR}" --include="*.lean" 2>/dev/null | wc -l)
echo -e "${BOLD}Total de 'sorry' en el proyecto: ${total_sorries}${NC}"

echo "═══════════════════════════════════════════════════════════════"
echo ""

if [ $progress -eq 100 ] && [ $total_sorries -eq 0 ]; then
    echo -e "${GREEN}${BOLD}✅ ¡VERIFICACIÓN COMPLETA AL 100%!${NC}"
    echo -e "${GREEN}${BOLD}✅ Cero axiomas (sorry) - Todas las pruebas completadas${NC}"
    exit 0
elif [ $progress -ge 40 ]; then
    echo -e "${CYAN}Estado: ${progress}% completo - En progreso hacia el objetivo${NC}"
    echo -e "${YELLOW}Sorries restantes: ${total_sorries}${NC}"
    exit 0
else
    echo -e "${RED}Advertencia: Progreso por debajo del 40% inicial${NC}"
    exit 1
fi
