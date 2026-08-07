#!/bin/bash
# validate_formalization_structure.sh
# Validates that all required Lean4 formalization files are present

set -e

echo "🔍 VALIDACIÓN DE ESTRUCTURA DE FORMALIZACIÓN LEAN4"
echo "═══════════════════════════════════════════════════════════════"
echo ""

LEAN4_DIR="Lean4-Formalization"
ERRORS=0

# Function to check if file exists
check_file() {
    local file="$1"
    local description="$2"
    
    if [ -f "$LEAN4_DIR/$file" ]; then
        echo "✅ $description"
        return 0
    else
        echo "❌ FALTA: $description ($file)"
        ERRORS=$((ERRORS + 1))
        return 1
    fi
}

# Function to check if directory exists
check_dir() {
    local dir="$1"
    local description="$2"
    
    if [ -d "$LEAN4_DIR/$dir" ]; then
        echo "✅ $description"
        return 0
    else
        echo "❌ FALTA: $description ($dir)"
        ERRORS=$((ERRORS + 1))
        return 1
    fi
}

echo "📋 Verificando módulos principales en $LEAN4_DIR/:"
echo ""

# Main root-level modules
check_file "NavierStokes.lean" "Módulo principal NavierStokes.lean"
check_file "PsiNSE_Production_NoSorry.lean" "Prueba estructural Ψ-NSE"
check_file "DyadicRiccati.lean" "Desigualdad de Riccati diádica"
check_file "ParabolicCoercivity.lean" "Lema de coercividad parabólica"
check_file "MisalignmentDefect.lean" "Defecto de desalineación δ*"
check_file "UnifiedBKM.lean" "Marco unificado BKM"
check_file "SerrinEndpoint.lean" "Endpoint de Serrin"
check_file "Theorem13_7.lean" "Teorema 13.7"
check_file "MainTheorem.lean" "Teorema principal"
check_file "Tests.lean" "Suite de pruebas"

echo ""
echo "📋 Verificando directorios de submódulos:"
echo ""

# Check subdirectories
check_dir "NavierStokes" "Directorio NavierStokes/"
check_dir "PsiNSE" "Directorio PsiNSE/"

echo ""
echo "📋 Verificando archivos clave en NavierStokes/:"
echo ""

# Key NavierStokes submodules
check_file "NavierStokes/BasicDefinitions.lean" "Definiciones básicas"
check_file "NavierStokes/UniformConstants.lean" "Constantes universales"
check_file "NavierStokes/FunctionalSpaces.lean" "Espacios funcionales"
check_file "NavierStokes/MisalignmentDefect.lean" "Defecto de desalineación (submódulo)"
check_file "NavierStokes/DyadicRiccati.lean" "Riccati diádico (submódulo)"
check_file "NavierStokes/ParabolicCoercivity.lean" "Coercividad parabólica (submódulo)"
check_file "NavierStokes/UnifiedBKM.lean" "BKM unificado (submódulo)"
check_file "NavierStokes/BKMCriterion.lean" "Criterio BKM"
check_file "NavierStokes/BesovEmbedding.lean" "Incrustaciones de Besov"
check_file "NavierStokes/GlobalRiccati.lean" "Riccati global"
check_file "NavierStokes/VibrationalRegularization.lean" "Regularización vibracional"

echo ""
echo "📋 Verificando subdirectorios de Foundation:"
echo ""

check_dir "NavierStokes/Foundation" "Foundation (NavierStokes)"
check_dir "PsiNSE/Foundation" "Foundation (PsiNSE)"

echo ""
echo "📋 Verificando archivos de configuración y documentación:"
echo ""

check_file "lakefile.lean" "Archivo de configuración Lake"
if [ -f "lean-toolchain" ]; then
    echo "✅ Especificación de versión Lean"
else
    echo "❌ FALTA: Especificación de versión Lean (lean-toolchain)"
    ERRORS=$((ERRORS + 1))
fi
check_file "CERTIFICATES.md" "Guía de certificados"
check_file "FORMALIZATION_STATUS.md" "Reporte de estado"
check_file "README.md" "Documentación principal"

echo ""
echo "📋 Verificando scripts de verificación:"
echo ""

if [ -f "verify_no_sorry.sh" ]; then
    echo "✅ Script verify_no_sorry.sh"
else
    echo "❌ FALTA: Script verify_no_sorry.sh"
    ERRORS=$((ERRORS + 1))
fi

if [ -f "check_no_axiom.py" ]; then
    echo "✅ Script check_no_axiom.py"
else
    echo "❌ FALTA: Script check_no_axiom.py"
    ERRORS=$((ERRORS + 1))
fi

echo ""
echo "═══════════════════════════════════════════════════════════════"

if [ $ERRORS -eq 0 ]; then
    echo "✅ ¡ÉXITO! Todos los archivos requeridos están presentes"
    echo ""
    echo "📊 Estadísticas:"
    echo "   Archivos .lean en Lean4-Formalization/: $(find $LEAN4_DIR -name "*.lean" | wc -l)"
    echo "   Módulos principales: 10"
    echo "   Submódulos NavierStokes: ~25"
    echo "   Submódulos PsiNSE: ~10"
    echo ""
    echo "🎉 Estructura de formalización VALIDADA"
    exit 0
else
    echo "⚠️  Se encontraron $ERRORS archivos faltantes"
    echo ""
    echo "Por favor, verifica que todos los módulos necesarios estén presentes."
    exit 1
fi
