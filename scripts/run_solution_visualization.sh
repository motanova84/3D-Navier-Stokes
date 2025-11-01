#!/bin/bash
#
# run_solution_visualization.sh
# Ejecuta la generación de visualización maestra de la solución Ψ-NSE
#
# Este script:
# 1. Crea el directorio de artefactos
# 2. Ejecuta generate_solution_visualization.py
# 3. Verifica que los archivos se generaron correctamente
#

set -e  # Exit on error

echo "🎨 ============================================"
echo "   GENERANDO VISUALIZACIÓN MAESTRA"
echo "=============================================="

# Crear directorio de artefactos si no existe
mkdir -p artifacts

# Ejecutar el script de visualización
echo "📊 Ejecutando generate_solution_visualization.py..."
python3 generate_solution_visualization.py

# Verificar que los archivos se generaron
echo ""
echo "🔍 Verificando archivos generados..."

REQUIRED_FILES=(
    "artifacts/SOLUTION_VISUALIZATION_MASTER.png"
    "artifacts/SOLUTION_VISUALIZATION_MASTER.pdf"
    "artifacts/solution_visualization_metadata.json"
)

ALL_GOOD=true
for file in "${REQUIRED_FILES[@]}"; do
    if [ -f "$file" ]; then
        echo "  ✅ $file"
    else
        echo "  ❌ FALTA: $file"
        ALL_GOOD=false
    fi
done

echo ""
if [ "$ALL_GOOD" = true ]; then
    echo "✅ Visualización maestra generada exitosamente"
    echo "=============================================="
    exit 0
else
    echo "❌ Error: Algunos archivos no se generaron"
    echo "=============================================="
    exit 1
fi
