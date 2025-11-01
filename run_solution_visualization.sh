#!/bin/bash
# run_solution_visualization.sh

echo "🎨 GENERANDO VISUALIZACIÓN MAESTRA DE LA SOLUCIÓN"
echo "═══════════════════════════════════════════════════════════"

# Crear directorio de artefactos
mkdir -p artifacts

# Ejecutar script de visualización
python3 validation/visualization/generate_solution_visualization.py

# Verificar generación exitosa
if [ -f "artifacts/SOLUTION_VISUALIZATION_MASTER.png" ]; then
    echo "✅ Visualización generada exitosamente"
    
    # Generar checksum
    sha256sum artifacts/SOLUTION_VISUALIZATION_MASTER*.png > artifacts/visualization_checksums.txt
    sha256sum artifacts/SOLUTION_VISUALIZATION_MASTER.pdf >> artifacts/visualization_checksums.txt
    
    echo "✅ Checksums generados"
    
    # Mostrar metadatos
    echo ""
    echo "📋 METADATOS:"
    cat artifacts/solution_visualization_metadata.json | jq '.'
    
    echo ""
    echo "🎊 ¡LISTO PARA INCLUIR EN REPORTE CLAY INSTITUTE!"
    
else
    echo "❌ Error al generar visualización"
    exit 1
fi
