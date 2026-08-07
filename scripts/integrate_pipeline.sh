#!/bin/bash
# ============================================================================
# scripts/integrate_pipeline.sh
# Integración del pipeline de verificación en el repositorio
# ============================================================================

set -e

echo "🌊 NOESIS — Integración del Pipeline de Verificación"
echo "====================================================="

# 1. Estructura de directorios
echo "📁 Creando estructura de directorios..."
mkdir -p src/NOESIS
mkdir -p circuits
mkdir -p contracts
mkdir -p noesis_oracle
mkdir -p scripts
mkdir -p test
mkdir -p docs

# 2. Verificar dependencias
echo "🔍 Verificando dependencias..."

# Lean 4
if command -v lake &> /dev/null; then
    echo "  ✅ Lean 4: lake disponible"
else
    echo "  ❌ Lean 4: lake no disponible"
    exit 1
fi

# Circom
if command -v circom &> /dev/null; then
    echo "  ✅ Circom: disponible"
else
    echo "  ❌ Circom: no disponible"
    exit 1
fi

# Python
if command -v python3 &> /dev/null; then
    echo "  ✅ Python3: disponible"
else
    echo "  ❌ Python3: no disponible"
    exit 1
fi

# 3. Ejecutar pruebas Lean 4
echo "🧪 Ejecutando pruebas..."
lake test

if [ $? -eq 0 ]; then
    echo "  ✅ Pruebas Lean 4 exitosas"
else
    echo "  ❌ Pruebas Lean 4 fallidas"
    exit 1
fi

# 4. Generar documentación
echo "📄 Generando documentación..."
lake build docs

echo "✅ Pipeline de verificación integrado"
echo "  📁 Estructura: lista"
echo "  📐 Lean 4: verificado"
echo "  🔐 Circom: listo"
echo "  🐍 Python: operativo"
