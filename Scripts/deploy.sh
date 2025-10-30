#!/bin/bash

# Script de despliegue automático
echo "🚀 Desplegando framework Navier-Stokes QCAL..."

# Verificar dependencias
if ! command -v lean &> /dev/null; then
    echo "📥 Lean4 no encontrado. Para instalarlo, ejecute:"
    echo "curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh"
    echo "Saltando instalación de Lean4..."
fi

# Configurar entorno Python
echo "🐍 Configurando entorno Python..."

if command -v conda &> /dev/null; then
    echo "Usando Conda..."
    conda env create -f Configuration/environment.yml -y 2>/dev/null || \
    conda env update -f Configuration/environment.yml -y
    echo "Para activar el entorno: conda activate navier-stokes-qcal"
else
    echo "Conda no encontrado. Usando pip..."
    pip install -r Configuration/requirements.txt
fi

# Crear directorios de resultados
echo "📁 Creando directorios de resultados..."
mkdir -p Results/Figures
mkdir -p Results/Data

# Construir proyecto Lean (si Lean está disponible)
if command -v lean &> /dev/null; then
    echo "🧠 Compilando formalización Lean4..."
    cd Lean4-Formalization
    lake build 2>/dev/null || echo "⚠️  Lean4 build requiere configuración adicional"
    cd ..
fi

echo "✅ Despliegue básico completado!"
echo ""
echo "📊 Próximos pasos:"
echo "  1. Activar entorno: conda activate navier-stokes-qcal (si usa Conda)"
echo "  2. Ejecutar tests: python Computational-Verification/Benchmarking/convergence_tests.py"
echo "  3. Ver resultados: ls Results/Figures/"
echo ""
echo "📖 Para más información, consulte Documentation/README.md"
