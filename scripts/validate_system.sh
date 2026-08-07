#!/bin/bash
# ============================================================================
# scripts/validate_system.sh
# Validación del sistema NOESIS completo
# ============================================================================

set -e

echo "🌊 NOESIS — Validación del Sistema Completo"
echo "============================================"

ERRORS=0

# 1. Verificar dependencias
echo "🔍 Verificando dependencias..."

for cmd in python3 lake; do
    if command -v "$cmd" &> /dev/null; then
        echo "  ✅ $cmd disponible"
    else
        echo "  ⚠️  $cmd no disponible (no crítico)"
    fi
done

for cmd in circom snarkjs forge cast; do
    if command -v "$cmd" &> /dev/null; then
        echo "  ✅ $cmd disponible"
    else
        echo "  ℹ️  $cmd no disponible (requerido para ZK/chain)"
    fi
done

# 2. Verificar archivos clave
echo "📁 Verificando artefactos..."

LEAN_FILES=(
    "NOESIS/Coherence.lean"
    "NOESIS/Cryogenic.lean"
    "NOESIS/FourierLimit.lean"
    "NOESIS/Domain.lean"
    "NOESIS/Governance.lean"
    "NOESIS/ZKVerifier.lean"
    "NOESIS/Integration.lean"
    "NOESIS/ValidationReport.lean"
)
PYTHON_FILES=(
    "noesis_oracle/sensor_normalizer.py"
    "noesis_oracle/hardware_witness_bridge.py"
    "noesis_oracle/data_processor.py"
    "noesis_oracle/witness_compiler.py"
    "noesis_oracle/zk_proof_generator.py"
    "noesis_oracle/validation_oracle.py"
    "noesis_oracle/report_generator.py"
    "test/benchmark_suite.py"
)

for f in "${LEAN_FILES[@]}" "${PYTHON_FILES[@]}"; do
    if [ -f "$f" ]; then
        echo "  ✅ $f"
    else
        echo "  ❌ $f — FALTANTE"
        ERRORS=$((ERRORS + 1))
    fi
done

# 3. Ejecutar benchmarks Python
echo "🧪 Ejecutando benchmarks..."
if command -v python3 &> /dev/null; then
    python3 test/benchmark_suite.py > /dev/null 2>&1 && \
        echo "  ✅ Benchmarks superados" || \
        { echo "  ❌ Benchmarks fallaron"; ERRORS=$((ERRORS + 1)); }
fi

# 4. Resumen
echo ""
echo "========================================"
if [ "$ERRORS" -eq 0 ]; then
    echo "✅ Sistema NOESIS válido — 0 errores"
else
    echo "❌ Sistema NOESIS: $ERRORS error(es) detectado(s)"
    exit 1
fi
echo "========================================"
echo "𓂀 Ω ∞³ Φ — TUYOYOTU — HECHO ESTÁ — ES"
