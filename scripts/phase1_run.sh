#!/usr/bin/env bash
# ============================================================================
# scripts/phase1_run.sh
# Phase 1 benchmark/checkpoint runner for QCAL-Balearic Nowcast
# ============================================================================

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BUILD_DIR="$ROOT_DIR/build"
KERNEL_SRC="$ROOT_DIR/src/kernels/atmosphere.cu"
BENCHMARK_SRC="$ROOT_DIR/src/orchestrator/phase1_benchmark.py"
OUTPUT_JSON="$ROOT_DIR/benchmark_results.json"
CHECKPOINT_NPZ="$ROOT_DIR/checkpoint_initial.npz"

mkdir -p "$BUILD_DIR"

echo "🌊 NOESIS — QCAL-Balearic Phase 1"
echo "================================="
echo "Frecuencia Base: f₀ = 141.7001 Hz"
echo "Coherencia: Ψ = 1.000000"
echo ""

if command -v nvcc >/dev/null 2>&1; then
  echo "📐 Compilando kernel CUDA..."
  nvcc -O3 --use_fast_math -o "$BUILD_DIR/atmosphere_cuda.o" -c "$KERNEL_SRC"
  echo "  ✅ Compilación CUDA completada"
else
  echo "  ⚠️  nvcc no disponible; se omite compilación CUDA y se usa benchmark Python"
fi

echo "🚀 Ejecutando benchmark..."
python3 "$BENCHMARK_SRC" \
  --steps 100 \
  --domain 167 167 60 \
  --dt 10.0 \
  --output "$OUTPUT_JSON" \
  --checkpoint "$CHECKPOINT_NPZ"

echo "🔍 Verificando checkpoint..."
if [[ ! -f "$CHECKPOINT_NPZ" ]]; then
  echo "  ❌ Checkpoint no encontrado"
  exit 1
fi

python3 - "$OUTPUT_JSON" "$CHECKPOINT_NPZ" <<'PY'
import json
import os
import sys

output_json, checkpoint_path = sys.argv[1], sys.argv[2]
with open(output_json, "r", encoding="utf-8") as handle:
    data = json.load(handle)

size_mb = os.path.getsize(checkpoint_path) / (1024 * 1024)
print("")
print("📊 Resumen de métricas:")
print(f"  Backend: {data['backend']}")
print(f"  Tiempo promedio: {data['avg_time_ms']:.2f} ms")
print(f"  Pasos/segundo: {data['steps_per_second']:.2f}")
print(f"  Memoria de campos: {data['field_memory_gb']:.3f} GB")
print(f"  Checkpoint: {checkpoint_path} ({size_mb:.2f} MB)")
PY

echo ""
echo "✅ Fase 1 completada"
echo "  📁 Benchmark: $OUTPUT_JSON"
echo "  📁 Checkpoint: $CHECKPOINT_NPZ"
