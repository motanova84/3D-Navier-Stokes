#!/bin/bash
# ============================================================================
# scripts/run_benchmarks.sh
# Ejecución del banco de pruebas sintéticas NOESIS
# ============================================================================

set -e

echo "🌊 NOESIS — Banco de Pruebas Sintéticas"
echo "========================================"

if ! command -v python3 &> /dev/null; then
    echo "❌ Python3 no disponible"
    exit 1
fi

echo "🧪 Ejecutando benchmark_suite.py..."
python3 test/benchmark_suite.py

if [ -f "benchmark_results.json" ]; then
    echo "📊 Resultados:"
    python3 - << 'EOF'
import json, sys
with open("benchmark_results.json") as f:
    r = json.load(f)
valid = sum(1 for s in r["scenarios"].values() if s["analysis"]["is_valid"])
total = len(r["scenarios"])
print(f"  Escenarios válidos: {valid}/{total}")
for name, data in r["scenarios"].items():
    a = data["analysis"]
    status = "✅ PASS" if a["is_valid"] else "❌ FAIL"
    print(f"  {name:<25} Ψ={a['psi']:.10f}  {status}")
EOF
    echo "✅ Resultados guardados en benchmark_results.json"
else
    echo "❌ benchmark_results.json no generado"
    exit 1
fi
