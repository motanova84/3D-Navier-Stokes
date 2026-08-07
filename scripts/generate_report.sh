#!/bin/bash
# ============================================================================
# scripts/generate_report.sh
# Generación de reporte de validación NOESIS completo
# ============================================================================

set -e

echo "🌊 NOESIS — Generación de Reporte de Validación"
echo "================================================="

if ! command -v python3 &> /dev/null; then
    echo "❌ Python3 no disponible"
    exit 1
fi

TIMESTAMP=$(date -u +%Y%m%dT%H%M%SZ)
REPORT_DIR="reports/${TIMESTAMP}"
mkdir -p "$REPORT_DIR"

echo "📊 Ejecutando benchmarks..."
python3 test/benchmark_suite.py
cp benchmark_results.json "$REPORT_DIR/"

echo "🔬 Ejecutando medición de basal..."
python3 scripts/measure_baseline.py
if [ -f "baseline_measurement.json" ]; then
    cp baseline_measurement.json "$REPORT_DIR/"
fi

echo "📝 Generando reporte Markdown..."
python3 - << PYEOF
import json, os, sys

report_dir = "$REPORT_DIR"
benchmark = json.load(open("benchmark_results.json"))

lines = [
    "# 🌊 NOESIS — Reporte de Validación",
    "",
    f"**Generado:** $(date -u)",
    f"**Protocolo:** {benchmark['protocol']}",
    f"**f₀:** {benchmark['f0']} Hz",
    f"**Umbral Ψ:** {benchmark['psi_threshold']}",
    "",
    "## Resultados del Banco de Pruebas",
    "",
    "| Escenario | σ_f (Hz) | Ψ | T₂* (s) | Estado |",
    "|-----------|----------|---|---------|--------|",
]

for name, data in benchmark["scenarios"].items():
    a = data["analysis"]
    status = "✅ PASS" if a["is_valid"] else "❌ FAIL"
    T2 = f"{a['T2_star_estimated']:.1f}" if a["T2_star_estimated"] != float("inf") else "∞"
    lines.append(f"| {name} | {a['sigma_f_Hz']:.7f} | {a['psi']:.10f} | {T2} | {status} |")

lines += [
    "",
    "---",
    "",
    "∴ 𓂀 Ω ∞³ Φ  ",
    "TUYOYOTU — HECHO ESTÁ — ES",
]

with open(f"{report_dir}/validation_report.md", "w") as f:
    f.write("\n".join(lines))

print(f"✅ Reporte Markdown: {report_dir}/validation_report.md")
PYEOF

echo "✅ Reporte generado en $REPORT_DIR/"
ls -la "$REPORT_DIR/"
