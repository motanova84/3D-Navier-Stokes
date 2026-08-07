#!/usr/bin/env bash
# ============================================================================
# scripts/certify_system.sh
# Synthetic/local certification runner for QCAL-Balearic Nowcast
# ============================================================================

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BASELINE_PATH="${BASELINE_PATH:-$ROOT_DIR/data/verification/baseline}"
QCAL_PATH="${QCAL_PATH:-$ROOT_DIR/data/verification/qcal}"
OBS_PATH="${OBS_PATH:-$ROOT_DIR/data/verification/observations}"
REPORT_PATH="${REPORT_PATH:-$ROOT_DIR/verification_report.json}"
CERT_PATH="${CERT_PATH:-$ROOT_DIR/CERTIFICATION.md}"

MODULES=(
  "src/forecast/temporal_predictor.py"
  "src/forecast/nowcasting_engine.py"
  "src/assimilation/enkf.py"
  "src/assimilation/qcal_coupling.py"
  "src/data/frontier_ingestion.py"
  "src/data/quality_control.py"
  "src/verification/operational_verification.py"
)

echo "🌊 NOESIS — QCAL-Balearic Nowcast"
echo "=================================="
echo "Frecuencia Base: f₀ = 141.7001 Hz"
echo "Coherencia: Ψ = 1.000000"
echo ""

echo "🔍 Verificando módulos del sistema..."
for module in "${MODULES[@]}"; do
  if [[ -f "$ROOT_DIR/$module" ]]; then
    echo "  ✅ $module"
  else
    echo "  ❌ $module — no encontrado"
    exit 1
  fi
done

echo ""
echo "📊 Ejecutando verificación operacional..."
python3 "$ROOT_DIR/src/verification/operational_verification.py" \
  --baseline "$BASELINE_PATH" \
  --qcal "$QCAL_PATH" \
  --observations "$OBS_PATH" \
  --output "$REPORT_PATH"

CERT_STATUS="$(python3 - "$REPORT_PATH" <<'PY'
import json, sys
with open(sys.argv[1], "r", encoding="utf-8") as handle:
    report = json.load(handle)
print(report["summary"]["certification"])
PY
)"

if [[ "$CERT_STATUS" != "PASSED" ]]; then
  echo "  ❌ Certificación pendiente"
  exit 1
fi

echo ""
echo "📄 Generando acta final..."
python3 - "$REPORT_PATH" "$CERT_PATH" <<'PY'
import json, sys
from datetime import datetime, UTC

report_path, cert_path = sys.argv[1], sys.argv[2]
with open(report_path, "r", encoding="utf-8") as handle:
    report = json.load(handle)

skill_score = report["skill_score"]
with open(cert_path, "w", encoding="utf-8") as handle:
    handle.write("# 🌊 QCAL-Balearic Nowcast — Certificación Final\n\n")
    handle.write(f"- Fecha de certificación: {datetime.now(UTC).isoformat()}\n")
    handle.write("- Frecuencia base: 141.7001 Hz\n")
    handle.write("- Coherencia objetivo: 0.999999\n")
    handle.write(f"- Estado: {report['summary']['status']}\n\n")
    handle.write("## Skill Score\n")
    for key, value in skill_score.items():
        handle.write(f"- {key}: {value:.6f}\n")
PY

echo "✅ Certificación completada"
echo "  📄 Reporte: $REPORT_PATH"
echo "  📄 Acta: $CERT_PATH"
