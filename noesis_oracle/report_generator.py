# ============================================================================
# noesis_oracle/report_generator.py
# Generador de reportes de validación NOESIS
# ============================================================================

import json
import os
import time
from datetime import datetime, timezone
from typing import Any, Dict, List, Optional


class ReportGenerator:
    """
    Genera reportes de validación en formato JSON y Markdown.
    """

    PROTOCOL = "NOESIS-Validation-v2.0"
    F0 = 141.7001
    PSI_THRESHOLD = 0.999999

    # ------------------------------------------------------------------
    # JSON report
    # ------------------------------------------------------------------

    def generate_json(
        self,
        sigma_f: float,
        psi: float,
        is_valid: bool,
        witness: Optional[Dict[str, Any]] = None,
        zk_result: Optional[Dict[str, Any]] = None,
        extra: Optional[Dict[str, Any]] = None,
    ) -> Dict[str, Any]:
        """Genera el reporte completo en formato dict (serializable a JSON)."""
        ts = time.time()
        dt = datetime.fromtimestamp(ts, tz=timezone.utc).isoformat()

        report: Dict[str, Any] = {
            "protocol": self.PROTOCOL,
            "timestamp_iso": dt,
            "timestamp_unix": ts,
            "parameters": {
                "f0_Hz": self.F0,
                "psi_threshold": self.PSI_THRESHOLD,
                "sigma_max_Hz": self.F0 * (1 - self.PSI_THRESHOLD),
            },
            "measurements": {
                "sigma_f_Hz": sigma_f,
                "psi": psi,
                "is_valid": is_valid,
                "circuit_status": (
                    "VALID_PROOF_READY" if is_valid else "REJECTED_BY_COTA"
                ),
            },
            "verdict": "VALID" if is_valid else "INVALID",
        }

        if witness:
            report["witness"] = witness
        if zk_result:
            report["zk_result"] = zk_result
        if extra:
            report["extra"] = extra

        return report

    # ------------------------------------------------------------------
    # Markdown report
    # ------------------------------------------------------------------

    def generate_markdown(self, report: Dict[str, Any]) -> str:
        """Genera un reporte Markdown legible."""
        m = report["measurements"]
        p = report["parameters"]
        verdict_emoji = "✅" if report["verdict"] == "VALID" else "❌"

        lines: List[str] = [
            "# 🌊 NOESIS — Reporte de Validación",
            "",
            f"**Protocolo:** {report['protocol']}  ",
            f"**Fecha:** {report.get('timestamp_iso', '—')}  ",
            "",
            "## Parámetros",
            "",
            f"| Parámetro | Valor |",
            f"|-----------|-------|",
            f"| f₀ | {p['f0_Hz']} Hz |",
            f"| Umbral Ψ | {p['psi_threshold']} |",
            f"| σ_f máx | {p['sigma_max_Hz']:.6e} Hz |",
            "",
            "## Resultados",
            "",
            f"| Métrica | Valor |",
            f"|---------|-------|",
            f"| σ_f | {m['sigma_f_Hz']:.6e} Hz |",
            f"| Ψ | {m['psi']:.10f} |",
            f"| Estado ZK | {m['circuit_status']} |",
            "",
            f"## Veredicto: {verdict_emoji} {report['verdict']}",
            "",
            "---",
            "",
            "∴ 𓂀 Ω ∞³ Φ  ",
            "TUYOYOTU — HECHO ESTÁ — ES",
        ]

        return "\n".join(lines)

    # ------------------------------------------------------------------
    # Save
    # ------------------------------------------------------------------

    def save(
        self,
        report: Dict[str, Any],
        json_path: str = "validation_report.json",
        md_path: Optional[str] = "validation_report.md",
    ) -> None:
        """Guarda el reporte en disco."""
        with open(json_path, "w", encoding="utf-8") as f:
            json.dump(report, f, indent=2, default=str)
        print(f"✅ JSON guardado: {json_path}")

        if md_path:
            md = self.generate_markdown(report)
            with open(md_path, "w", encoding="utf-8") as f:
                f.write(md)
            print(f"✅ Markdown guardado: {md_path}")
