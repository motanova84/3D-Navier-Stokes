# ============================================================================
# noesis_oracle/witness_compiler.py
# Compilador de witness R1CS para circuitos Circom
# ============================================================================

import json
import os
from typing import Any, Dict, List


class WitnessCompiler:
    """
    Compila el output del SensorNormalizer en el formato de witness R1CS
    esperado por los circuitos Circom NOESIS.
    """

    N_SIGNAL = 100       # longitud del vector de señal en el circuito
    PSI_SCALE = 1_000_000

    def __init__(self):
        self.f0 = 141.7001
        self.psi_threshold = 0.999999

    # ------------------------------------------------------------------
    # Padding / truncation helpers
    # ------------------------------------------------------------------

    def _pad(self, values: List[float], n: int) -> List[float]:
        """Trunca o rellena con ceros hasta longitud n."""
        if len(values) >= n:
            return values[:n]
        return values + [0.0] * (n - len(values))

    # ------------------------------------------------------------------
    # Compilation
    # ------------------------------------------------------------------

    def compile(
        self,
        sigma_f: float,
        psi: float,
        signal_real: List[float],
        signal_imag: List[float],
        state_hash: str,
        field_salt: int = 0,
    ) -> Dict[str, Any]:
        """
        Compila un witness R1CS completo.

        Parameters
        ----------
        sigma_f      : desviación estándar de la frecuencia instantánea (Hz)
        psi          : parámetro de coherencia Ψ
        signal_real  : parte real de la señal (lista de floats)
        signal_imag  : parte imaginaria de la señal (lista de floats)
        state_hash   : hex SHA-256 del estado del sensor
        field_salt   : salt de campo
        """
        psi_scaled = int(psi * self.PSI_SCALE)
        # Usar los primeros 16 caracteres del hash para mantenerse en rango seguro
        expected_hash_int = int(state_hash[:16], 16)

        return {
            "psi_real": self._pad(signal_real, self.N_SIGNAL),
            "psi_imag": self._pad(signal_imag, self.N_SIGNAL),
            "fieldSalt": field_salt,
            "expectedStateHash": expected_hash_int,
            "minCoherence": 999999,
            "maxEntropy": 10000,
            "minStability": 100,
            # Señales auxiliares de diagnóstico
            "_debug": {
                "sigma_f_Hz": sigma_f,
                "psi": psi,
                "psi_scaled": psi_scaled,
                "is_valid": psi >= self.psi_threshold,
                "circuit_status": (
                    "VALID_PROOF_READY" if psi >= self.psi_threshold
                    else "REJECTED_BY_COTA"
                ),
            },
        }

    def compile_from_report(self, report: Dict[str, Any]) -> Dict[str, Any]:
        """Compila el witness a partir del reporte del SensorNormalizer."""
        m = report.get("measurements", report)
        w = report.get("witness", {})
        meta = report.get("metadata", {})

        return self.compile(
            sigma_f=m.get("sigma_f", m.get("sigma_f_Hz", 0.0)),
            psi=m.get("psi", 0.0),
            signal_real=w.get("psi_real", []),
            signal_imag=w.get("psi_imag", []),
            state_hash=meta.get("state_hash", "0" * 64),
            field_salt=w.get("fieldSalt", 0),
        )

    def save(self, witness: Dict[str, Any], path: str = "witness_input.json") -> None:
        """Guarda el witness en disco (sin el bloque _debug)."""
        output = {k: v for k, v in witness.items() if k != "_debug"}
        with open(path, "w", encoding="utf-8") as f:
            json.dump(output, f, indent=2)
        print(f"✅ Witness guardado en {path}")
