# ============================================================================
# noesis_oracle/validation_oracle.py
# Oráculo de validación: coordina el pipeline sensor → ZK → chain
# ============================================================================

import json
import time
from typing import Any, Dict, Optional

import numpy as np

from noesis_oracle.sensor_normalizer import SensorNormalizer
from noesis_oracle.zk_proof_generator import ZKProofGenerator


class ValidationOracle:
    """
    Oráculo de validación NOESIS.
    Coordina: señal → normalización → witness → ZK proof → reporte.
    """

    def __init__(
        self,
        zkey_path: str = "build/noesis_coherence_final.zkey",
        wasm_path: str = "build/noesis_coherence_js/noesis_coherence.wasm",
        vkey_path: str = "build/verification_key.json",
    ):
        self.normalizer = SensorNormalizer()
        self.zk_gen = ZKProofGenerator(zkey_path, wasm_path, vkey_path)
        self.f0 = 141.7001
        self.psi_threshold = 0.999999

    # ------------------------------------------------------------------
    # Core pipeline
    # ------------------------------------------------------------------

    def validate(
        self,
        signal: np.ndarray,
        fs: float,
        run_zk: bool = False,
    ) -> Dict[str, Any]:
        """
        Valida una señal y genera el reporte completo.

        Parameters
        ----------
        signal  : señal de entrada
        fs      : frecuencia de muestreo (Hz)
        run_zk  : si True, intenta generar y verificar la prueba Groth16
        """
        # 1. Normalización y cálculo de Ψ
        norm_data = self.normalizer.normalize_sensor_data(signal, fs)

        # 2. (Opcional) Prueba ZK
        zk_result: Optional[Dict[str, Any]] = None
        if run_zk:
            zk_result = self.zk_gen.run_pipeline(norm_data["witness"])

        # 3. Estado del circuito
        circuit_status = (
            "VALID_PROOF_READY" if norm_data["is_valid"] else "REJECTED_BY_COTA"
        )

        return {
            "protocol": "NOESIS-Validation-v2.0",
            "f0": self.f0,
            "psi_threshold": self.psi_threshold,
            "sigma_f": norm_data["sigma_f"],
            "psi": norm_data["psi"],
            "is_valid": norm_data["is_valid"],
            "circuit_status": circuit_status,
            "witness": norm_data["witness"],
            "zk_result": zk_result,
            "metadata": norm_data["metadata"],
            "timestamp": time.time(),
        }

    def validate_cryogenic(self, T2: float = 1200.0, fs: float = 1000.0) -> Dict[str, Any]:
        """
        Valida una señal sintética de sistema criogénico (NV center a 4K).
        """
        duration = min(T2 / 10, 60.0)
        t = np.linspace(0, duration, int(fs * duration), endpoint=False)
        rng = np.random.default_rng(seed=0)
        signal = np.sin(2 * np.pi * self.f0 * t) + 1e-8 * rng.standard_normal(len(t))
        return self.validate(signal, fs, run_zk=False)


# ============================================================================
# Entry point
# ============================================================================

def main():
    oracle = ValidationOracle()

    # Señal sintética criogénica
    result = oracle.validate_cryogenic(T2=1200.0)

    print("🌊 NOESIS — Oráculo de Validación")
    print("==================================")
    print(f"σ_f = {result['sigma_f']:.6e} Hz")
    print(f"Ψ   = {result['psi']:.10f}")
    print(f"Estado: {result['circuit_status']}")

    with open("oracle_report.json", "w", encoding="utf-8") as f:
        json.dump(result, f, indent=2, default=str)

    print("✅ Reporte guardado en oracle_report.json")


if __name__ == "__main__":
    main()
