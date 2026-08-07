# ============================================================================
# noesis_oracle/sensor_normalizer.py
# Normalización de datos de sensores y compilación ZK
# ============================================================================

import time
import hashlib
import json

import numpy as np
from typing import Dict, Any
from scipy.signal import hilbert


class SensorNormalizer:
    """
    Normalización de datos de sensores RMN/ULF-NMR para el pipeline ZK
    """

    def __init__(self):
        self.f0 = 141.7001          # Hz
        self.psi_threshold = 0.999999
        self.sigma_max = 1.417001e-4  # Hz

    def compute_instantaneous_frequency(self, signal: np.ndarray, fs: float) -> np.ndarray:
        """
        Calcula la frecuencia instantánea usando la transformada de Hilbert
        """
        analytic = hilbert(signal)
        phase = np.unwrap(np.angle(analytic))
        freq = np.diff(phase) / (2 * np.pi) * fs
        return freq

    def compute_sigma_f(self, signal: np.ndarray, fs: float) -> float:
        """
        Calcula la desviación estándar de la frecuencia instantánea
        """
        freq = self.compute_instantaneous_frequency(signal, fs)
        sigma = float(np.std(freq - self.f0))
        return sigma

    def compute_psi(self, signal: np.ndarray, fs: float) -> float:
        """
        Calcula el parámetro Ψ a partir de la señal
        """
        sigma = self.compute_sigma_f(signal, fs)
        psi = max(0.0, 1.0 - sigma / self.f0)
        return psi

    def normalize_sensor_data(self, signal: np.ndarray, fs: float) -> Dict[str, Any]:
        """
        Normaliza los datos del sensor y prepara el witness para ZK
        """
        # 1. Calcular métricas
        sigma = self.compute_sigma_f(signal, fs)
        psi = self.compute_psi(signal, fs)

        # 2. Verificar umbral
        is_valid = psi >= self.psi_threshold

        # 3. Preparar witness para Circom
        n = min(100, len(signal))
        psi_real = signal[:n].real.tolist()
        psi_imag = [0.0] * n  # Placeholder

        # 4. Generar hash del estado
        state_hash = hashlib.sha256(
            signal.tobytes() + str(fs).encode()
        ).hexdigest()

        return {
            "sigma_f": sigma,
            "psi": psi,
            "is_valid": is_valid,
            "witness": {
                "psi_real": psi_real,
                "psi_imag": psi_imag,
                "fieldSalt": 0,
                "expectedStateHash": int(state_hash, 16),
                "minCoherence": 999999,
                "maxEntropy": 10000,
                "minStability": 100,
            },
            "metadata": {
                "fs": fs,
                "n_samples": len(signal),
                "state_hash": state_hash,
                "timestamp": time.time(),
            },
        }

    def generate_validation_report(self, signal: np.ndarray, fs: float) -> Dict[str, Any]:
        """
        Genera un reporte de validación completo
        """
        data = self.normalize_sensor_data(signal, fs)

        report = {
            "protocol": "NOESIS-Empirical-Validation-v1.0",
            "f0": self.f0,
            "psi_threshold": self.psi_threshold,
            "sigma_max": self.sigma_max,
            "measurements": {
                "sigma_f": data["sigma_f"],
                "psi": data["psi"],
                "is_valid": data["is_valid"],
            },
            "witness": data["witness"],
            "metadata": data["metadata"],
            "verdict": "VALID" if data["is_valid"] else "INVALID",
        }

        return report


# ============================================================================
# Uso del normalizador
# ============================================================================

def main():
    # Cargar datos del sensor (simulación)
    fs = 1000  # Hz
    t = np.linspace(0, 10, fs * 10)

    # Señal sintética con frecuencia cercana a f0
    rng = np.random.default_rng(seed=42)
    signal = np.sin(2 * np.pi * 141.7001 * t) + 0.01 * rng.standard_normal(len(t))

    # Normalizar
    normalizer = SensorNormalizer()
    report = normalizer.generate_validation_report(signal, fs)

    # Guardar reporte
    with open("validation_report.json", "w") as f:
        json.dump(report, f, indent=2)

    print(f"Ψ = {report['measurements']['psi']:.10f}")
    print(f"Verificación: {report['verdict']}")


if __name__ == "__main__":
    main()
