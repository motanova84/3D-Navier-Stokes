# ============================================================================
# noesis_oracle/hardware_witness_bridge.py
# Pipeline transductor Hardware-to-Witness
# ============================================================================

import hashlib
import json
import os
import struct
import time
from typing import Any, Dict, Optional

import numpy as np
from scipy.signal import hilbert


class HardwareWitnessBridge:
    """
    Bridge entre hardware de adquisición y generación de witness ZK
    """

    def __init__(self, config_path: str = "config/hardware_config.json"):
        with open(config_path, "r") as f:
            self.config = json.load(f)

        self.f0 = 141.7001          # Hz
        self.psi_threshold = 0.999999
        self.sigma_max = 1.417001e-4  # Hz

        self._serial_conn: Optional[Any] = None
        self.is_connected = False

    # ------------------------------------------------------------------
    # Hardware connection
    # ------------------------------------------------------------------

    def connect_hardware(self, port: str, baudrate: int = 115200) -> bool:
        """
        Conecta al hardware de adquisición vía puerto serial
        """
        try:
            import serial  # type: ignore

            self._serial_conn = serial.Serial(port, baudrate, timeout=1)
            self.is_connected = True
            print(f"✅ Conectado a hardware en {port}")
            return True
        except Exception as exc:
            print(f"❌ Error de conexión: {exc}")
            return False

    def read_signal(self, duration: float, fs: float) -> np.ndarray:
        """
        Lee la señal del hardware por puerto serial (4 bytes por muestra, float32)
        """
        if not self.is_connected or self._serial_conn is None:
            raise RuntimeError("No hay conexión con el hardware")

        n_samples = int(duration * fs)
        signal = np.zeros(n_samples, dtype=np.float64)

        for i in range(n_samples):
            raw = self._serial_conn.read(4)
            if len(raw) == 4:
                signal[i] = struct.unpack("f", raw)[0]

        return signal

    # ------------------------------------------------------------------
    # Signal processing
    # ------------------------------------------------------------------

    def compute_instantaneous_frequency(
        self, signal: np.ndarray, fs: float
    ) -> np.ndarray:
        """Frecuencia instantánea vía transformada de Hilbert"""
        analytic = hilbert(signal)
        phase = np.unwrap(np.angle(analytic))
        return np.diff(phase) / (2 * np.pi) * fs

    def compute_sigma_f(self, signal: np.ndarray, fs: float) -> float:
        """Desviación estándar de la frecuencia instantánea"""
        freq = self.compute_instantaneous_frequency(signal, fs)
        return float(np.std(freq - self.f0))

    def compute_psi(self, signal: np.ndarray, fs: float) -> float:
        """Parámetro de coherencia Ψ"""
        sigma = self.compute_sigma_f(signal, fs)
        return max(0.0, 1.0 - sigma / self.f0)

    # ------------------------------------------------------------------
    # Witness generation
    # ------------------------------------------------------------------

    def generate_witness(self, signal: np.ndarray, fs: float) -> Dict[str, Any]:
        """
        Genera el witness R1CS (JSON) a partir de la señal capturada
        """
        sigma = self.compute_sigma_f(signal, fs)
        psi = self.compute_psi(signal, fs)
        is_valid = psi >= self.psi_threshold

        n = min(100, len(signal))
        psi_real = signal[:n].real.tolist()
        psi_imag = [0.0] * n

        state_hash = hashlib.sha256(
            signal.tobytes() + str(fs).encode()
        ).hexdigest()
        # Use only first 16 hex chars to stay within JS safe integer range
        expected_state_hash = int(state_hash[:16], 16)

        witness = {
            "psi_real": psi_real,
            "psi_imag": psi_imag,
            "fieldSalt": 0,
            "expectedStateHash": expected_state_hash,
            "minCoherence": 999999,
            "maxEntropy": 10000,
            "minStability": 100,
        }

        return {
            "witness": witness,
            "metrics": {
                "sigma_f": sigma,
                "psi": psi,
                "is_valid": is_valid,
            },
            "metadata": {
                "fs": fs,
                "n_samples": len(signal),
                "state_hash": state_hash,
                "timestamp": time.time(),
            },
        }

    # ------------------------------------------------------------------
    # High-level pipeline
    # ------------------------------------------------------------------

    def process_hardware_data(
        self, duration: float = 10.0, fs: float = 1000.0
    ) -> Dict[str, Any]:
        """
        Procesa los datos del hardware y genera el witness
        """
        signal = self.read_signal(duration, fs)
        result = self.generate_witness(signal, fs)

        if result["metrics"]["is_valid"]:
            print("✅ Witness válido generado")
        else:
            print("❌ Witness inválido — Ψ por debajo del umbral")

        return result


# ============================================================================
# Uso del bridge
# ============================================================================

def main():
    config_dir = "config"
    os.makedirs(config_dir, exist_ok=True)

    config = {
        "hardware": {
            "port": "/dev/ttyUSB0",
            "baudrate": 115200,
            "sensor_type": "ULF_NMR",
        },
        "measurement": {
            "fs": 1000.0,
            "duration": 10.0,
            "f0": 141.7001,
        },
    }

    config_path = os.path.join(config_dir, "hardware_config.json")
    with open(config_path, "w") as f:
        json.dump(config, f, indent=2)

    bridge = HardwareWitnessBridge(config_path)

    connected = bridge.connect_hardware("/dev/ttyUSB0")
    if not connected:
        print("⚠️  Modo simulación: hardware no disponible")
        return

    result = bridge.process_hardware_data(duration=10.0, fs=1000.0)

    with open("witness_input.json", "w") as f:
        json.dump(result["witness"], f, indent=2)

    print("✅ Witness guardado en witness_input.json")
    return result


if __name__ == "__main__":
    main()
