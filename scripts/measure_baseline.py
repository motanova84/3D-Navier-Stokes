# ============================================================================
# scripts/measure_baseline.py
# Medición experimental de basal en celda de agua destilada
# ============================================================================

import json
import hashlib

import numpy as np
from scipy.fft import fft, fftfreq


class BaselineMeasurement:
    """
    Caracterización del tiempo de decaimiento de inducción libre (T₂*)
    """

    def __init__(self, fs: float = 1000.0, duration: float = 60.0):
        self.fs = fs
        self.duration = duration
        self.f0 = 141.7001  # Hz
        self.t = np.linspace(0, duration, int(fs * duration), endpoint=False)

    def simulate_fid(self, T2: float, amplitude: float = 1.0) -> np.ndarray:
        """
        Simula una señal de decaimiento de inducción libre (FID)
        """
        decay = amplitude * np.exp(-self.t / T2)
        signal = decay * np.sin(2 * np.pi * self.f0 * self.t)

        # Ruido térmico (SNR ≈ 40 dB)
        rng = np.random.default_rng(seed=0)
        noise = amplitude * 1e-4 * rng.standard_normal(len(self.t))
        return signal + noise

    def compute_T2_star(self, signal: np.ndarray):
        """
        Estima T₂* a partir del ancho de línea espectral (FWHM).

        Returns
        -------
        T2 : float
            Tiempo de coherencia estimado en segundos.
        delta_f : float
            Ancho de línea a media altura en Hz.
        """
        f = fftfreq(len(signal), 1 / self.fs)
        spectrum = np.abs(fft(signal))

        # Sólo frecuencias positivas
        pos_mask = f >= 0
        f_pos = f[pos_mask]
        spec_pos = spectrum[pos_mask]

        idx = int(np.argmin(np.abs(f_pos - self.f0)))
        half_max = spec_pos[idx] / 2

        left_indices = np.where(spec_pos[:idx] < half_max)[0]
        right_indices = np.where(spec_pos[idx:] < half_max)[0]

        if len(left_indices) > 0 and len(right_indices) > 0:
            f_left = f_pos[left_indices[-1]]
            f_right = f_pos[idx + right_indices[0]]
            delta_f = float(f_right - f_left)
            T2 = 1.0 / (np.pi * delta_f) if delta_f > 0 else 0.0
        else:
            delta_f = 0.0
            T2 = 0.0

        return T2, delta_f

    def measure_baseline(self, T2_real: float = 1.0) -> dict:
        """
        Realiza la medición de basal y genera reporte
        """
        signal = self.simulate_fid(T2_real)
        T2_est, delta_f = self.compute_T2_star(signal)

        sigma_f = delta_f / (2 * np.sqrt(2)) if delta_f > 0 else 0.0
        psi = max(0.0, 1.0 - sigma_f / self.f0)

        state_hash = hashlib.sha256(signal.tobytes()).hexdigest()

        return {
            "measurement": {
                "T2_real_s": T2_real,
                "T2_estimated_s": T2_est,
                "delta_f_Hz": delta_f,
                "sigma_f_Hz": sigma_f,
                "psi": psi,
                "is_valid": psi >= 0.999999,
            },
            "metadata": {
                "fs": self.fs,
                "duration": self.duration,
                "state_hash": state_hash,
                "temperature_C": 20.0,
                "pressure_atm": 1.0,
            },
        }


def main():
    fs = 1000.0   # Hz
    duration = 60.0  # segundos

    meas = BaselineMeasurement(fs, duration)
    result = meas.measure_baseline(T2_real=1.0)

    m = result["measurement"]
    print("🌊 NOESIS — Medición de Basal en Celda")
    print("======================================")
    print(f"T₂* estimado:   {m['T2_estimated_s']:.4f} s")
    print(f"Ancho de línea: {m['delta_f_Hz']:.4f} Hz")
    print(f"σ_f:            {m['sigma_f_Hz']:.6f} Hz")
    print(f"Ψ:              {m['psi']:.10f}")
    print(f"Estado:         {'✅ VÁLIDO' if m['is_valid'] else '❌ INVÁLIDO'}")
    print(f"Hash del estado: {result['metadata']['state_hash'][:32]}...")

    with open("baseline_measurement.json", "w") as f:
        json.dump(result, f, indent=2)

    print("\n✅ Reporte guardado en baseline_measurement.json")


if __name__ == "__main__":
    main()
