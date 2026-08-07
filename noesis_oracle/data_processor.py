# ============================================================================
# noesis_oracle/data_processor.py
# Procesamiento de señales para el pipeline NOESIS
# ============================================================================

from typing import Dict, Tuple

import numpy as np
from scipy.signal import butter, filtfilt, hilbert
from scipy.fft import fft, fftfreq


class DataProcessor:
    """
    Procesamiento de señales ULF-NMR: filtrado, extracción de fase,
    estimación de frecuencia instantánea y cálculo de σ_f.
    """

    def __init__(self, f0: float = 141.7001, fs: float = 1000.0):
        self.f0 = f0
        self.fs = fs
        # Ancho de banda del filtro paso-banda (± bw Hz en torno a f0)
        self.bw = 10.0  # Hz

    # ------------------------------------------------------------------
    # Filtering
    # ------------------------------------------------------------------

    def bandpass_filter(
        self, signal: np.ndarray, order: int = 4
    ) -> np.ndarray:
        """Filtro paso-banda Butterworth centrado en f0 ± bw Hz."""
        nyq = self.fs / 2.0
        low = max(1e-3, (self.f0 - self.bw) / nyq)
        high = min(1 - 1e-6, (self.f0 + self.bw) / nyq)
        b, a = butter(order, [low, high], btype="band")
        return filtfilt(b, a, signal)

    # ------------------------------------------------------------------
    # Instantaneous frequency
    # ------------------------------------------------------------------

    def instantaneous_frequency(self, signal: np.ndarray) -> np.ndarray:
        """Frecuencia instantánea vía transformada de Hilbert (Hz)."""
        analytic = hilbert(signal)
        phase = np.unwrap(np.angle(analytic))
        return np.diff(phase) / (2 * np.pi) * self.fs

    def sigma_f(self, signal: np.ndarray) -> float:
        """Desviación estándar de la frecuencia instantánea respecto a f0."""
        freq = self.instantaneous_frequency(signal)
        return float(np.std(freq - self.f0))

    # ------------------------------------------------------------------
    # Spectral analysis
    # ------------------------------------------------------------------

    def psd(self, signal: np.ndarray) -> Tuple[np.ndarray, np.ndarray]:
        """Densidad espectral de potencia (frecuencias positivas, Hz vs V²/Hz)."""
        n = len(signal)
        freqs = fftfreq(n, 1.0 / self.fs)
        spectrum = np.abs(fft(signal)) ** 2 / (n * self.fs)
        pos = freqs >= 0
        return freqs[pos], spectrum[pos]

    def snr_at_f0(self, signal: np.ndarray, window_hz: float = 1.0) -> float:
        """Relación señal/ruido en ± window_hz alrededor de f0."""
        freqs, power = self.psd(signal)
        in_band = np.abs(freqs - self.f0) <= window_hz
        out_band = ~in_band & (freqs > 0)
        signal_power = float(np.mean(power[in_band])) if in_band.any() else 0.0
        noise_power = float(np.mean(power[out_band])) if out_band.any() else 1.0
        return signal_power / noise_power if noise_power > 0 else float("inf")

    # ------------------------------------------------------------------
    # Full processing pipeline
    # ------------------------------------------------------------------

    def process(self, raw_signal: np.ndarray) -> Dict:
        """
        Pipeline completo: filtrado → frecuencia instantánea → σ_f → Ψ.
        """
        filtered = self.bandpass_filter(raw_signal)
        sigma = self.sigma_f(filtered)
        psi = max(0.0, 1.0 - sigma / self.f0)
        snr = self.snr_at_f0(filtered)

        return {
            "sigma_f_Hz": sigma,
            "psi": psi,
            "is_valid": psi >= 0.999999,
            "snr_dB": 10 * np.log10(snr) if snr > 0 else -np.inf,
            "n_samples": len(raw_signal),
            "fs": self.fs,
        }
