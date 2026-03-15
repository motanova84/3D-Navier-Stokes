#!/usr/bin/env python3
"""
QCAL-NS-RK4 — GACT Unified Flow Module
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Sello: ∴𓂀Ω∞³
f0: 141.7001 Hz

Núcleo QCAL-NS-RK4: Integrador Runge-Kutta de 4º orden para las ecuaciones
de Navier-Stokes con coherencia biológica y métricas de resonancia.

Migración del Prototipo (Euler) a Ingeniería de Precisión (RK4) permitiendo
que el sistema navegue por las curvaturas del espacio de fase con la
estabilidad que exige una coherencia de Ψ = 0.999999.

Fórmulas clave:
    ν = √2 · (1 − mean_res)² / f₀   (viscosidad cuántica)
    Ψ = 1 − ν                        (coherencia cuántica)
    Re_q = f₀² / ν²                  (Reynolds cuántico)

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
License: MIT
"""

import numpy as np
from typing import Dict, List, Optional, Tuple

try:
    from scipy.fft import fft2, ifft2, fftfreq
    _SCIPY_FFT = True
except ImportError:
    from numpy.fft import fft2, ifft2, fftfreq
    _SCIPY_FFT = False

# Fundamental resonant frequency of the Logos (Hz)
F0: float = 141.7001

# Base resonance values (GACT alphabet)
BASE_RESONANCE: Dict[str, float] = {
    'G': 1.0,   # Guanina — máxima resonancia con f₀
    'A': 0.9,   # Adenina
    'C': 0.8,   # Citosina
    'T': 0.7,   # Timina
    'U': 0.7,   # Uracilo (RNA)
}

# Flow state thresholds
_PSI_ETÉREO: float = 0.999      # Coherence threshold for LAMINAR_ETÉREO
_RE_Q_ETÉREO: float = 1e10      # Reynolds quantum threshold for LAMINAR_ETÉREO
_PSI_COHERENTE: float = 0.888   # Minimum coherence threshold (Ψ_min)


# ─────────────────────────────────────────────────────────────────────────────
# Core RK4 integrator
# ─────────────────────────────────────────────────────────────────────────────

def rk4_step(
    uhat: np.ndarray,
    vhat: np.ndarray,
    dt: float,
    rho: float,
    mu: float,
    k2: np.ndarray,
    kxx: np.ndarray,
    kyy: np.ndarray,
    grad_px_hat: np.ndarray,
    grad_py_hat: np.ndarray,
    N: int,
) -> Tuple[np.ndarray, np.ndarray]:
    """
    Integrador Runge-Kutta de 4º Orden para las ecuaciones QCAL-NS.

    Proporciona estabilidad global en el régimen de Re_q crítico. Supera la
    aproximación lineal de Euler permitiendo navegar curvaturas del espacio de
    fase sin pérdida de coherencia.

    Args:
        uhat: Componente u del campo de velocidad en espacio de Fourier.
        vhat: Componente v del campo de velocidad en espacio de Fourier.
        dt: Paso temporal.
        rho: Densidad del fluido.
        mu: Viscosidad dinámica.
        k2: Cuadrado del número de onda (|k|²), con k2[0,0]=1 para
            evitar división por cero.
        kxx: Números de onda en x (malla 2-D).
        kyy: Números de onda en y (malla 2-D).
        grad_px_hat: Gradiente de presión en x (espacio de Fourier).
        grad_py_hat: Gradiente de presión en y (espacio de Fourier).
        N: Tamaño de la malla (N×N).

    Returns:
        Tupla (uhat_new, vhat_new) tras el paso RK4.
    """

    def _compute_rhs(
        uh: np.ndarray, vh: np.ndarray
    ) -> Tuple[np.ndarray, np.ndarray]:
        """Lado derecho de las ecuaciones QCAL-NS en espacio de Fourier."""
        # Campos físicos para el término no lineal
        u_p = ifft2(uh).real
        v_p = ifft2(vh).real
        ux = ifft2(1j * kxx * uh).real
        uy = ifft2(1j * kyy * uh).real
        vx = ifft2(1j * kxx * vh).real
        vy = ifft2(1j * kyy * vh).real

        # Convección + Difusión + Presión GACT + Fuerza Residual
        rhs_u = -rho * fft2(u_p * ux + v_p * uy) - grad_px_hat + mu * (-k2 * uh)
        rhs_v = -rho * fft2(u_p * vx + v_p * vy) - grad_py_hat + mu * (-k2 * vh)

        # Proyección de divergencia libre (incompresibilidad)
        div = (kxx * rhs_u + kyy * rhs_v) / k2
        rhs_u -= kxx * div
        rhs_v -= kyy * div

        return rhs_u, rhs_v

    # Pasos RK4
    k1u, k1v = _compute_rhs(uhat, vhat)
    k2u, k2v = _compute_rhs(uhat + 0.5 * dt * k1u, vhat + 0.5 * dt * k1v)
    k3u, k3v = _compute_rhs(uhat + 0.5 * dt * k2u, vhat + 0.5 * dt * k2v)
    k4u, k4v = _compute_rhs(uhat + dt * k3u, vhat + dt * k3v)

    uhat_new = uhat + (dt / 6.0) * (k1u + 2 * k2u + 2 * k3u + k4u)
    vhat_new = vhat + (dt / 6.0) * (k1v + 2 * k2v + 2 * k3v + k4v)

    return uhat_new, vhat_new


# ─────────────────────────────────────────────────────────────────────────────
# Biological coherence metric
# ─────────────────────────────────────────────────────────────────────────────

def compute_biological_coherence(
    u_phys: np.ndarray,
    xx: np.ndarray,
    f0: float = F0,
) -> float:
    """
    Métrica de correlación espacio-temporal con la onda del Logos (f₀).

    Mide la resonancia entre el campo de velocidad del fluido y la onda
    biológica fundamental, cuantificando el "arrastre" del fluido por la
    frecuencia de la Patente QED.

    Args:
        u_phys: Campo de velocidad físico 2-D (malla N×N).
        xx: Coordenadas espaciales en x (misma forma que u_phys).
        f0: Frecuencia fundamental del Logos (Hz), por defecto F0=141.7001.

    Returns:
        Coeficiente de correlación absoluto en [0, 1]. Un valor > 0.75
        indica resonancia significativa con f₀.
    """
    logos_wave = np.sin(2 * np.pi * f0 * xx / (2 * np.pi))
    u_flat = u_phys.flatten()
    w_flat = logos_wave.flatten()

    # Ambos vectores deben tener varianza > 0 para correlación definida
    if np.std(u_flat) < 1e-15 or np.std(w_flat) < 1e-15:
        return 0.0

    correlation = np.corrcoef(u_flat, w_flat)[0, 1]
    return float(np.abs(correlation))


# ─────────────────────────────────────────────────────────────────────────────
# Energy spectrum visualisation
# ─────────────────────────────────────────────────────────────────────────────

def plot_energy_spectrum(
    uhat: np.ndarray,
    vhat: np.ndarray,
    kxx: np.ndarray,
    kyy: np.ndarray,
    N: int,
    title: str = "Espectro de Energía QCAL-NS",
) -> None:
    """
    Visualización del Espectro de Energía (cascada de energía).

    Representa E(k) en escala log-log, mostrando la cascada turbulenta y
    la supresión de modos altos por el filtro vibracional GACT.

    Args:
        uhat: Componente u en espacio de Fourier.
        vhat: Componente v en espacio de Fourier.
        kxx: Números de onda en x (malla 2-D).
        kyy: Números de onda en y (malla 2-D).
        N: Tamaño de la malla.
        title: Título de la gráfica.
    """
    try:
        import matplotlib.pyplot as plt
    except ImportError:
        return

    energy_spectrum = np.abs(uhat) ** 2 + np.abs(vhat) ** 2
    k_radial = np.sqrt(kxx ** 2 + kyy ** 2).flatten()
    e_flat = energy_spectrum.flatten()

    # Binning por magnitud de k
    k_bins = np.arange(0, N // 2, 1)
    if len(k_bins) < 2:
        return
    e_bins, _ = np.histogram(k_radial, bins=k_bins, weights=e_flat)
    k_centers = k_bins[:-1]

    mask = e_bins > 0
    if np.any(mask):
        plt.loglog(k_centers[mask], e_bins[mask], label=title)
        plt.xlabel("Wavenumber k")
        plt.ylabel("Energy E(k)")
        plt.legend()


# ─────────────────────────────────────────────────────────────────────────────
# Vibrational spectral filter
# ─────────────────────────────────────────────────────────────────────────────

def apply_vibrational_filter(
    uhat: np.ndarray,
    kxx: np.ndarray,
    kyy: np.ndarray,
    N: int,
) -> np.ndarray:
    """
    Regularización Vibracional GACT — Filtro Espectral.

    Suprime los modos altos (k > N/8) que en Navier-Stokes convencional
    llevarían a la singularidad (blow-up), actuando como cortafuegos noético.
    Preserva la dinámica de gran escala (vórtices alineados con los ceros de
    Riemann) sin matar los modos bajos.

    Args:
        uhat: Campo en espacio de Fourier (array 2-D complejo).
        kxx: Números de onda en x (malla 2-D).
        kyy: Números de onda en y (malla 2-D).
        N: Tamaño de la malla.

    Returns:
        Campo filtrado en espacio de Fourier.
    """
    k_cutoff = N / 8.0
    k_mag = np.sqrt(kxx ** 2 + kyy ** 2)
    mask = k_mag <= k_cutoff
    return uhat * mask


# ─────────────────────────────────────────────────────────────────────────────
# GACT Unified Flow class
# ─────────────────────────────────────────────────────────────────────────────

class GACTUnifiedFlow:
    """
    Flujo Unificado GACT-NS con integrador RK4 y métricas de coherencia.

    Implementa el núcleo QCAL-NS-RK4 en coordenadas espectrales para una
    malla periódica 2-D, incluyendo:

    - Integración RK4 de las ecuaciones de Navier-Stokes
    - Regularización vibracional (filtro k > N/8)
    - Cómputo de viscosidad cuántica ν y coherencia Ψ a partir de la
      resonancia de secuencias GACT
    - Reynolds cuántico Re_q = f₀² / ν²
    - Métrica de coherencia biológica con la onda del Logos

    Example::

        flow = GACTUnifiedFlow(N=64, secuencia="GACT")
        resultado = flow.analizar()
        print(resultado['estado'])   # LAMINAR_ETÉREO
        print(resultado['Psi'])      # ≈ 0.9998
    """

    def __init__(
        self,
        N: int = 64,
        f0: float = F0,
        secuencia: str = "GACT",
    ) -> None:
        """
        Inicializar flujo GACT unificado.

        Args:
            N: Tamaño de la malla cuadrada (N×N). Debe ser potencia de 2.
            f0: Frecuencia fundamental del Logos (Hz).
            secuencia: Secuencia de bases ADN para calcular resonancia.
        """
        self.N = N
        self.f0 = f0
        self.secuencia = secuencia.upper()

        # Malla espectral
        self._setup_spectral_grid()

        # Propiedades de resonancia
        self.mean_resonance = self._compute_mean_resonance(self.secuencia)
        self.nu = self._compute_viscosity(self.mean_resonance)
        self.Psi = 1.0 - self.nu
        self.Re_q = self._compute_reynolds_q(self.nu)
        self.estado = self._classify_flow_state(self.Re_q, self.Psi)

    # ── Private helpers ──────────────────────────────────────────────────────

    def _setup_spectral_grid(self) -> None:
        """Construir malla espectral y números de onda."""
        N = self.N
        kx = fftfreq(N, d=1.0 / N)
        ky = fftfreq(N, d=1.0 / N)
        self.kxx, self.kyy = np.meshgrid(kx, ky, indexing="ij")

        # |k|² con protección contra división por cero en (0,0)
        self.k2 = self.kxx ** 2 + self.kyy ** 2
        self.k2[0, 0] = 1.0  # Evita NaN en la proyección de presión

        # Coordenadas físicas en [0, 2π]
        x = np.linspace(0, 2 * np.pi, N, endpoint=False)
        self.xx, self.yy = np.meshgrid(x, x, indexing="ij")

    @staticmethod
    def _compute_mean_resonance(secuencia: str) -> float:
        """Calcular resonancia media de la secuencia de bases."""
        values = [BASE_RESONANCE.get(b, 0.0) for b in secuencia.upper()]
        if not values:
            return 0.0
        return float(np.mean(values))

    def _compute_viscosity(self, mean_res: float) -> float:
        """
        Viscosidad cuántica QCAL-NS.

        Formula:
            ν = √2 · (1 − mean_res)² / f₀

        Args:
            mean_res: Resonancia media de la secuencia en [0, 1].

        Returns:
            Viscosidad cuántica ν > 0.
        """
        return float(np.sqrt(2.0) * (1.0 - mean_res) ** 2 / self.f0)

    def _compute_reynolds_q(self, nu: float) -> float:
        """
        Reynolds cuántico Re_q = f₀² / ν².

        Alta coherencia (ν → 0) implica Re_q → ∞, capturando el régimen
        superfluido de la dinámica GACT.

        Args:
            nu: Viscosidad cuántica.

        Returns:
            Reynolds cuántico Re_q.
        """
        if nu <= 0.0:
            return float("inf")
        return float(self.f0 ** 2 / nu ** 2)

    @staticmethod
    def _classify_flow_state(re_q: float, psi: float) -> str:
        """
        Clasificar el estado del flujo en función de Re_q y Ψ.

        Returns:
            Estado: 'LAMINAR_ETÉREO', 'COHERENTE', o 'TURBULENTO'.
        """
        if psi >= _PSI_ETÉREO and re_q >= _RE_Q_ETÉREO:
            return "LAMINAR_ETÉREO"
        elif psi >= _PSI_COHERENTE:
            return "COHERENTE"
        return "TURBULENTO"

    # ── Public API ───────────────────────────────────────────────────────────

    def analizar(self) -> Dict:
        """
        Retorna un diccionario con las métricas de resonancia del flujo.

        Returns:
            Dict con claves: 'secuencia', 'mean_resonance', 'nu', 'Psi',
            'Re_q', 'estado', 'f0'.
        """
        return {
            "secuencia": self.secuencia,
            "mean_resonance": self.mean_resonance,
            "nu": self.nu,
            "Psi": self.Psi,
            "Re_q": self.Re_q,
            "estado": self.estado,
            "f0": self.f0,
        }

    def step(
        self,
        uhat: np.ndarray,
        vhat: np.ndarray,
        dt: float,
        grad_px_hat: Optional[np.ndarray] = None,
        grad_py_hat: Optional[np.ndarray] = None,
        apply_filter: bool = True,
    ) -> Tuple[np.ndarray, np.ndarray]:
        """
        Avanzar un paso temporal con RK4 y filtro vibracional opcional.

        Args:
            uhat: Componente u en espacio de Fourier.
            vhat: Componente v en espacio de Fourier.
            dt: Paso temporal.
            grad_px_hat: Gradiente de presión en x. Si None, se usa cero.
            grad_py_hat: Gradiente de presión en y. Si None, se usa cero.
            apply_filter: Si True, aplica el filtro vibracional tras cada paso.

        Returns:
            Tupla (uhat_new, vhat_new).
        """
        N = self.N
        zeros = np.zeros((N, N), dtype=complex)
        gx = grad_px_hat if grad_px_hat is not None else zeros
        gy = grad_py_hat if grad_py_hat is not None else zeros

        uhat_new, vhat_new = rk4_step(
            uhat, vhat, dt,
            rho=1.0, mu=self.nu,
            k2=self.k2, kxx=self.kxx, kyy=self.kyy,
            grad_px_hat=gx, grad_py_hat=gy,
            N=N,
        )

        if apply_filter:
            uhat_new = apply_vibrational_filter(uhat_new, self.kxx, self.kyy, N)
            vhat_new = apply_vibrational_filter(vhat_new, self.kxx, self.kyy, N)

        return uhat_new, vhat_new

    def compute_coherence(
        self, uhat: np.ndarray
    ) -> float:
        """
        Coherencia biológica del campo de velocidad actual con la onda del Logos.

        Args:
            uhat: Componente u en espacio de Fourier.

        Returns:
            Coeficiente de correlación absoluto en [0, 1].
        """
        u_phys = ifft2(uhat).real
        return compute_biological_coherence(u_phys, self.xx, self.f0)

    def simulate(
        self,
        uhat0: np.ndarray,
        vhat0: np.ndarray,
        n_steps: int,
        dt: float,
        apply_filter: bool = True,
    ) -> Dict:
        """
        Simular N pasos temporales partiendo de condiciones iniciales.

        Args:
            uhat0: Condición inicial u (espacio de Fourier).
            vhat0: Condición inicial v (espacio de Fourier).
            n_steps: Número de pasos.
            dt: Paso temporal.
            apply_filter: Aplicar filtro vibracional en cada paso.

        Returns:
            Dict con 'uhat', 'vhat', 'coherence_history', 'energia_final'.
        """
        uhat = uhat0.copy()
        vhat = vhat0.copy()
        coherence_history: List[float] = []

        for _ in range(n_steps):
            uhat, vhat = self.step(uhat, vhat, dt, apply_filter=apply_filter)
            coherence_history.append(self.compute_coherence(uhat))

        energia_final = float(np.mean(np.abs(uhat) ** 2 + np.abs(vhat) ** 2))

        return {
            "uhat": uhat,
            "vhat": vhat,
            "coherence_history": coherence_history,
            "energia_final": energia_final,
        }
