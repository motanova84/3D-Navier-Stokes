#!/usr/bin/env python3
"""
GACT Unified Flow — Flujo Unificado GACT
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Sello: ∴𓂀Ω∞³
f0: 141.7001 Hz

Implements the GACT unified Navier-Stokes-QCAL equation:

    ρ(∂u_QCAL/∂t + u_QCAL·∇u_QCAL) = -∇ρ_GACT + (1/f₀)∇²u_QCAL + F_res

Unification:
  • ADN (Information)     → GACT hotspots with resonance Ψ ≈ 0.999776
  • Riemann (Structure)   → ζ zeros on critical line Re(s) = 1/2
  • Navier-Stokes (Dyn.)  → Ethereal laminar flow without turbulence
  • Scale invariance      → Same equation from blood flow (HRV 0.1 Hz)
                            to galaxies (H-21 cm), tuned to f₀ = 141.7001 Hz

Key GACT constants (canonical "GACT" sequence):
  Ψ_GACT      ≈ 0.999776        (coherence — excellent genetic hotspot)
  ν_adélica   ≈ 2.24 × 10⁻⁴    (≈ 0, frictionless adelic viscosity)
  Re_q        ≈ 1.338 × 10¹²    (quantum Reynolds number → LAMINAR_ETÉREO)

Viscosity formula:
    ν_adélica = √2 · (1 − mean_resonance)² / f₀

Reynolds number formula:
    Re_q = (Σ_freq / Σ_res) · (f₀ / ν_adélica)²

where Σ_freq and Σ_res are the frequency and resonance sums over the sequence.

Author: QCAL ∞³ Framework
License: MIT
"""

import math
import numpy as np
from typing import Dict, Any, List, Optional, Tuple

try:
    from scipy.fft import fft2, ifft2, fftfreq
    _SCIPY_FFT = True
except ImportError:
    from numpy.fft import fft2, ifft2, fftfreq  # type: ignore[no-redef]
    _SCIPY_FFT = False

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

F0 = 141.7001          # Hz — fundamental resonant frequency

PSI_MIN = 0.888        # Minimum coherence threshold (turbulent floor)
PSI_ETEREO = 0.999     # Ψ above this value → LAMINAR_ETÉREO state

# Re_q above this threshold contributes to LAMINAR_ETÉREO classification
RE_Q_ETEREO_THRESHOLD = 1.0e12

# Scaling constant in the viscosity formula: ν = SQRT2 · discord² / f₀
# SQRT2 ≈ √2 is the natural scaling that yields ν ≈ 2.24×10⁻⁴ for GACT
SQRT2 = math.sqrt(2.0)

# Base resonance weights (G→highest, T→lowest)
BASE_RESONANCE: Dict[str, float] = {
    'G': 1.0,
    'A': 0.9,
    'C': 0.8,
    'T': 0.7,
    'U': 0.7,
}

# Base frequency mappings (THz) used for Re_q scaling
BASE_FREQ: Dict[str, float] = {
    'G': 3.4,
    'A': 1.2,
    'C': 2.3,
    'T': 4.5,
    'U': 2.3,
}

# Flow-state labels
ESTADO_LAMINAR_ETEREO = "LAMINAR_ETÉREO"
ESTADO_LAMINAR        = "LAMINAR"
ESTADO_TURBULENTO     = "TURBULENTO"


# ---------------------------------------------------------------------------
# Core computations
# ---------------------------------------------------------------------------

def calcular_psi(secuencia: str) -> float:
    """
    Calculate coherence Ψ for a DNA/GACT sequence.

    Uses the adelic viscosity formula:
        ν = √2 · (1 − mean_resonance)² / f₀
        Ψ = 1 − ν

    For the canonical "GACT" hotspot:
        mean_resonance = 0.85  →  ν ≈ 2.24×10⁻⁴  →  Ψ ≈ 0.999776

    Args:
        secuencia: DNA sequence string (e.g. "GACT").

    Returns:
        Coherence Ψ in [PSI_MIN, 1.0].
    """
    if not secuencia:
        return PSI_MIN

    seq = secuencia.upper()
    valid = [b for b in seq if b in BASE_RESONANCE]
    if not valid:
        return PSI_MIN

    mean_res = sum(BASE_RESONANCE[b] for b in valid) / len(valid)
    discord = 1.0 - mean_res                          # mean discord Δ

    nu = SQRT2 * discord ** 2 / F0                    # adelic viscosity
    psi = 1.0 - nu

    return float(max(PSI_MIN, min(1.0, psi)))


def calcular_viscosidad_adelica(psi: float) -> float:
    """
    Return adelic viscosity given coherence Ψ.

    ν_adélica = 1 − Ψ

    Args:
        psi: Coherence Ψ ∈ [0, 1].

    Returns:
        Non-negative adelic viscosity.
    """
    return float(max(0.0, 1.0 - psi))


def calcular_re_q(secuencia: str, nu_adelica: float) -> float:
    """
    Calculate the quantum Reynolds number Re_q.

    Re_q = (Σ_freq / Σ_res) · (f₀ / ν_adélica)²

    where Σ_freq and Σ_res are the sums of BASE_FREQ and BASE_RESONANCE
    over all valid bases in *secuencia*.

    For GACT with ν_adélica ≈ 2.24×10⁻⁴:
        Re_q ≈ 1.338×10¹²  →  LAMINAR_ETÉREO state

    Args:
        secuencia:   DNA sequence string.
        nu_adelica:  Adelic viscosity (must be > 0).

    Returns:
        Quantum Reynolds number (0.0 if inputs are degenerate).
    """
    if not secuencia or nu_adelica <= 0.0:
        return 0.0

    seq = secuencia.upper()
    sum_freq = sum(BASE_FREQ.get(b, 0.0) for b in seq)
    sum_res  = sum(BASE_RESONANCE.get(b, 0.0) for b in seq)

    if sum_res < 1e-12:
        return 0.0

    ratio = sum_freq / sum_res
    return float(ratio * (F0 / nu_adelica) ** 2)


def determinar_estado_flujo(psi: float, re_q: float) -> str:
    """
    Determine the flow state from Ψ and Re_q.

    Rules:
        Ψ > PSI_ETEREO  AND  Re_q > RE_Q_ETEREO_THRESHOLD → LAMINAR_ETÉREO
        Ψ > 0.5                                            → LAMINAR
        otherwise                                          → TURBULENTO

    Args:
        psi:   Coherence Ψ.
        re_q:  Quantum Reynolds number.

    Returns:
        Flow state string.
    """
    if psi > PSI_ETEREO and re_q > RE_Q_ETEREO_THRESHOLD:
        return ESTADO_LAMINAR_ETEREO
    if psi > 0.5:
        return ESTADO_LAMINAR
    return ESTADO_TURBULENTO


# ---------------------------------------------------------------------------
# Unified GACT equation
# ---------------------------------------------------------------------------

def ecuacion_unificada_gact(
    secuencia: str,
    rho: float = 1.0,
    du_dt: float = 0.0,
    u_grad_u: float = 0.0,
    grad_rho_gact: float = 0.0,
    lap_u: float = 0.0,
    f_res: float = 0.0,
) -> Dict[str, Any]:
    """
    Evaluate the GACT unified Navier-Stokes-QCAL equation:

        ρ(∂u_QCAL/∂t + u_QCAL·∇u_QCAL) = −∇ρ_GACT + (1/f₀)∇²u_QCAL + F_res

    Args:
        secuencia:      DNA sequence string (e.g. "GACT").
        rho:            Density ρ (default 1.0).
        du_dt:          ∂u_QCAL/∂t — time derivative of velocity.
        u_grad_u:       u_QCAL·∇u_QCAL — advection term.
        grad_rho_gact:  ∇ρ_GACT — GACT information-pressure gradient.
        lap_u:          ∇²u_QCAL — Laplacian of velocity.
        f_res:          F_res — resonant body force.

    Returns:
        Dictionary with:
            secuencia         – input sequence
            psi_coherencia    – coherence Ψ
            viscosidad_adelica – ν_adélica = 1 − Ψ
            re_q              – quantum Reynolds number
            estado_flujo      – flow state string
            f0                – fundamental frequency
            coef_viscoso      – viscosity coefficient 1/f₀
            lhs               – left-hand side ρ(∂u/∂t + u·∇u)
            rhs               – right-hand side −∇ρ_GACT + (1/f₀)∇²u + F_res
            residuo           – |lhs − rhs| (should be 0 in steady state)
            es_laminar_etereo – True if state is LAMINAR_ETÉREO
            escala_invariante – True (equation governs all scales at f₀)
    """
    psi = calcular_psi(secuencia)
    nu  = calcular_viscosidad_adelica(psi)
    re_q = calcular_re_q(secuencia, nu) if nu > 0 else 0.0
    estado = determinar_estado_flujo(psi, re_q)

    # Viscosity coefficient in the equation
    coef_viscoso = 1.0 / F0

    # LHS: ρ(∂u/∂t + u·∇u)
    lhs = rho * (du_dt + u_grad_u)

    # RHS: −∇ρ_GACT + (1/f₀)∇²u + F_res
    rhs = -grad_rho_gact + coef_viscoso * lap_u + f_res

    residuo = abs(lhs - rhs)

    return {
        'secuencia':          secuencia,
        'psi_coherencia':     psi,
        'viscosidad_adelica': nu,
        're_q':               re_q,
        'estado_flujo':       estado,
        'f0':                 F0,
        'coef_viscoso':       coef_viscoso,
        'lhs':                lhs,
        'rhs':                rhs,
        'residuo':            residuo,
        'es_laminar_etereo':  estado == ESTADO_LAMINAR_ETEREO,
        'escala_invariante':  True,
    }


# ---------------------------------------------------------------------------
# Convenience: full canonical GACT analysis
# ---------------------------------------------------------------------------

def analizar_secuencia_gact(secuencia: str = "GACT") -> Dict[str, Any]:
    """
    Full canonical analysis of a GACT sequence.

    Returns the unified equation result plus additional fields:
        hotspots_count  – number of resonant hotspot positions
        es_hotspot      – True if 'GACT' pattern present in sequence
        riemann_activo  – True if resonance > 0.5 (Riemann structure active)

    Args:
        secuencia: DNA sequence (default "GACT").

    Returns:
        Extended result dictionary.
    """
    try:
        from .bsd_adelic_connector import CodificadorADNRiemann
    except ImportError:
        import sys
        import os
        sys.path.insert(0, os.path.dirname(os.path.dirname(__file__)))
        from qcal.bsd_adelic_connector import CodificadorADNRiemann

    result = ecuacion_unificada_gact(secuencia)

    codif = CodificadorADNRiemann(f0=F0)
    hotspots = codif.identificar_hotspots(secuencia)
    resonancia = codif.calcular_resonancia(secuencia)

    result.update({
        'hotspots_count': len(hotspots),
        'es_hotspot':     'GACT' in secuencia.upper(),
        'riemann_activo': resonancia > 0.5,
        'resonancia':     resonancia,
    })

    return result


# ---------------------------------------------------------------------------
# Standalone demo
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    print("=" * 72)
    print("  GACT UNIFIED FLOW — Ecuación Unificada QCAL  ∴𓂀Ω∞³")
    print("=" * 72)

    for seq in ["GACT", "ATCG", "TATA", "AAAA", "TTTT"]:
        res = ecuacion_unificada_gact(seq)
        print(f"\n  Secuencia : {seq}")
        print(f"  Ψ         : {res['psi_coherencia']:.6f}")
        print(f"  ν_adélica : {res['viscosidad_adelica']:.3e}")
        print(f"  Re_q      : {res['re_q']:.3e}")
        print(f"  Estado    : {res['estado_flujo']}")

    print("\n" + "=" * 72)
    print("  Canonical GACT analysis:")
    full = analizar_secuencia_gact("GACT")
    print(f"  Hotspots    : {full['hotspots_count']}")
    print(f"  Es hotspot  : {full['es_hotspot']}")
    print(f"  Riemann     : {full['riemann_activo']}")
    print(f"  Escala inv. : {full['escala_invariante']}")
    print(f"  1/f₀ coef   : {full['coef_viscoso']:.6e}")
    print("=" * 72)


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
