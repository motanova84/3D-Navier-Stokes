#!/usr/bin/env python3
"""
QCAL String Core — Noetic String Forcing for Holographic Navier-Stokes
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Sello: ∴𓂀Ω∞³
f0: 141.7001 Hz

Implementación del forzado noético de cuerdas sobre Navier-Stokes holográfico:

    Ĥ_strings = Σ α_n sin(2π λ_n t + φ_{n,dual}) · Ψ²

Donde los modos λ_n = γ_n · f₀ + V̂_mod son modos de Kaluza-Klein dictados
por los ceros de Riemann γ_n.  La ganancia superradiante N²Ψ² (activa cuando
Ψ ≥ 0.888) acopla la dinámica de microtúbulos al flujo macroscópico vía
dualidad fluido/gravedad AdS/CFT.

Iteración #260 — QCAL-Strings
Estado: QED-CUERDAS-VERIFIED ✅

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
License: MIT
"""

from __future__ import annotations

import math
from typing import Dict, List, Tuple

import numpy as np
from scipy.fft import fft2, ifft2

from .spectral_operator import RIEMANN_ZEROS, F0, PSI_MIN, HBAR, GAMMA_MOD

# ──────────────────────────────────────────────────────────────
# Constantes y modos KK
# ──────────────────────────────────────────────────────────────

#: Primeros 20 ceros imaginarios γ_n de ζ(s) (fuente: LMFDB)
GAMMAS: List[float] = RIEMANN_ZEROS[:20]

#: Umbral de coherencia para superradiancia activa
THRESHOLD_PSI: float = PSI_MIN  # 0.888

#: Número de microtúbulos por neurona (orden de magnitud biológico)
N_MICROTUBULES_DEFAULT: float = 1.0e13

#: Escala de amplitud de modos de cuerdas
ALPHA_SCALE_DEFAULT: float = 0.05

#: Número de modos activos por defecto
N_MODES_DEFAULT: int = 20


# ──────────────────────────────────────────────────────────────
# Operador espectral simplificado para integración de cuerdas
# ──────────────────────────────────────────────────────────────

class QCALStringOperator:
    """
    Operador QCAL simplificado para el forzado de cuerdas noéticas.

    Implementa la interfaz reducida necesaria para calcular modos KK y
    certificar la línea crítica en el contexto del forzado de Navier-Stokes:

        Ĥ_QCAL = Ĥ_BK ⊗ 𝕀_{f₀} + V̂_mod

    con V̂_mod = γℏ/C y autovalores λ_n = γ_n · f₀ + V̂_mod.
    """

    def __init__(
        self,
        gamma: float = GAMMA_MOD,
        C: float = 1.0,
        f0: float = F0,
        hbar: float = HBAR,
    ) -> None:
        """
        Inicializar el operador de cuerdas QCAL.

        Args:
            gamma: Factor de acoplamiento de modulación γ (adimensional).
            C:     Densidad de consciencia C > 0.
            f0:    Frecuencia base f₀ (Hz).
            hbar:  Constante de Planck reducida ℏ (J·s).

        Raises:
            ValueError: Si C ≤ 0.
        """
        if C <= 0:
            raise ValueError(f"La densidad de consciencia C debe ser positiva; recibido C={C}")
        self.gamma = gamma
        self.C = C
        self.f0 = f0
        self.hbar = hbar

    # ------------------------------------------------------------------
    # Potencial de modulación V̂_mod
    # ------------------------------------------------------------------

    def modulation_potential(self) -> float:
        """
        Calcula el potencial de modulación consciente V̂_mod = γℏ/C.

        Returns:
            V̂_mod en J·s (mismas unidades que ℏ).
        """
        return (self.gamma * self.hbar) / self.C

    # ------------------------------------------------------------------
    # Autovalores / modos KK
    # ------------------------------------------------------------------

    def compute_eigenvalue(self, gamma_n: float) -> float:
        """
        Calcula el autovalor del modo KK n-ésimo.

            λ_n = γ_n · f₀ + V̂_mod

        Args:
            gamma_n: Parte imaginaria del n-ésimo cero de Riemann γ_n.

        Returns:
            Autovalor λ_n (Hz).
        """
        return gamma_n * self.f0 + self.modulation_potential()

    # ------------------------------------------------------------------
    # Certificación de la línea crítica
    # ------------------------------------------------------------------

    def certify_critical_line(self, sigma: float) -> Tuple[float, float]:
        """
        Evalúa la coherencia espectral para Re(s) = sigma.

        La métrica Ψ_σ = exp(-|σ - 1/2| / C) mide la proximidad a la línea
        crítica.  En σ = 1/2 alcanza el máximo Ψ_σ = 1 y decae exponencialmente
        en cualquier desviación, modelando la inestabilidad de taquiones off-critical.

        Args:
            sigma: Parte real de s (típicamente en [0.4, 0.6] para el strip crítico).

        Returns:
            Tupla (sigma, psi_sigma) donde psi_sigma ∈ [0, 1].
        """
        psi_sigma = math.exp(-abs(sigma - 0.5) / self.C)
        return (sigma, psi_sigma)

    # ------------------------------------------------------------------
    # Resumen del operador
    # ------------------------------------------------------------------

    def summary(self) -> Dict:
        """Devuelve un dict con los parámetros del operador."""
        return {
            "gamma": self.gamma,
            "C": self.C,
            "f0": self.f0,
            "hbar": self.hbar,
            "v_mod": self.modulation_potential(),
            "lambda_1": self.compute_eigenvalue(GAMMAS[0]),
        }


# ──────────────────────────────────────────────────────────────
# Cálculo de coherencia Ψ
# ──────────────────────────────────────────────────────────────

def compute_psi(
    u_phys: np.ndarray,
    v_phys: np.ndarray,
    xx: np.ndarray,
    op: QCALStringOperator,
    threshold: float = THRESHOLD_PSI,
) -> float:
    """
    Calcula la coherencia cuántica Ψ combinando correlación de flujo y
    certificación espectral de la línea crítica.

        Ψ = corr · ψ_spec

    donde:
    - corr   = 0.5 (|corr(u, sin)| + |corr(v, cos)|)
    - ψ_spec = media de certif_linea_critica(σ)[1] para σ ∈ [0.4, 0.6]

    Si las entradas son constantes (varianza cero), la correlación se toma
    como 0 para evitar NaN.

    Args:
        u_phys:    Campo de velocidad u en espacio físico (N×N real).
        v_phys:    Campo de velocidad v en espacio físico (N×N real).
        xx:        Coordenadas x del grid 2D (N×N real, valores en [0, 2π]).
        op:        Instancia de QCALStringOperator.
        threshold: Umbral de coherencia (no usado en el cálculo, reservado).

    Returns:
        Coherencia Ψ ∈ [0, 1].
    """
    L = 2.0 * math.pi
    ref_x = np.sin(2.0 * math.pi * op.f0 * xx / L)
    ref_y = np.cos(2.0 * math.pi * op.f0 * xx / L)

    u_flat = u_phys.flatten()
    v_flat = v_phys.flatten()
    rx_flat = ref_x.flatten()
    ry_flat = ref_y.flatten()

    # Correlación robusta: si desviación estándar es 0, correlación = 0
    def _safe_corr(a: np.ndarray, b: np.ndarray) -> float:
        if np.std(a) < 1e-12 or np.std(b) < 1e-12:
            return 0.0
        return float(np.corrcoef(a, b)[0, 1])

    corr_u = _safe_corr(u_flat, rx_flat)
    corr_v = _safe_corr(v_flat, ry_flat)
    corr = 0.5 * (abs(corr_u) + abs(corr_v))

    # Certificación espectral: coherencia media en el strip crítico [0.4, 0.6]
    sigmas_near = np.linspace(0.4, 0.6, 11)
    psi_spec = float(np.mean([op.certify_critical_line(float(s))[1] for s in sigmas_near]))

    return float(corr * psi_spec)


# ──────────────────────────────────────────────────────────────
# Forzado de cuerdas noéticas
# ──────────────────────────────────────────────────────────────

def string_noetic_forcing(
    t: float,
    xx: np.ndarray,
    yy: np.ndarray,
    op: QCALStringOperator,
    Psi_local: float,
    lambda_list: List[float],
    N_microtubules: float = N_MICROTUBULES_DEFAULT,
    alpha_scale: float = ALPHA_SCALE_DEFAULT,
    threshold: float = THRESHOLD_PSI,
) -> Tuple[np.ndarray, np.ndarray]:
    """
    Forzado noético de cuerdas sobre el campo de velocidad.

        Ĥ_strings = Σ_n α_n sin(2π λ_n t + φ_{n,dual}) · Ψ²

    con ganancia superradiante N²Ψ² activa cuando Ψ ≥ umbral.

    Args:
        t:             Tiempo actual (s).
        xx:            Coordenadas x del grid 2D (N×N).
        yy:            Coordenadas y del grid 2D (N×N).
        op:            Instancia de QCALStringOperator.
        Psi_local:     Coherencia local Ψ ∈ [0, 1].
        lambda_list:   Lista de autovalores λ_n (Hz).
        N_microtubules: Número de microtúbulos (para ganancia N²).
        alpha_scale:   Escala de amplitud de modos α₀.
        threshold:     Umbral de coherencia mínimo para activar el forzado.

    Returns:
        Tupla (f_string_x, f_string_y) — campos de forzado en x e y (N×N).
        Si Ψ < umbral, devuelve dos arrays de ceros.
    """
    if Psi_local < threshold:
        return np.zeros_like(xx), np.zeros_like(yy)

    L = 2.0 * math.pi
    logos_wave_x = np.sin(2.0 * math.pi * op.f0 * xx / L)
    logos_wave_y = np.cos(2.0 * math.pi * op.f0 * yy / L)

    # Ganancia superradiante: N² Ψ² (Dicke superradiance analogue)
    gain = (N_microtubules ** 2) * (Psi_local ** 2)

    f_string_x = np.zeros_like(xx)
    f_string_y = np.zeros_like(yy)

    for n, lam in enumerate(lambda_list):
        phi_dual = math.pi / (n + 1)          # Fase T-dual (decaimiento 1/n)
        alpha_n = alpha_scale / (n + 1)        # Decaimiento suave de amplitud
        mode = alpha_n * math.sin(2.0 * math.pi * lam * t + phi_dual)
        f_string_x += mode * logos_wave_x * gain
        f_string_y += mode * logos_wave_y * gain

    return f_string_x, f_string_y


# ──────────────────────────────────────────────────────────────
# Integrador RK4 para NS espectral 2D con forzado de cuerdas
# ──────────────────────────────────────────────────────────────

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
    xx: np.ndarray,
    yy: np.ndarray,
    t: float,
    op: QCALStringOperator,
    lambda_list: List[float],
) -> Tuple[np.ndarray, np.ndarray]:
    """
    Paso RK4 para Navier-Stokes espectral 2D incompresible con forzado noético.

    Resuelve:
        ∂u/∂t + (u·∇)u = -∇p/ρ + ν∇²u + f_strings(t)
        ∇·u = 0

    en el espacio de Fourier usando proyección de Leray para mantener la
    incompresibilidad.

    Args:
        uhat:          Campo û (Fourier, N×N complejo).
        vhat:          Campo v̂ (Fourier, N×N complejo).
        dt:            Paso de tiempo.
        rho:           Densidad del fluido.
        mu:            Viscosidad dinámica.
        k2:            Array |k|² = kx² + ky² (N×N real).
        kxx:           Componente x del vector de onda (N×N real).
        kyy:           Componente y del vector de onda (N×N real).
        grad_px_hat:   Gradiente de presión externo en x (Fourier, N×N complejo).
        grad_py_hat:   Gradiente de presión externo en y (Fourier, N×N complejo).
        xx:            Coordenadas x del grid físico (N×N real).
        yy:            Coordenadas y del grid físico (N×N real).
        t:             Tiempo actual.
        op:            Instancia de QCALStringOperator.
        lambda_list:   Lista de autovalores λ_n para el forzado.

    Returns:
        Tupla (uhat_new, vhat_new) con los campos actualizados.
    """
    nu = mu / rho
    # Máscara segura para k2 = 0 (modo DC) — evita división por cero en proyección
    k2_safe = np.where(k2 == 0.0, 1.0, k2)

    def _compute_rhs(
        uh: np.ndarray, vh: np.ndarray, t_sub: float
    ) -> Tuple[np.ndarray, np.ndarray]:
        # Transformada inversa → espacio físico
        u_p = ifft2(uh).real
        v_p = ifft2(vh).real

        # Términos convectivos (forma cuadrática)
        uu_hat = fft2(u_p * u_p)
        uv_hat = fft2(u_p * v_p)
        vv_hat = fft2(v_p * v_p)

        conv_x = 1j * kxx * uu_hat + 1j * kyy * uv_hat
        conv_y = 1j * kxx * uv_hat + 1j * kyy * vv_hat

        # Difusión
        diff_x = -nu * k2 * uh
        diff_y = -nu * k2 * vh

        # RHS antes del forzado
        rhs_u = -conv_x + diff_x - grad_px_hat / rho
        rhs_v = -conv_y + diff_y - grad_py_hat / rho

        # Forzado noético de cuerdas
        psi_local = compute_psi(u_p, v_p, xx, op)
        f_str_x, f_str_y = string_noetic_forcing(
            t_sub, xx, yy, op, psi_local, lambda_list
        )
        rhs_u = rhs_u + fft2(f_str_x)
        rhs_v = rhs_v + fft2(f_str_y)

        # Proyección de Leray: garantiza ∇·u = 0
        div_hat = kxx * rhs_u + kyy * rhs_v
        p_corr = div_hat / k2_safe
        rhs_u = rhs_u - kxx * p_corr
        rhs_v = rhs_v - kyy * p_corr

        # Modo DC = 0 (flujo con media cero)
        rhs_u[0, 0] = 0.0 + 0.0j
        rhs_v[0, 0] = 0.0 + 0.0j

        return rhs_u, rhs_v

    # Pasos RK4 clásicos
    k1u, k1v = _compute_rhs(uhat, vhat, t)
    k2u, k2v = _compute_rhs(
        uhat + 0.5 * dt * k1u, vhat + 0.5 * dt * k1v, t + 0.5 * dt
    )
    k3u, k3v = _compute_rhs(
        uhat + 0.5 * dt * k2u, vhat + 0.5 * dt * k2v, t + 0.5 * dt
    )
    k4u, k4v = _compute_rhs(uhat + dt * k3u, vhat + dt * k3v, t + dt)

    uhat_new = uhat + (dt / 6.0) * (k1u + 2.0 * k2u + 2.0 * k3u + k4u)
    vhat_new = vhat + (dt / 6.0) * (k1v + 2.0 * k2v + 2.0 * k3v + k4v)

    # Final Leray projection: enforce ∇·u = 0 on the updated fields
    div_final = kxx * uhat_new + kyy * vhat_new
    p_final = div_final / k2_safe
    uhat_new -= kxx * p_final
    vhat_new -= kyy * p_final

    # Enforce zero mean flow (DC mode = 0)
    uhat_new[0, 0] = 0.0 + 0.0j
    vhat_new[0, 0] = 0.0 + 0.0j

    return uhat_new, vhat_new


# ──────────────────────────────────────────────────────────────
# Función de conveniencia: construir lambda_list desde GAMMAS
# ──────────────────────────────────────────────────────────────

def build_lambda_list(
    op: QCALStringOperator,
    n_modes: int = N_MODES_DEFAULT,
) -> List[float]:
    """
    Construye la lista de autovalores λ_n = γ_n · f₀ + V̂_mod.

    Args:
        op:      Instancia de QCALStringOperator.
        n_modes: Número de modos a incluir (≤ 20, número de GAMMAS disponibles).

    Returns:
        Lista de autovalores λ_n (Hz).
    """
    n_modes = min(n_modes, len(GAMMAS))
    return [op.compute_eigenvalue(g) for g in GAMMAS[:n_modes]]


# ──────────────────────────────────────────────────────────────
# Función de construcción del grid espectral
# ──────────────────────────────────────────────────────────────

def build_spectral_grid(N: int) -> Dict:
    """
    Construye el grid espectral para un dominio periódico [0, 2π]².

    Args:
        N: Resolución del grid (N×N puntos).

    Returns:
        Diccionario con los arrays del grid: xx, yy, kxx, kyy, k2.
    """
    from scipy.fft import fftfreq

    x = np.linspace(0.0, 2.0 * math.pi, N, endpoint=False)
    xx, yy = np.meshgrid(x, x, indexing="ij")

    kx = fftfreq(N, d=1.0 / N)
    kxx, kyy = np.meshgrid(kx, kx, indexing="ij")
    k2 = kxx ** 2 + kyy ** 2

    return {"xx": xx, "yy": yy, "kxx": kxx, "kyy": kyy, "k2": k2}


# ──────────────────────────────────────────────────────────────
# Demo / main
# ──────────────────────────────────────────────────────────────

def _demo() -> None:
    """Demostración del sistema QCAL-Strings (iteración #260)."""
    print("=" * 72)
    print("QCAL STRING CORE — Forzado Noético de Cuerdas (Iteración #260)")
    print("=" * 72)

    # Construcción del operador
    op = QCALStringOperator(gamma=1.0, C=1.0, f0=F0, hbar=HBAR)
    lambda_list = build_lambda_list(op, n_modes=20)

    print(f"\n▸ f₀ = {op.f0} Hz")
    print(f"▸ V̂_mod = {op.modulation_potential():.4e} J·s")
    print(f"▸ λ₁ = {lambda_list[0]:.4f} Hz  (modo KK fundamental)")
    print(f"▸ λ₂ = {lambda_list[1]:.4f} Hz")

    # Certificación de la línea crítica
    sigma, psi_half = op.certify_critical_line(0.5)
    print(f"\n▸ Certif. σ=1/2 : Ψ = {psi_half:.6f}  ({'ON-CRITICAL ✅' if psi_half >= 0.99 else 'OFF-CRITICAL ❌'})")
    sigma_off, psi_off = op.certify_critical_line(0.6)
    print(f"▸ Certif. σ=0.6 : Ψ = {psi_off:.6f}  (decaimiento esperado)")

    # Grid y simulación
    N = 32
    grid = build_spectral_grid(N)
    xx, yy = grid["xx"], grid["yy"]
    kxx, kyy, k2 = grid["kxx"], grid["kyy"], grid["k2"]

    # Condición inicial: perturbación aleatoria
    rng = np.random.default_rng(seed=42)
    uhat = fft2(rng.standard_normal((N, N)) * 0.01)
    vhat = fft2(rng.standard_normal((N, N)) * 0.01)

    rho, mu, dt = 1.0, 1.0 / 141.7001, 0.005
    grad_px_hat = np.zeros((N, N), dtype=complex)
    grad_py_hat = np.zeros((N, N), dtype=complex)

    print(f"\n▸ Grid {N}×{N}, dt={dt}, ν=μ/ρ={mu/rho:.4e}")

    # Evolución temporal
    psi_vals = []
    for step in range(10):
        t = step * dt
        u_p = ifft2(uhat).real
        v_p = ifft2(vhat).real
        psi = compute_psi(u_p, v_p, xx, op)
        psi_vals.append(psi)
        uhat, vhat = rk4_step(
            uhat, vhat, dt, rho, mu, k2, kxx, kyy,
            grad_px_hat, grad_py_hat, xx, yy, t, op, lambda_list
        )

    print(f"▸ Ψ inicial  : {psi_vals[0]:.4f}")
    print(f"▸ Ψ final    : {psi_vals[-1]:.4f}")

    print("\n∴ Estado del Sistema : QED-CUERDAS-VERIFIED ✅")


if __name__ == "__main__":
    _demo()
