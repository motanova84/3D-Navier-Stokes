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
from typing import Dict, Any

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
