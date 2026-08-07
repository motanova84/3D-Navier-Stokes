#!/usr/bin/env python3
"""
NOESIS Analytic Rectification — NMR Coherence Ceiling & Algebraic Reframing
============================================================================

Formalises the analytic rectification that establishes the internal
consistency between metrology, quantum mechanics and information theory
within the QCAL/NOESIS framework.

Three independent formal results are implemented
------------------------------------------------

1. **Invariant B₀ derivation** (CODATA proton gyromagnetic ratio)

       f₀ = γ_p / (2π) · B₀

       → B₀ = 2π · f₀ / γ_p

   Using CODATA 2018 value  γ_p = 2.6752218744 × 10⁸ rad·s⁻¹·T⁻¹
   and f₀ = 141.7001 Hz gives  B₀ ≈ 3.327 µT.

2. **Fourier-T₂* linewidth bound (NMR coherence ceiling)**

   For a Lorentzian free-induction decay with decay constant T₂*:

       Δf_FWHM = 1 / (π · T₂*)

   The standard deviation of a Lorentzian line:
       σ_f ≥ Δf_FWHM / (2·√2)  =  1 / (2π·√2·T₂*)

   The resulting ceiling on the spectral-purity Ψ estimator:
       Ψ_max(T₂*) = 1 − σ_f_min / f₀
                  = 1 − 1 / (2π·√2·T₂*·f₀)

   This demonstrates that  Ψ ≥ 0.999999  is physically unreachable via
   conventional NMR free-induction decay.

3. **Algebraic / cryptographic reframing**

   Ψ = 0.999999 and f₀ = 141.7001 Hz operate as algebraic constraints and
   cryptographic primitives within zero-knowledge proof circuits
   (Circom / Groth16) and the Lean 4 theorem prover.  The formal invariant
   is independent of any empirical phenomenology of liquid water.

References
----------
  NOESIS Analytic Rectification (problem statement 2).
  CODATA 2018: https://physics.nist.gov/cgi-bin/cuu/Value?gammap
"""

from __future__ import annotations

from dataclasses import dataclass
from math import pi, sqrt
from typing import Optional, Tuple

# ---------------------------------------------------------------------------
# CODATA 2018 constants
# ---------------------------------------------------------------------------

#: Proton gyromagnetic ratio  [rad·s⁻¹·T⁻¹]  (CODATA 2018)
GAMMA_P_RAD_S_T: float = 2.6752218744e8

#: Reduced gyromagnetic ratio  γ_p / 2π  [Hz·T⁻¹]
GAMMA_P_HZ_PER_T: float = GAMMA_P_RAD_S_T / (2.0 * pi)

#: Reduced gyromagnetic ratio  γ_p / 2π  [Hz·µT⁻¹]
GAMMA_P_HZ_PER_UT: float = GAMMA_P_HZ_PER_T * 1e-6

#: Base frequency invariant  [Hz]
F0_HZ: float = 141.7001

#: Coherence threshold  (algebraic / cryptographic invariant)
PSI_TOTAL: float = 0.999999

#: Derived shielded static field  [µT]
B0_SHIELDED_UT: float = F0_HZ / GAMMA_P_HZ_PER_UT  # ≈ 3.327 µT


# ---------------------------------------------------------------------------
# Data containers
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class B0DerivationResult:
    """Result of the B₀ derivation from CODATA constants."""

    b0_uT: float  # Derived static field [µT]
    f0_hz: float  # Base frequency used [Hz]
    gamma_p_hz_per_uT: float  # Reduced gyromagnetic ratio used [Hz·µT⁻¹]
    larmor_check_hz: float  # f₀ recomputed from B₀ — should equal f₀ [Hz]
    residual_hz: float  # |f₀ − larmor_check| [Hz]


@dataclass(frozen=True)
class FourierBound:
    """Linewidth-limited coherence ceiling for a given T₂*."""

    t2_star_s: float  # Input T₂* [s]
    delta_f_fwhm_hz: float  # FWHM linewidth  1/(π·T₂*) [Hz]
    sigma_f_min_hz: float  # Minimum σ_f = FWHM / (2·√2) [Hz]
    psi_max: float  # Ψ_max = 1 − σ_f_min / f₀  (clamped to [0,1])
    psi_threshold_reachable: bool  # Whether PSI_TOTAL is reachable at this T₂*


@dataclass(frozen=True)
class AlgebraicInvariant:
    """
    Algebraic / cryptographic invariant declaration.

    f₀ and Ψ operate as formal constants in ZK-proof circuits and Lean 4,
    independent of any empirical water-structure claims.
    """

    f0_hz: float
    psi: float
    circuit_system: str  # e.g. "Circom/Groth16"
    prover_system: str  # e.g. "Lean 4"
    is_empirical: bool  # Must be False: no empirical water-structure assumption


# ---------------------------------------------------------------------------
# Core computations
# ---------------------------------------------------------------------------


def derive_b0(
    f0_hz: float = F0_HZ,
    gamma_p_hz_per_uT: float = GAMMA_P_HZ_PER_UT,
) -> B0DerivationResult:
    """
    Derive the shielded static field B₀ from the Larmor relation.

        B₀ = f₀ / (γ_p / 2π)   [µT]

    Parameters
    ----------
    f0_hz:
        Target Larmor frequency [Hz].
    gamma_p_hz_per_uT:
        Reduced gyromagnetic ratio [Hz·µT⁻¹].

    Returns
    -------
    B0DerivationResult
    """
    if f0_hz <= 0:
        raise ValueError("f0_hz must be > 0")
    if gamma_p_hz_per_uT <= 0:
        raise ValueError("gamma_p_hz_per_uT must be > 0")

    b0 = f0_hz / gamma_p_hz_per_uT
    larmor_check = gamma_p_hz_per_uT * b0
    residual = abs(f0_hz - larmor_check)

    return B0DerivationResult(
        b0_uT=b0,
        f0_hz=f0_hz,
        gamma_p_hz_per_uT=gamma_p_hz_per_uT,
        larmor_check_hz=larmor_check,
        residual_hz=residual,
    )


def fourier_coherence_bound(
    t2_star_s: float,
    f0_hz: float = F0_HZ,
    psi_threshold: float = PSI_TOTAL,
) -> FourierBound:
    """
    Compute the Fourier-limited NMR coherence ceiling.

    For a Lorentzian FID with decay constant T₂*:

        Δf_FWHM = 1 / (π · T₂*)
        σ_f_min = Δf_FWHM / (2·√2)
        Ψ_max   = 1 − σ_f_min / f₀

    Parameters
    ----------
    t2_star_s:
        Effective transverse relaxation time [s].
    f0_hz:
        Reference frequency [Hz].
    psi_threshold:
        Coherence level to test reachability against (default PSI_TOTAL).

    Returns
    -------
    FourierBound
    """
    if t2_star_s <= 0:
        raise ValueError("t2_star_s must be > 0")
    if f0_hz <= 0:
        raise ValueError("f0_hz must be > 0")
    if not 0.0 < psi_threshold < 1.0:
        raise ValueError("psi_threshold must be in (0, 1)")

    delta_f = 1.0 / (pi * t2_star_s)
    sigma_f_min = delta_f / (2.0 * sqrt(2.0))
    psi_max = max(0.0, min(1.0, 1.0 - sigma_f_min / f0_hz))
    reachable = psi_max >= psi_threshold

    return FourierBound(
        t2_star_s=t2_star_s,
        delta_f_fwhm_hz=delta_f,
        sigma_f_min_hz=sigma_f_min,
        psi_max=psi_max,
        psi_threshold_reachable=reachable,
    )


def psi_ceiling_requires_t2_star(
    psi_target: float = PSI_TOTAL,
    f0_hz: float = F0_HZ,
) -> float:
    """
    Return the T₂* [s] required so that Ψ_max ≥ psi_target.

    Solving  psi_target = 1 − 1 / (2π·√2·T₂*·f₀)  for T₂*:

        T₂*_min = 1 / (2π·√2·f₀·(1−psi_target))

    Parameters
    ----------
    psi_target:
        Desired coherence lower bound.
    f0_hz:
        Reference frequency [Hz].

    Returns
    -------
    float
        Minimum T₂* [s].
    """
    if not 0.0 < psi_target < 1.0:
        raise ValueError("psi_target must be in (0, 1)")
    if f0_hz <= 0:
        raise ValueError("f0_hz must be > 0")
    return 1.0 / (2.0 * pi * sqrt(2.0) * f0_hz * (1.0 - psi_target))


def algebraic_invariant(
    f0_hz: float = F0_HZ,
    psi: float = PSI_TOTAL,
    circuit_system: str = "Circom/Groth16",
    prover_system: str = "Lean 4",
) -> AlgebraicInvariant:
    """
    Declare the algebraic / cryptographic invariant.

    Ψ and f₀ function as algebraic primitives in ZK-proof circuits and a
    formal theorem prover.  This function simply packages and validates the
    declaration — it asserts that no empirical water-structure assumption is
    encoded.

    Parameters
    ----------
    f0_hz:
        Frequency invariant [Hz].
    psi:
        Coherence invariant (≡ PSI_TOTAL).
    circuit_system:
        ZK circuit / proving system identifier.
    prover_system:
        Formal proof system identifier.

    Returns
    -------
    AlgebraicInvariant
    """
    if f0_hz <= 0:
        raise ValueError("f0_hz must be > 0")
    if not 0.0 < psi <= 1.0:
        raise ValueError("psi must be in (0, 1]")

    return AlgebraicInvariant(
        f0_hz=f0_hz,
        psi=psi,
        circuit_system=circuit_system,
        prover_system=prover_system,
        is_empirical=False,  # invariant: no phenomenological claim on water
    )
