#!/usr/bin/env python3
"""
NOESIS Axiom Zero — Continuous Macroscopic Coherence Field (QCAL)
=================================================================

Formalises the Collective Phase Field Theory (QCAL) framework that replaces
the reductionist molecular-pair description with a continuous macroscopic
coherence field ψ(r, t).

Core quantities implemented
---------------------------

1. Temporal first-order autocorrelation Ψ (normalised):

       Ψ = |⟨ψ*(r,t) ψ(r,t+τ)⟩_{r,t}| / ⟨|ψ(r,t)|²⟩_{r,t}

2. Spectral-purity coherence estimator (frequency domain):

       Ψ = 1 − σ_f / f₀

   where σ_f = sqrt( ⟨(f(t)−f₀)²⟩ ) is the standard deviation of the
   instantaneous frequency around the base frequency f₀ = 141.7001 Hz,
   extracted via the Hilbert/analytic-signal phase derivative.

3. Combined uncertainty of Ψ via GUM variance propagation:

       u²(Ψ) = (1/f₀)² · u²(σ_f)  +  (σ_f/f₀²)² · u²(f₀)

4. Phase-coherence threshold: Ψ_total = 0.999999  ↔  σ_f → 0.

5. Integration-region constraints:
   - Spatial: ∇ψ · n = 0 on ∂Ω  (Neumann boundary)
   - Temporal: T ≫ 1/f₀ ≈ 7.057 ms;  typical T ~ 1 s … 100 s

References
----------
  NOESIS_Axiom_Zero_Continuous_Coherence formulation (problem statement 1).
"""

from __future__ import annotations

from dataclasses import dataclass
from math import pi, sqrt
from typing import Optional, Tuple

import numpy as np

# ---------------------------------------------------------------------------
# Physical / system constants
# ---------------------------------------------------------------------------

#: Base frequency invariant [Hz]
F0_HZ: float = 141.7001

#: Coherence unity threshold  (Ψ = 1 − ε, ε → 0)
PSI_TOTAL: float = 0.999999

#: Von Neumann entropy upper bound for zero-chaos limit
S_VN_MAX: float = 0.01

#: Minimum integration window  T_min ≫ 1/f₀  [s]
T_MIN_S: float = 10.0 / F0_HZ  # ≈ 70.6 ms  (conservative ×10 margin)


# ---------------------------------------------------------------------------
# Data containers
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class CoherenceEstimate:
    """Result of a coherence calculation."""

    psi: float  # Ψ ∈ [0, 1]
    sigma_f_hz: float  # Instantaneous-frequency std dev [Hz]
    f0_hz: float  # Reference frequency used [Hz]


@dataclass(frozen=True)
class CoherenceUncertainty:
    """GUM-propagated uncertainty of the Ψ estimator."""

    u_psi: float  # Combined standard uncertainty of Ψ
    u_sigma_f_hz: float  # Input uncertainty of σ_f [Hz]
    u_f0_hz: float  # Input uncertainty of f₀ [Hz]
    sigma_f_hz: float  # σ_f value at which the budget is evaluated [Hz]
    f0_hz: float  # f₀ value at which the budget is evaluated [Hz]


@dataclass(frozen=True)
class IntegrationRegion:
    """Spatial and temporal integration domain for the coherence field."""

    #: Spatial volume [m³]  — informational; Neumann BC applied on boundary
    volume_m3: float
    #: Integration window T [s]
    window_s: float
    #: Whether the temporal window satisfies T ≫ 1/f₀
    window_adequate: bool
    #: Larmor period 1/f₀ [s]
    larmor_period_s: float


# ---------------------------------------------------------------------------
# Core computations
# ---------------------------------------------------------------------------


def spectral_purity_coherence(
    signal: np.ndarray,
    sample_rate_hz: float,
    f0_hz: float = F0_HZ,
) -> CoherenceEstimate:
    """
    Estimate Ψ via spectral-purity / Hilbert-transform method.

    Steps
    -----
    1. Band-pass the analytic signal around f₀ using the Hilbert transform.
    2. Extract instantaneous phase φ(t) = arg(ψ(t)).
    3. Compute instantaneous frequency f(t) = dφ/dt / 2π.
    4. Evaluate σ_f = sqrt(⟨(f(t) − f₀)²⟩).
    5. Return Ψ = 1 − σ_f / f₀  (clamped to [0, 1]).

    Parameters
    ----------
    signal:
        1-D real-valued field samples.
    sample_rate_hz:
        Sampling rate [Hz].
    f0_hz:
        Reference/base frequency [Hz].

    Returns
    -------
    CoherenceEstimate
    """
    if sample_rate_hz <= 0:
        raise ValueError("sample_rate_hz must be > 0")
    if f0_hz <= 0:
        raise ValueError("f0_hz must be > 0")
    if len(signal) < 4:
        raise ValueError("Signal too short for phase analysis (need ≥ 4 samples)")

    from scipy.signal import hilbert  # local import to keep scipy optional at module level

    analytic = hilbert(signal)
    phase = np.unwrap(np.angle(analytic))
    # Instantaneous frequency via central differences; discard edge samples
    dt = 1.0 / sample_rate_hz
    f_inst = np.diff(phase) / (2.0 * pi * dt)
    sigma_f = float(np.std(f_inst - f0_hz))

    psi = max(0.0, min(1.0, 1.0 - sigma_f / f0_hz))
    return CoherenceEstimate(psi=psi, sigma_f_hz=sigma_f, f0_hz=f0_hz)


def autocorrelation_coherence(
    field_samples: np.ndarray,
    tau_samples: int = 1,
) -> float:
    """
    Estimate Ψ as the normalised first-order temporal autocorrelation.

    Ψ = |⟨ψ*(t) ψ(t+τ)⟩| / ⟨|ψ(t)|²⟩

    Parameters
    ----------
    field_samples:
        1-D complex or real field  ψ(t).
    tau_samples:
        Time-lag in samples for the correlation (default 1 sample).

    Returns
    -------
    float
        Ψ ∈ [0, 1].
    """
    if len(field_samples) < tau_samples + 2:
        raise ValueError("field_samples too short for the requested lag")
    if tau_samples < 1:
        raise ValueError("tau_samples must be ≥ 1")

    psi_t = field_samples[:-tau_samples].astype(complex)
    psi_tau = field_samples[tau_samples:].astype(complex)

    numerator = float(np.abs(np.mean(np.conj(psi_t) * psi_tau)))
    denominator = float(np.mean(np.abs(field_samples) ** 2))

    if denominator == 0.0:
        return 0.0

    return max(0.0, min(1.0, numerator / denominator))


def coherence_uncertainty(
    sigma_f_hz: float,
    u_sigma_f_hz: float,
    f0_hz: float = F0_HZ,
    u_f0_hz: float = 0.0,
) -> CoherenceUncertainty:
    """
    Propagate GUM uncertainty to the Ψ estimator.

    Ψ = 1 − σ_f / f₀

    Partial derivatives:
        ∂Ψ/∂σ_f = −1/f₀
        ∂Ψ/∂f₀  =  σ_f / f₀²

    Combined uncertainty (no correlation assumed):
        u²(Ψ) = (1/f₀)² · u²(σ_f)  +  (σ_f/f₀²)² · u²(f₀)

    Parameters
    ----------
    sigma_f_hz:
        Estimated σ_f [Hz].
    u_sigma_f_hz:
        Standard uncertainty of σ_f [Hz].
    f0_hz:
        Reference frequency [Hz].
    u_f0_hz:
        Standard uncertainty of f₀ [Hz]  (0 if treated as exact).

    Returns
    -------
    CoherenceUncertainty
    """
    if f0_hz <= 0:
        raise ValueError("f0_hz must be > 0")
    if sigma_f_hz < 0:
        raise ValueError("sigma_f_hz must be ≥ 0")
    if u_sigma_f_hz < 0:
        raise ValueError("u_sigma_f_hz must be ≥ 0")
    if u_f0_hz < 0:
        raise ValueError("u_f0_hz must be ≥ 0")

    term_sigma = (1.0 / f0_hz) ** 2 * u_sigma_f_hz ** 2
    term_f0 = (sigma_f_hz / f0_hz ** 2) ** 2 * u_f0_hz ** 2
    u_psi = sqrt(term_sigma + term_f0)

    return CoherenceUncertainty(
        u_psi=u_psi,
        u_sigma_f_hz=u_sigma_f_hz,
        u_f0_hz=u_f0_hz,
        sigma_f_hz=sigma_f_hz,
        f0_hz=f0_hz,
    )


def psi_threshold_sigma_f(
    psi_min: float = PSI_TOTAL,
    f0_hz: float = F0_HZ,
) -> float:
    """
    Return the maximum σ_f [Hz] compatible with Ψ ≥ psi_min.

        σ_f_max = f₀ · (1 − Ψ_min)

    Parameters
    ----------
    psi_min:
        Lower bound on Ψ  (default PSI_TOTAL = 0.999999).
    f0_hz:
        Reference frequency [Hz].

    Returns
    -------
    float
        σ_f_max [Hz].
    """
    if not 0.0 < psi_min < 1.0:
        raise ValueError("psi_min must be in (0, 1)")
    if f0_hz <= 0:
        raise ValueError("f0_hz must be > 0")
    return f0_hz * (1.0 - psi_min)


def integration_region(
    volume_m3: float,
    window_s: float,
    f0_hz: float = F0_HZ,
) -> IntegrationRegion:
    """
    Construct and validate an integration region.

    The temporal window is adequate when  T ≥ T_MIN_S = 10/f₀.

    Parameters
    ----------
    volume_m3:
        Spatial domain volume [m³].
    window_s:
        Temporal integration window [s].
    f0_hz:
        Base frequency [Hz].

    Returns
    -------
    IntegrationRegion
    """
    if volume_m3 <= 0:
        raise ValueError("volume_m3 must be > 0")
    if window_s <= 0:
        raise ValueError("window_s must be > 0")
    if f0_hz <= 0:
        raise ValueError("f0_hz must be > 0")

    larmor_period = 1.0 / f0_hz
    adequate = window_s >= 10.0 * larmor_period

    return IntegrationRegion(
        volume_m3=volume_m3,
        window_s=window_s,
        window_adequate=adequate,
        larmor_period_s=larmor_period,
    )
