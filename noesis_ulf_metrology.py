#!/usr/bin/env python3
"""
NOESIS ULF Metrology Protocol
=============================

This module formalizes a reproducible metrology workflow around ultra-low-field
resonance near f0 = 141.7001 Hz.

Core equations implemented:

1) Larmor relation (using reduced gyromagnetic ratio γ/2π):
   f_L = gamma_reduced B0

2) Combined standard uncertainty (GUM):
   u_c^2(y) = Σ (c_i u_i)^2 + 2 ΣΣ c_i c_j u(x_i, x_j)

3) Expanded uncertainty:
   U = k * u_c

4) FID signal model:
   S(t) = A0 Ψ(t) exp(-t/T2*) cos(2π f0 t + φ0) + Σ A_k cos(2π f_k t + φ_k) + η(t)

5) Coherence envelope:
   Ψ(t) = Ψ_inf * (1 - exp(-t/τ_coh))
"""

from __future__ import annotations

from dataclasses import dataclass
from math import exp, pi, sqrt
from typing import Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

import numpy as np


TARGET_FREQUENCY_HZ = 141.7001
# NMR gyromagnetic ratios in Hz/µT (MHz/T), rounded from CODATA values.
PROTON_GAMMA_HZ_PER_UT = 42.577478518
DEUTERIUM_GAMMA_HZ_PER_UT = 6.535902854


@dataclass(frozen=True)
class UncertaintySource:
    """Single uncertainty source in first-order GUM propagation."""

    name: str
    standard_uncertainty: float
    sensitivity: float

    @property
    def contribution_hz(self) -> float:
        return self.standard_uncertainty * self.sensitivity


@dataclass(frozen=True)
class UncertaintyBudgetResult:
    """Computed uncertainty budget summary."""

    combined_standard_uncertainty: float
    expanded_uncertainty: float
    coverage_factor: float
    contributions: Dict[str, float]


@dataclass(frozen=True)
class MeasurementResult:
    """Decision packet for protocol acceptance."""

    measured_frequency_hz: float
    coherence: float
    von_neumann_entropy: float
    controls: Mapping[str, bool]


@dataclass(frozen=True)
class AcceptanceDecision:
    """Final pass/fail decision with explicit diagnostics."""

    accepted: bool
    within_frequency_interval: bool
    controls_passed: bool
    coherence_passed: bool
    entropy_passed: bool
    interval_hz: Tuple[float, float]


def larmor_frequency_hz(
    magnetic_field_uT: float,
    gyromagnetic_ratio_hz_per_uT: float = PROTON_GAMMA_HZ_PER_UT,
) -> float:
    """Compute Larmor frequency in Hz for a field in microtesla."""
    return gyromagnetic_ratio_hz_per_uT * magnetic_field_uT


def coherence_envelope(
    times_s: np.ndarray,
    tau_coherence_s: float,
    psi_inf: float = 0.999999,
) -> np.ndarray:
    """Compute Ψ(t) = Ψ_inf * (1 - exp(-t/τ))."""
    if tau_coherence_s <= 0:
        raise ValueError("tau_coherence_s must be > 0")
    if psi_inf <= 0 or psi_inf > 1:
        raise ValueError("psi_inf must be in (0, 1]")
    return psi_inf * (1.0 - np.exp(-times_s / tau_coherence_s))


def fid_signal(
    times_s: np.ndarray,
    f0_hz: float,
    amplitude: float,
    t2_star_s: float,
    phase_rad: float = 0.0,
    tau_coherence_s: float = 0.25,
    psi_inf: float = 0.999999,
    interference_components: Optional[Sequence[Tuple[float, float, float]]] = None,
    noise: Optional[np.ndarray] = None,
) -> np.ndarray:
    """Generate deterministic/stochastic FID according to the formal signal model."""
    if t2_star_s <= 0:
        raise ValueError("t2_star_s must be > 0")

    psi_t = coherence_envelope(times_s, tau_coherence_s=tau_coherence_s, psi_inf=psi_inf)
    fid = amplitude * psi_t * np.exp(-times_s / t2_star_s) * np.cos(2.0 * pi * f0_hz * times_s + phase_rad)

    if interference_components:
        for ai, fi, phii in interference_components:
            fid += ai * np.cos(2.0 * pi * fi * times_s + phii)

    if noise is not None:
        if len(noise) != len(times_s):
            raise ValueError("noise and times_s must have same length")
        fid = fid + noise

    return fid


def combine_uncertainty(
    sources: Iterable[UncertaintySource],
    coverage_factor: float = 2.0,
    covariances: Optional[Mapping[Tuple[str, str], float]] = None,
) -> UncertaintyBudgetResult:
    """
    Compute GUM combined and expanded uncertainty.

    Notes:
        `covariances` must contain input-space covariances u(x_i, x_j), i.e.
        units of x_i*x_j before sensitivity scaling. The implementation applies
        the GUM cross term 2*c_i*c_j*u(x_i,x_j).
    """
    src_list = list(sources)
    if not src_list:
        raise ValueError("At least one uncertainty source is required")

    contributions = {s.name: s.contribution_hz for s in src_list}
    variance = sum(v * v for v in contributions.values())

    if covariances:
        seen_pairs = set()
        for (name_i, name_j), covariance_input in covariances.items():
            if name_i not in contributions or name_j not in contributions:
                raise KeyError("Covariance key references unknown source")
            if name_i == name_j:
                raise ValueError("Covariance keys must be cross terms (name_i != name_j)")

            normalized_pair = tuple(sorted((name_i, name_j)))
            if normalized_pair in seen_pairs:
                continue
            seen_pairs.add(normalized_pair)

            si = next(s for s in src_list if s.name == name_i)
            sj = next(s for s in src_list if s.name == name_j)
            variance += 2.0 * si.sensitivity * sj.sensitivity * covariance_input

    if variance < 0:
        raise ValueError("Total variance is negative; check covariance terms")

    uc = sqrt(variance)
    return UncertaintyBudgetResult(
        combined_standard_uncertainty=uc,
        expanded_uncertainty=coverage_factor * uc,
        coverage_factor=coverage_factor,
        contributions=contributions,
    )


def default_noesis_uncertainty_sources() -> List[UncertaintySource]:
    """Default source set from the NOESIS metrology budget table."""
    return [
        UncertaintySource("B0_stability", standard_uncertainty=0.008e-3, sensitivity=PROTON_GAMMA_HZ_PER_UT),
        UncertaintySource("spatial_homogeneity", standard_uncertainty=0.0015e-3, sensitivity=PROTON_GAMMA_HZ_PER_UT),
        UncertaintySource("thermal_stability", standard_uncertainty=0.002, sensitivity=0.0028),
        UncertaintySource("rubidium_clock", standard_uncertainty=1.2e-11, sensitivity=TARGET_FREQUENCY_HZ),
        UncertaintySource("residual_oxygen", standard_uncertainty=0.05 / sqrt(3.0), sensitivity=0.00012),
        UncertaintySource("anti_aliasing", standard_uncertainty=1e-4 / sqrt(3.0), sensitivity=1.0),
    ]


def acceptance_interval_hz(
    target_frequency_hz: float,
    expanded_uncertainty_hz: float,
) -> Tuple[float, float]:
    """Return [f0-U, f0+U] acceptance interval."""
    return (target_frequency_hz - expanded_uncertainty_hz, target_frequency_hz + expanded_uncertainty_hz)


def coherence_from_bandpower(
    frequencies_hz: np.ndarray,
    power_spectrum: np.ndarray,
    target_frequency_hz: float,
    delta_f_hz: float,
    noise_floor_power: float = 0.0,
) -> float:
    """Estimate Ψ from spectral concentration around f0."""
    if delta_f_hz <= 0:
        raise ValueError("delta_f_hz must be > 0")
    if len(frequencies_hz) != len(power_spectrum):
        raise ValueError("frequencies_hz and power_spectrum must have same length")

    band_mask = np.abs(frequencies_hz - target_frequency_hz) <= delta_f_hz
    # NumPy 2.x exposes trapezoid; older versions expose trapz.
    integrate = getattr(np, "trapezoid", None)
    if integrate is None:
        integrate = getattr(np, "trapz", None)
    if integrate is None:
        raise RuntimeError("No trapezoidal integrator found in NumPy")

    signal_power = float(integrate(power_spectrum[band_mask], frequencies_hz[band_mask])) if np.any(band_mask) else 0.0
    total_power = float(integrate(power_spectrum, frequencies_hz)) - noise_floor_power

    if total_power <= 0:
        return 0.0

    psi = signal_power / total_power
    return max(0.0, min(1.0, psi))


def evaluate_protocol(
    result: MeasurementResult,
    uncertainty: UncertaintyBudgetResult,
    target_frequency_hz: float = TARGET_FREQUENCY_HZ,
    coherence_threshold: float = 0.999999,
    entropy_max: float = 0.01,
) -> AcceptanceDecision:
    """Evaluate full decision logic for protocol pass/fail."""
    lo, hi = acceptance_interval_hz(target_frequency_hz, uncertainty.expanded_uncertainty)

    within_interval = lo <= result.measured_frequency_hz <= hi
    controls_passed = all(bool(v) for v in result.controls.values())
    coherence_passed = result.coherence >= coherence_threshold
    entropy_passed = result.von_neumann_entropy <= entropy_max

    accepted = within_interval and controls_passed and coherence_passed and entropy_passed

    return AcceptanceDecision(
        accepted=accepted,
        within_frequency_interval=within_interval,
        controls_passed=controls_passed,
        coherence_passed=coherence_passed,
        entropy_passed=entropy_passed,
        interval_hz=(lo, hi),
    )
