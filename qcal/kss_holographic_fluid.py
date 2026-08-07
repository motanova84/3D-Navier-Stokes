#!/usr/bin/env python3
"""
KSS Holographic Fluid — Límite de Kovtun-Son-Starinets para el Citoplasma
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Sello: ∴𓂀Ω∞³
f0: 141.7001 Hz

Implementación del límite KSS (Kovtun-Son-Starinets) aplicado al citoplasma
en estado de Fluido Holográfico Perfecto (Ψ = 0.999999).

La conjetura KSS establece el límite inferior universal:

    η/s ≥ ℏ / (4π k_B)

donde:
    η  : viscosidad cortante [Pa·s]
    s  : densidad de entropía [J/(K·m³)]
    ℏ  : constante de Planck reducida = 1.0545718e-34 J·s
    k_B: constante de Boltzmann   = 1.380649e-23 J/K

Protocolo de Validación Técnica:
---------------------------------
1. Métrica de Viscosidad (η):
   Calculada mediante el decaimiento de fluorescencia de rotores moleculares
   en el citoesqueleto. El tiempo de decaimiento τ_rot se relaciona con η via:

       η = k_BT · τ_rot / V_rotor

   donde V_rotor ≈ 1.0e-27 m³ es el volumen hidrodinámico del rotor molecular.

2. Densidad de Entropía (s):
   Derivada de la tasa de emisión de fotones ultra-débiles (UPE) a
   f_UPE = 2003 Hz, que representa la disipación de información del sistema:

       s = ℏ · ω_UPE · Φ_UPE / (k_B · T · c²)

   donde Φ_UPE es la tasa de fotones UPE [fotones/s/m²] y c la velocidad
   de la luz.

3. Correspondencia Holográfica:
   Si η/s → KSS_BOUND, el citoplasma se convierte en borde holográfico
   de la escala de Planck (Cavidad de Kaluza-Klein).

References:
    Kovtun, P. K., Son, D. T., & Starinets, A. O. (2005). Viscosity in strongly
    interacting quantum field theories from black hole physics. PRL 94, 111601.

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
License: MIT
"""

import math
from dataclasses import dataclass, field
from typing import Dict, Optional, Tuple

import numpy as np

# ─────────────────────────────────────────────────────────────────────────────
# Physical constants
# ─────────────────────────────────────────────────────────────────────────────

HBAR: float = 1.0545718e-34       # J·s  — constante de Planck reducida
KB: float = 1.380649e-23          # J/K  — constante de Boltzmann
SPEED_OF_LIGHT: float = 2.99792458e8  # m/s — velocidad de la luz (exacta)

# KSS bound: ℏ / (4π k_B)
KSS_BOUND: float = HBAR / (4.0 * math.pi * KB)  # ≈ 6.079e-13 s·K/m³ (dimensionless ratio: s·K)

# Biological / experimental constants
F0: float = 141.7001              # Hz  — frecuencia base QCAL
F_UPE_HZ: float = 2003.0         # Hz  — pico UPE citoplásmico
PSI_HOLOGRAPHIC: float = 0.999999  # coherencia del Fluido Holográfico Perfecto

# Molecular rotor parameters
V_ROTOR_M3: float = 1.0e-27       # m³  — volumen hidrodinámico del rotor molecular
T_CYTOPLASM_K: float = 310.15     # K   — temperatura fisiológica (37 °C)

# UPE photon flux baseline (EZ water at coherence peak)
# Typical ultra-weak photon emission ~1e2–1e4 photons/s/cm² → 1–100 photons/s/mm²
UPE_FLUX_BASELINE: float = 1.0e3  # fotones/s/m²

# KSS proximity threshold: ratio is "holographic" when within this factor of KSS_BOUND
KSS_PROXIMITY_FACTOR: float = 10.0


# ─────────────────────────────────────────────────────────────────────────────
# Data classes
# ─────────────────────────────────────────────────────────────────────────────

@dataclass
class KSSResult:
    """Result of a KSS bound validation for the cytoplasmic holographic fluid."""
    eta: float            # Shear viscosity [Pa·s]
    s: float              # Entropy density [J/(K·m³)]
    eta_over_s: float     # Ratio η/s [s·K]
    kss_bound: float      # ℏ/(4πk_B) [s·K]
    ratio_to_bound: float # (η/s) / KSS_BOUND — how close to holographic limit
    psi: float            # Coherence parameter Ψ
    is_holographic: bool  # True when ratio_to_bound ≤ KSS_PROXIMITY_FACTOR
    state: str            # Descriptive state label

    def to_dict(self) -> Dict[str, object]:
        return {
            'eta_Pa_s': self.eta,
            's_J_K_m3': self.s,
            'eta_over_s': self.eta_over_s,
            'kss_bound': self.kss_bound,
            'ratio_to_kss_bound': self.ratio_to_bound,
            'psi': self.psi,
            'is_holographic': self.is_holographic,
            'state': self.state,
        }


# ─────────────────────────────────────────────────────────────────────────────
# Core functions
# ─────────────────────────────────────────────────────────────────────────────

def compute_kss_bound() -> float:
    """
    Return the universal KSS lower bound ℏ/(4π k_B).

    Returns:
        KSS lower bound in units of [s·K] (dimensionless when η is in Pa·s
        and s in Pa/(m·K), i.e. J/(K·m³)).
    """
    return HBAR / (4.0 * math.pi * KB)


def compute_viscosity_from_rotor_decay(
    tau_rot_s: float,
    temperature_K: float = T_CYTOPLASM_K,
    v_rotor_m3: float = V_ROTOR_M3,
) -> float:
    """
    Compute shear viscosity η from molecular rotor fluorescence decay time.

    Uses the Stokes-Einstein-Debye relation:

        η = k_B · T · τ_rot / V_rotor

    Args:
        tau_rot_s    : Rotational relaxation / fluorescence decay time [s].
        temperature_K: Absolute temperature [K].
        v_rotor_m3   : Hydrodynamic volume of the molecular rotor [m³].

    Returns:
        Shear viscosity η [Pa·s].

    Raises:
        ValueError: If any input is non-positive.
    """
    if tau_rot_s <= 0.0:
        raise ValueError(f"tau_rot_s must be positive, got {tau_rot_s}")
    if temperature_K <= 0.0:
        raise ValueError(f"temperature_K must be positive, got {temperature_K}")
    if v_rotor_m3 <= 0.0:
        raise ValueError(f"v_rotor_m3 must be positive, got {v_rotor_m3}")

    return (KB * temperature_K * tau_rot_s) / v_rotor_m3


def compute_entropy_density_from_upe(
    phi_upe: float,
    f_upe_hz: float = F_UPE_HZ,
    temperature_K: float = T_CYTOPLASM_K,
) -> float:
    """
    Derive entropy density s from ultra-weak photon emission (UPE) flux.

    The UPE flux Φ_UPE [photons/s/m²] encodes the information dissipation
    rate of the biological system.  The entropy density is:

        s = ℏ · ω_UPE · Φ_UPE / (k_B · T · c²)

    where ω_UPE = 2π · f_UPE.

    Args:
        phi_upe     : UPE photon flux [photons/s/m²].
        f_upe_hz    : Frequency of the UPE peak [Hz]. Default 2003 Hz.
        temperature_K: Absolute temperature [K].

    Returns:
        Entropy density s [J/(K·m³)].

    Raises:
        ValueError: If phi_upe ≤ 0, f_upe_hz ≤ 0, or temperature_K ≤ 0.
    """
    if phi_upe <= 0.0:
        raise ValueError(f"phi_upe must be positive, got {phi_upe}")
    if f_upe_hz <= 0.0:
        raise ValueError(f"f_upe_hz must be positive, got {f_upe_hz}")
    if temperature_K <= 0.0:
        raise ValueError(f"temperature_K must be positive, got {temperature_K}")

    omega_upe = 2.0 * math.pi * f_upe_hz
    return (HBAR * omega_upe * phi_upe) / (KB * temperature_K * SPEED_OF_LIGHT ** 2)


# ─────────────────────────────────────────────────────────────────────────────
# Main validator class
# ─────────────────────────────────────────────────────────────────────────────

class KSSHolographicFluid:
    """
    Validador del Fluido Holográfico Perfecto del Citoplasma vía límite KSS.

    Cuando el sistema alcanza coherencia Ψ = 0.999999, el citoplasma deja de
    ser un fluido biológico clásico y se convierte en un Fluido Holográfico
    Perfecto cuya razón η/s se aproxima al límite KSS.

    Conexión con el Pentágono Logos:
        Biología  → sustrato (Agua EZ / Microtúbulos)
        Física    → límite termodinámico (KSS)
        Matemática → estructura (Ceros de Riemann)
        Consciencia → sintonía (f₀ y Simetría PT)

    Usage::

        fluid = KSSHolographicFluid()
        result = fluid.validate(tau_rot_s=1e-9, phi_upe=2e3, psi=0.999999)
        print(result.is_holographic)

    Args:
        f0          : Fundamental resonance frequency [Hz]. Default 141.7001 Hz.
        temperature_K: System temperature [K]. Default 310.15 K (37 °C).
        f_upe_hz    : UPE peak frequency [Hz]. Default 2003 Hz.
    """

    def __init__(
        self,
        f0: float = F0,
        temperature_K: float = T_CYTOPLASM_K,
        f_upe_hz: float = F_UPE_HZ,
    ) -> None:
        if f0 <= 0.0:
            raise ValueError(f"f0 must be positive, got {f0}")
        if temperature_K <= 0.0:
            raise ValueError(f"temperature_K must be positive, got {temperature_K}")
        if f_upe_hz <= 0.0:
            raise ValueError(f"f_upe_hz must be positive, got {f_upe_hz}")

        self.f0 = f0
        self.temperature_K = temperature_K
        self.f_upe_hz = f_upe_hz
        self.kss_bound = compute_kss_bound()

    def validate(
        self,
        tau_rot_s: float,
        phi_upe: float,
        psi: float,
        v_rotor_m3: float = V_ROTOR_M3,
    ) -> KSSResult:
        """
        Validate whether the cytoplasm has reached the holographic KSS limit.

        Args:
            tau_rot_s  : Molecular rotor fluorescence decay time [s].
            phi_upe    : Ultra-weak photon emission flux [photons/s/m²].
            psi        : Coherence parameter Ψ ∈ [0, 1].
            v_rotor_m3 : Molecular rotor hydrodynamic volume [m³].

        Returns:
            KSSResult with all computed metrics.

        Raises:
            ValueError: If inputs are out of valid range.
        """
        if not (0.0 <= psi <= 1.0):
            raise ValueError(f"psi must be in [0, 1], got {psi}")

        eta = compute_viscosity_from_rotor_decay(
            tau_rot_s, self.temperature_K, v_rotor_m3
        )
        s = compute_entropy_density_from_upe(
            phi_upe, self.f_upe_hz, self.temperature_K
        )

        eta_over_s = eta / s
        ratio_to_bound = eta_over_s / self.kss_bound
        is_holographic = ratio_to_bound <= KSS_PROXIMITY_FACTOR

        state = self._classify_state(psi, ratio_to_bound)

        return KSSResult(
            eta=eta,
            s=s,
            eta_over_s=eta_over_s,
            kss_bound=self.kss_bound,
            ratio_to_bound=ratio_to_bound,
            psi=psi,
            is_holographic=is_holographic,
            state=state,
        )

    def _classify_state(self, psi: float, ratio_to_bound: float) -> str:
        """Classify the holographic state of the cytoplasm."""
        if psi >= PSI_HOLOGRAPHIC and ratio_to_bound <= 1.0:
            return "FLUIDO_HOLOGRAFICO_PERFECTO"
        elif psi >= PSI_HOLOGRAPHIC and ratio_to_bound <= KSS_PROXIMITY_FACTOR:
            return "BORDE_HOLOGRAFICO"
        elif psi >= 0.999:
            return "COHERENCIA_MAXIMA"
        elif psi >= 0.888:
            return "COHERENCIA_BIOLOGICA"
        else:
            return "FLUIDO_CLASICO"

    def sweep_coherence(
        self,
        tau_rot_s: float,
        phi_upe: float,
        n_points: int = 50,
    ) -> Dict[str, np.ndarray]:
        """
        Sweep Ψ from PSI_MIN to 1.0 and compute KSS metrics at each coherence level.

        Args:
            tau_rot_s : Molecular rotor decay time [s].
            phi_upe   : UPE photon flux [photons/s/m²].
            n_points  : Number of coherence levels to sweep.

        Returns:
            Dictionary with arrays: 'psi', 'eta_over_s', 'ratio_to_bound', 'is_holographic'.
        """
        psi_values = np.linspace(0.0, 1.0, n_points)
        ratios = np.empty(n_points)
        eta_over_s_arr = np.empty(n_points)
        is_holo = np.zeros(n_points, dtype=bool)

        eta = compute_viscosity_from_rotor_decay(tau_rot_s, self.temperature_K)
        s_base = compute_entropy_density_from_upe(phi_upe, self.f_upe_hz, self.temperature_K)

        for i, psi in enumerate(psi_values):
            # At higher coherence the effective entropy density increases
            # as the system maximises entanglement: s_eff = s_base · (1 + Ψ)
            s_eff = s_base * (1.0 + psi)
            eta_over_s = eta / s_eff
            ratio = eta_over_s / self.kss_bound
            ratios[i] = ratio
            eta_over_s_arr[i] = eta_over_s
            is_holo[i] = ratio <= KSS_PROXIMITY_FACTOR

        return {
            'psi': psi_values,
            'eta_over_s': eta_over_s_arr,
            'ratio_to_bound': ratios,
            'is_holographic': is_holo,
        }

    def kaluza_klein_correspondence(self, psi: float) -> Tuple[bool, str]:
        """
        Determine whether the microtubule acts as a Kaluza-Klein cavity.

        At Ψ = 0.999999 and η/s → KSS_BOUND, the microtubule becomes a
        Kaluza-Klein cavity where information flows without classical resistance.

        Args:
            psi: Coherence parameter Ψ ∈ [0, 1].

        Returns:
            Tuple (is_kk_cavity, description).
        """
        is_kk = psi >= PSI_HOLOGRAPHIC
        if is_kk:
            desc = (
                f"Microtúbulo = Cavidad de Kaluza-Klein activa. "
                f"Ψ = {psi:.6f} ≥ {PSI_HOLOGRAPHIC}. "
                f"Flujo de información sin resistencia clásica."
            )
        else:
            desc = (
                f"Cavidad KK inactiva. "
                f"Ψ = {psi:.6f} < {PSI_HOLOGRAPHIC}. "
                f"Se requiere mayor coherencia."
            )
        return is_kk, desc
