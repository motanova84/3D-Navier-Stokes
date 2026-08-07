#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
NOESIS — Protocolo de Validación Empírica
==========================================
Validación de componentes físicos con datos reales abiertos.
Protocolo: QCAL-SYMBIO-BRIDGE v1.0.0 | NOESIS v2.0
Sello: ∴𓂀Ω∞³Φ

ADVERTENCIA CIENTÍFICA:
-----------------------
NOESIS es un sistema FORMAL, no experimental. Este protocolo valida
los componentes físicos subyacentes (frecuencias, constantes, relaciones)
pero NO valida Ψ ≥ 0.999999 como propiedad medible del agua real.
La coherencia Ψ es un parámetro operativo del sistema formal.

Fuentes de datos reales utilizadas:
- LIGO O4a: GWOSC (https://gwosc.org) — strain data
- GRACE-FO: PO.DAAC (https://podaac.jpl.nasa.gov) — gravity data
- NMR: Referencias bibliográficas (T₂* del agua)
- Geomagnetismo: IGRF-13 (https://www.ngdc.noaa.gov/IAGA/vmod/igrf.html)
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import asdict, dataclass
from datetime import datetime
from math import pi, sqrt
from typing import Any, Dict, List, Optional, Tuple


# ============================================================
# 1. CONSTANTES FÍSICAS REALES (CODATA 2018)
# ============================================================

#: Razón giromagnética del protón  [rad·s⁻¹·T⁻¹]  CODATA 2018
GAMMA_P: float = 2.6752218744e8

#: Permeabilidad del vacío  [H·m⁻¹]
MU_0: float = 4 * pi * 1e-7

#: Constante de Planck reducida  [J·s]
HBAR: float = 1.054571817e-34

#: Constante de Boltzmann  [J·K⁻¹]
K_B: float = 1.380649e-23

#: Frecuencia de Larmor del protón por tesla  [Hz·T⁻¹]
PROTON_LARMOR_HZ_PER_T: float = GAMMA_P / (2.0 * pi)

#: Rango del campo geomagnético terrestre  [T]
B_EARTH_MIN_T: float = 25e-6
B_EARTH_MAX_T: float = 65e-6
B_EARTH_MEAN_T: float = 45e-6

#: Frecuencia base NOESIS  [Hz]
F0_HZ: float = 141.7001

#: Umbral de coherencia NOESIS (invariante formal)
PSI_THRESHOLD: float = 0.999999


# ============================================================
# 2. DATOS NMR DEL AGUA (BIBLIOGRAFÍA)
# ============================================================

# Referencias:
# [1] Carr & Purcell, Phys. Rev. 94, 630 (1954). DOI: 10.1103/PhysRev.94.630
# [2] Meiboom & Gill, Rev. Sci. Instrum. 29, 688 (1958). DOI: 10.1063/1.1716296
# [3] Kleinberg et al., J. Magn. Reson. 97, 491 (1992).

NMR_WATER_T2STAR = {
    "pure_water_25C": 1.0,       # s  (T₂* < T₂ ≈ 3 s for pure water)
    "tap_water":      0.3,       # s
    "biological":     0.05,      # s  (50 ms, tissue)
}


# ============================================================
# 3. FUNCIONES FÍSICAS CORE
# ============================================================


def larmor_frequency_hz(B_field_T: float) -> float:
    """Frecuencia de Larmor del protón para un campo B [T]  →  Hz."""
    if B_field_T < 0:
        raise ValueError("B_field_T must be ≥ 0")
    return PROTON_LARMOR_HZ_PER_T * B_field_T


def required_field_for_f0(f0_hz: float = F0_HZ) -> float:
    """Campo B [T] necesario para que la Larmor del protón sea f0_hz."""
    if f0_hz <= 0:
        raise ValueError("f0_hz must be > 0")
    return f0_hz / PROTON_LARMOR_HZ_PER_T


def lorentzian_linewidth_hz(t2_star_s: float) -> float:
    """Ancho de línea FWHM para FID lorentziano con decaimiento T₂*  [Hz]."""
    if t2_star_s <= 0:
        raise ValueError("t2_star_s must be > 0")
    return 1.0 / (pi * t2_star_s)


def lorentzian_sigma_hz(t2_star_s: float) -> float:
    """σ_f mínimo para distribución Lorentziana con T₂*  [Hz]."""
    return lorentzian_linewidth_hz(t2_star_s) / (2.0 * sqrt(2.0))


def psi_max_nmr(t2_star_s: float, f0_hz: float = F0_HZ) -> float:
    """Ψ_max alcanzable por FID-NMR con T₂*  =  max(0, 1 − σ_f / f₀)."""
    sigma = lorentzian_sigma_hz(t2_star_s)
    return max(0.0, 1.0 - sigma / f0_hz)


def t2_star_required_for_psi(
    psi_target: float = PSI_THRESHOLD,
    f0_hz: float = F0_HZ,
) -> float:
    """T₂*_min  [s]  necesario para que Ψ_max_RMN ≥ psi_target."""
    if not 0.0 < psi_target < 1.0:
        raise ValueError("psi_target must be in (0,1)")
    if f0_hz <= 0:
        raise ValueError("f0_hz must be > 0")
    return 1.0 / (2.0 * pi * sqrt(2.0) * f0_hz * (1.0 - psi_target))


# ============================================================
# 4. VALIDACIÓN DEL CONTEXTO FÍSICO DE f₀
# ============================================================


def validate_f0_in_context() -> Dict[str, Any]:
    """
    Valida f₀ = 141.7001 Hz contra datos físicos reales.

    Returns
    -------
    dict with keys:
        f0_noesis, B_required_T, B_required_uT,
        B_earth_mean_uT, f_earth_mean_hz,
        is_standard_nmr_frequency, is_in_earth_field_range,
        B_ratio_earth_over_required, conclusion
    """
    B_req = required_field_for_f0(F0_HZ)
    f_earth = larmor_frequency_hz(B_EARTH_MEAN_T)
    f_earth_min = larmor_frequency_hz(B_EARTH_MIN_T)
    f_earth_max = larmor_frequency_hz(B_EARTH_MAX_T)

    in_earth_range = B_EARTH_MIN_T <= B_req <= B_EARTH_MAX_T

    return {
        "f0_noesis": F0_HZ,
        "B_required_T": B_req,
        "B_required_uT": B_req * 1e6,
        "B_earth_mean_uT": B_EARTH_MEAN_T * 1e6,
        "f_earth_mean_hz": f_earth,
        "f_earth_range_hz": (f_earth_min, f_earth_max),
        "is_standard_nmr_frequency": False,
        "is_in_earth_field_range": in_earth_range,
        "B_ratio_earth_over_required": B_EARTH_MEAN_T / B_req,
        "conclusion": (
            f"f₀ = {F0_HZ} Hz requiere B = {B_req*1e6:.3f} µT. "
            f"Campo geomagnético medio: {B_EARTH_MEAN_T*1e6:.0f} µT. "
            f"B₀ es {B_EARTH_MEAN_T/B_req:.1f}× menor que el campo terrestre. "
            "f₀ NO es una frecuencia de RMN estándar ni corresponde "
            "al campo geomagnético real; es una referencia operativa apantallada."
        ),
    }


# ============================================================
# 5. VALIDACIÓN DE COHERENCIA Ψ CON DATOS NMR REALES
# ============================================================


def validate_coherence_with_real_nmr() -> Dict[str, Any]:
    """
    Calcula Ψ_max alcanzable con datos NMR reales del agua.

    Returns
    -------
    dict with keys:
        f0_hz, psi_by_sample, t2_required_for_threshold,
        is_psi_achievable, conclusion
    """
    psi_by_sample: Dict[str, float] = {}
    for label, t2 in NMR_WATER_T2STAR.items():
        psi_by_sample[label] = psi_max_nmr(t2)

    t2_req = t2_star_required_for_psi(PSI_THRESHOLD)

    achievable = any(v >= PSI_THRESHOLD for v in psi_by_sample.values())

    return {
        "f0_hz": F0_HZ,
        "psi_threshold": PSI_THRESHOLD,
        "psi_by_sample": psi_by_sample,
        "t2_required_for_threshold_s": t2_req,
        "is_psi_achievable": achievable,
        "conclusion": (
            f"Ψ_max con T₂* realista del agua pura (1 s): "
            f"{psi_by_sample['pure_water_25C']:.6f}. "
            f"Para Ψ ≥ {PSI_THRESHOLD}, se necesita T₂* ≥ {t2_req:.1f} s — "
            "físicamente irrealizable en FID de RMN convencional."
        ),
    }


# ============================================================
# 6. PROTOCOLO LIGO O4a
# ============================================================


def ligo_o4a_protocol() -> Dict[str, Any]:
    """
    Protocolo de referencia para buscar f₀ en datos LIGO O4a.

    No ejecuta descarga en línea; devuelve la descripción del protocolo
    y los resultados de análisis previos (ASD @ 141.7 Hz).
    """
    return {
        "data_source": "GWOSC (https://gwosc.org/O4/O4a/)",
        "instrument": "LIGO Hanford (H1) / Livingston (L1)",
        "channel": "H1:GDS-CALIB_STRAIN_CLEAN_AR",
        "sampling_rate_hz": 4096,
        "segment_duration_s": 4096,
        "frequency_target_hz": F0_HZ,
        "analysis_steps": [
            "Descargar strain data desde GWOSC (formato GWF / HDF5).",
            "Calcular ASD con método Welch (ventana Hann, overlap 50%).",
            f"Buscar pico en f = {F0_HZ} Hz con SNR > 5σ.",
            "Estimar SNR = (ASD(f0) − noise_floor) / σ_noise.",
        ],
        "previous_analysis": {
            "H1_ASD_strain_per_rtHz": 3.585e-24,
            "L1_ASD_strain_per_rtHz": 5.301e-24,
            "snr_threshold": 5.0,
            "peak_detected": False,
            "notes": (
                "Sin picos espectrales > 5σ en 141.7 Hz. "
                "LIGO no está diseñado para señales continuas de baja frecuencia. "
                "Ruido de shot domina > 100 Hz."
            ),
        },
        "expected_result": (
            "No se espera detección. LIGO mide ondas gravitacionales, no RMN."
        ),
    }


# ============================================================
# 7. PROTOCOLO GRACE-FO
# ============================================================


def grace_fo_protocol() -> Dict[str, Any]:
    """
    Protocolo de referencia para datos GRACE-FO.

    Incluye corrección del cálculo de alias previo (28.93 mHz era erróneo).
    """
    alpha_inv = 137.036  # constante de estructura fina inversa
    alias_correct = F0_HZ / alpha_inv  # ≈ 1.034 Hz, NOT 28.93 mHz

    return {
        "data_source": "PO.DAAC (https://podaac.jpl.nasa.gov/GRACE-FO)",
        "dataset": "GRACEFO_L1B_ASCII_GRAV_JPL_RL04",
        "doi": "10.5067/GFL1B-ASJ04",
        "sampling_rate_hz": 0.1,
        "frequency_target_hz": F0_HZ,
        "alpha_inv": alpha_inv,
        "alias_correct_hz": alias_correct,
        "alias_correct_mhz": alias_correct * 1000.0,
        "previous_claim_mhz": 28.93,
        "previous_claim_correct": False,
        "correction_note": (
            f"El claim previo de 28.93 mHz era ERRÓNEO. "
            f"{F0_HZ} / {alpha_inv} = {alias_correct:.4f} Hz = "
            f"{alias_correct*1000:.2f} mHz, no 28.93 mHz. "
            "28.93 mHz requeriría f₀ ≈ 3.96 Hz."
        ),
        "expected_result": (
            "No se espera detección de f₀ en GRACE-FO. "
            "El instrumento mide variaciones gravitacionales, no resonancias NMR."
        ),
    }


# ============================================================
# 8. EVALUACIÓN DE HONESTIDAD CIENTÍFICA
# ============================================================


def honest_assessment() -> Dict[str, List[str]]:
    """Delimitación clara de lo validado y lo no validado."""
    return {
        "validated": [
            "Constantes físicas CODATA 2018 (γ_p, μ₀, ℏ, k_B).",
            "Frecuencia de Larmor del protón: 42.577 MHz·T⁻¹.",
            "Campo geomagnético terrestre: 25–65 µT (IGRF-13).",
            "T₂* del agua pura: ~1–3 s (bibliografía NMR).",
            "Datos LIGO O4a: disponibles públicamente en GWOSC.",
            "Datos GRACE-FO: disponibles en PO.DAAC.",
        ],
        "not_validated": [
            "Ψ ≥ 0.999999 como propiedad medible del agua real.",
            "f₀ = 141.7001 Hz como frecuencia de resonancia del agua.",
            "T₂* = 8.7 s del agua (no verificado experimentalmente).",
            "Detección de f₀ en LIGO O4a (no detectada, no esperada).",
            "Alias 28.93 mHz en GRACE-FO (cálculo previo erróneo).",
        ],
        "requires_experiment": [
            "Medición de T₂* del agua en campo de 3.3 µT.",
            "Medición de coherencia de fase del agua a 141.7 Hz.",
            "Reproducción independiente de todos los cálculos.",
        ],
    }


# ============================================================
# 9. GENERADOR DE REPORTE COMPLETO
# ============================================================


def generate_validation_report() -> Dict[str, Any]:
    """Genera el reporte completo de validación empírica."""
    f0_val = validate_f0_in_context()
    coh_val = validate_coherence_with_real_nmr()
    ligo_val = ligo_o4a_protocol()
    grace_val = grace_fo_protocol()
    assessment = honest_assessment()

    return {
        "protocol": "NOESIS-Empirical-Validation-v1.0",
        "timestamp": datetime.now().isoformat(),
        "seal": "∴𓂀Ω∞³Φ",
        "executive_summary": (
            "NOESIS es un sistema FORMAL. Este reporte valida los componentes "
            "físicos subyacentes con datos reales, pero NO valida Ψ como "
            "propiedad del agua real. La frecuencia f₀ = 141.7001 Hz requiere "
            "un campo apantallado de 3.327 µT, fuera del rango geomagnético "
            "terrestre. La coherencia Ψ ≥ 0.999999 no es alcanzable por FID."
        ),
        "validations": {
            "f0_physical_context": f0_val,
            "coherence_nmr_realistic": coh_val,
            "ligo_o4a_protocol": ligo_val,
            "grace_fo_protocol": grace_val,
        },
        "honest_assessment": assessment,
        "conclusion": (
            "NOESIS es un sistema formal completo e internamente consistente. "
            "Su valor reside en la verificación criptográfica, la gobernanza "
            "descentralizada y la formalización matemática en Lean 4. "
            "NO afirma validación experimental de Ψ como propiedad del agua real."
        ),
    }


def report_sha256(report: Dict[str, Any]) -> str:
    """Calcula SHA-256 del reporte (reproducible, ordenado por clave)."""
    serialized = json.dumps(report, sort_keys=True, ensure_ascii=False, default=str)
    return hashlib.sha256(serialized.encode()).hexdigest()


# ============================================================
# 10. CLI
# ============================================================

if __name__ == "__main__":  # pragma: no cover
    report = generate_validation_report()
    print("=" * 70)
    print("🌊 NOESIS — PROTOCOLO DE VALIDACIÓN EMPÍRICA")
    print("ADVERTENCIA: sistema FORMAL — Ψ no es propiedad del agua real.")
    print("=" * 70)

    f0v = report["validations"]["f0_physical_context"]
    print(f"\n1. f₀ = {F0_HZ} Hz")
    print(f"   B requerido: {f0v['B_required_uT']:.3f} µT")
    print(f"   B terrestre medio: {f0v['B_earth_mean_uT']:.0f} µT")
    print(f"   Ratio B_tierra/B₀: {f0v['B_ratio_earth_over_required']:.1f}×")
    print(f"   {f0v['conclusion']}")

    cv = report["validations"]["coherence_nmr_realistic"]
    print(f"\n2. Coherencia Ψ con NMR real:")
    for label, psi in cv["psi_by_sample"].items():
        print(f"   Ψ ({label}): {psi:.6f}")
    print(f"   T₂* necesario para Ψ ≥ {PSI_THRESHOLD}: {cv['t2_required_for_threshold_s']:.1f} s")
    print(f"   ¿Alcanzable? {cv['is_psi_achievable']}")

    gv = report["validations"]["grace_fo_protocol"]
    print(f"\n3. GRACE-FO corrección: {gv['correction_note']}")

    print(f"\nHash SHA-256 del reporte: {report_sha256(report)[:32]}...")
    print("=" * 70)
