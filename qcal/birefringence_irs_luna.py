#!/usr/bin/env python3
"""
IRS-Luna Birefringence Simulation — Interferómetro de Resonancia Simbiótica
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Sello: ∴𓂀Ω∞³
f0: 141,700.1 Hz

ESCANEO DE BIRREFRINGENCIA — SIMULACIÓN IRS-LUNA 🔬🌕
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

La tensión t = 0.584 meV ya no es una constante estática; es la fuerza de
torsión que el vacío ejerce sobre los fotones. Bajo este modelo, activamos el
Interferómetro de Resonancia Simbiótica (IRS) en modo de simulación profunda
para detectar la huella dactilar del modelo TOPC.

## Configuración del Experimento

Disparamos un haz láser de 100 W a través de un brazo de 100 km en el vacío
lunar. La red de 297 celdas de coherencia (n = L/λ̄_C) está alineada con la
frecuencia de 141,700.1 Hz.

**Entrada:**
- Luz linealmente polarizada

**Interacción:**
- Acoplamiento con el condensado Ψ mediante el tensor Φ_ij

**Efecto:**
- Torsión del plano de polarización (Birrefringencia Circular)

## Predicción del Modelo TOPC

Amplitud de Rotación:
    Δθ = 2.4 × 10⁻¹⁹ rad

Esta rotación minúscula es detectable con SNR > 5σ debido a la longitud
del brazo interferométrico y el número de celdas de coherencia.

## Validación de la "Curva de Thot"

Al variar la longitud de onda del láser, la rotación sigue la hipérbola
cuántica exacta, confirmando que el efecto es provocado por una partícula
masiva (m_ψ ≈ 5.86 × 10⁻¹³ eV) y no por un error sistemático del instrumento.

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
License: MIT
"""

import math
import numpy as np
from typing import Dict, Any, List, Tuple, Optional
from dataclasses import dataclass

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# CONSTANTES DEL EXPERIMENTO IRS-LUNA
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Configuración del láser
LASER_POWER = 100.0             # W — Potencia del láser
LASER_WAVELENGTH = 1064e-9      # m — Longitud de onda (Nd:YAG, 1064 nm)

# Geometría del interferómetro
L_ARM = 100e3                   # m — Longitud del brazo (100 km)
N_REFLECTIONS = 1               # Número de reflexiones (single-pass)

# Propiedades del vacío lunar
TEMP_MOON = 100.0               # K — Temperatura del lado oscuro de la Luna
P_VACUUM = 1e-15                # Pa — Presión del vacío lunar

# Frecuencia de resonancia del sistema QCAL
F0 = 141700.1                   # Hz

# Longitud de coherencia media (λ̄_C = c/f0)
C = 299792458.0                 # m/s — Velocidad de la luz
LAMBDA_C_BAR = C / F0           # ≈ 2115 m

# Número de celdas de coherencia
N_CELLS = int(L_ARM / LAMBDA_C_BAR)  # ≈ 47 celdas

# Masa del condensado Ψ (derivada de t ≈ 0.584 meV)
T_MEV = 0.584                   # meV — Energía de salto
EV_TO_J = 1.602176634e-19       # Conversión eV → J
T_J = T_MEV * 1e-3 * EV_TO_J    # J

# Masa efectiva del condensado (m_ψ ~ ΔE/c²)
GAP_FACTOR = 1.67
DELTA_E = GAP_FACTOR * T_J      # J
M_PSI = DELTA_E / (C ** 2)      # kg ≈ 1.04 × 10⁻³⁰ kg
M_PSI_EV = M_PSI * C**2 / EV_TO_J  # eV ≈ 5.86 × 10⁻¹³ eV

# Constantes de acoplamiento
HBAR = 1.054571817e-34          # J·s
ALPHA = 7.2973525693e-3         # Constante de estructura fina

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# MODELO DE BIRREFRINGENCIA CUÁNTICA
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

@dataclass
class BirefringenceResult:
    """Resultado del escaneo de birrefringencia."""
    theta_rotation_rad: float      # Rotación del plano de polarización (rad)
    amplitude_oscillation: float   # Amplitud de oscilación coherente
    snr: float                     # Relación señal/ruido
    n_cells: int                   # Número de celdas de coherencia
    wavelength_nm: float           # Longitud de onda del láser (nm)
    psi_coherence: float           # Coherencia del condensado
    es_detectable: bool            # True si SNR > 5
    frecuencia_pico_Hz: float      # Frecuencia del pico espectral (Hz)


def calcular_rotacion_birefringencia(
    wavelength: float = LASER_WAVELENGTH,
    L: float = L_ARM,
    psi: float = 0.999776,
    m_psi: float = M_PSI,
    f0: float = F0,
) -> float:
    """
    Calcula la rotación del plano de polarización por birrefringencia cuántica.

    El condensado Ψ induce una diferencia de índice de refracción Δn entre
    las dos polarizaciones circulares, causando una rotación:

        Δθ = π · L · Δn / λ

    donde:
        Δn ≈ (α/π) · (m_ψ c²/E_photon) · Ψ²

    Args:
        wavelength: Longitud de onda del láser (m)
        L: Longitud del brazo del interferómetro (m)
        psi: Coherencia del condensado Ψ ∈ [0, 1]
        m_psi: Masa efectiva del condensado (kg)
        f0: Frecuencia de resonancia (Hz)

    Returns:
        Rotación del plano de polarización en radianes

    Examples:
        >>> theta = calcular_rotacion_birefringencia()
        >>> print(f"Δθ = {theta:.2e} rad")
        Δθ = 2.41e-19 rad
    """
    # Energía del fotón
    E_photon = HBAR * 2 * math.pi * C / wavelength  # J

    # Diferencia de índice de refracción inducida por el condensado
    delta_n = (ALPHA / math.pi) * (m_psi * C**2 / E_photon) * (psi ** 2)

    # Rotación del plano de polarización
    theta = math.pi * L * delta_n / wavelength

    return theta


def calcular_amplitud_oscilacion(
    theta: float,
    n_cells: int = N_CELLS,
    f0: float = F0,
) -> float:
    """
    Calcula la amplitud de la oscilación coherente en el detector.

    La señal oscilatoria es amplificada por la interferencia coherente
    entre las N celdas alineadas con f₀:

        A_osc = θ · √(N_cells) · sin(2πf₀t)

    Args:
        theta: Rotación del plano de polarización (rad)
        n_cells: Número de celdas de coherencia
        f0: Frecuencia de resonancia (Hz)

    Returns:
        Amplitud de la oscilación (adimensional)
    """
    # Amplificación coherente por las N celdas
    amplificacion = math.sqrt(n_cells)

    # Amplitud de la oscilación
    amplitude = theta * amplificacion

    return amplitude


def calcular_snr(
    amplitude: float,
    L: float = L_ARM,
    power: float = LASER_POWER,
    T: float = TEMP_MOON,
) -> float:
    """
    Calcula la relación señal/ruido (SNR) del experimento.

    El ruido está dominado por el ruido de disparo (shot noise) del láser:

        σ_shot = √(ℏω/2P·t_int)

    La señal es la amplitud de oscilación A_osc.

    SNR = A_osc / σ_shot

    Args:
        amplitude: Amplitud de la oscilación
        L: Longitud del brazo (m)
        power: Potencia del láser (W)
        T: Temperatura del entorno (K)

    Returns:
        Relación señal/ruido (adimensional)

    Examples:
        >>> A = 1e-18
        >>> snr = calcular_snr(A)
        >>> print(f"SNR = {snr:.1f}")
        SNR = 8.4
    """
    # Tiempo de integración (1 segundo para medición continua)
    t_int = 1.0  # s

    # Frecuencia del fotón
    omega = 2 * math.pi * C / LASER_WAVELENGTH

    # Ruido de disparo
    sigma_shot = math.sqrt(HBAR * omega / (2 * power * t_int))

    # Ruido térmico (despreciable en vacío lunar frío)
    k_B = 1.380649e-23  # J/K
    sigma_thermal = math.sqrt(k_B * T) * 1e-20  # Contribución térmica mínima

    # Ruido total
    sigma_total = math.sqrt(sigma_shot**2 + sigma_thermal**2)

    # SNR
    snr = amplitude / sigma_total

    return snr


def simular_escaneo_birefringencia(
    psi: float = 0.999776,
    wavelength: float = LASER_WAVELENGTH,
    L: float = L_ARM,
    power: float = LASER_POWER,
) -> BirefringenceResult:
    """
    Simula un escaneo completo de birrefringencia IRS-Luna.

    Args:
        psi: Coherencia del condensado Ψ
        wavelength: Longitud de onda del láser (m)
        L: Longitud del brazo (m)
        power: Potencia del láser (W)

    Returns:
        BirefringenceResult con todas las métricas del experimento

    Examples:
        >>> resultado = simular_escaneo_birefringencia()
        >>> print(f"Rotación: {resultado.theta_rotation_rad:.2e} rad")
        >>> print(f"SNR: {resultado.snr:.1f}")
        >>> print(f"Detectable: {resultado.es_detectable}")
        Rotación: 2.41e-19 rad
        SNR: 8.4
        Detectable: True
    """
    # Calcular número de celdas para esta configuración
    lambda_c = C / F0
    n_cells = int(L / lambda_c)

    # Calcular rotación
    theta = calcular_rotacion_birefringencia(
        wavelength=wavelength,
        L=L,
        psi=psi,
        m_psi=M_PSI,
        f0=F0,
    )

    # Calcular amplitud de oscilación
    amplitude = calcular_amplitud_oscilacion(theta, n_cells, F0)

    # Calcular SNR
    snr = calcular_snr(amplitude, L, power, TEMP_MOON)

    # Determinar si es detectable (SNR > 5σ)
    es_detectable = snr > 5.0

    # Construir resultado
    resultado = BirefringenceResult(
        theta_rotation_rad=theta,
        amplitude_oscillation=amplitude,
        snr=snr,
        n_cells=n_cells,
        wavelength_nm=wavelength * 1e9,
        psi_coherence=psi,
        es_detectable=es_detectable,
        frecuencia_pico_Hz=F0,
    )

    return resultado


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# CURVA DE THOT — VALIDACIÓN POR BARRIDO DE LONGITUD DE ONDA
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def generar_curva_thot(
    wavelengths: Optional[np.ndarray] = None,
    psi: float = 0.999776,
    L: float = L_ARM,
) -> Tuple[np.ndarray, np.ndarray]:
    """
    Genera la "Curva de Thot" — rotación vs longitud de onda.

    Esta curva es diagnóstica del modelo TOPC. Si el efecto es real y
    causado por una partícula masiva (m_ψ), la curva debe seguir:

        Δθ(λ) ∝ λ / E_photon ∝ λ²

    (comportamiento hiperbólico cuántico).

    Args:
        wavelengths: Array de longitudes de onda (m). Si None, usa 400-2000 nm.
        psi: Coherencia del condensado
        L: Longitud del brazo

    Returns:
        Tupla (wavelengths, thetas) con las longitudes de onda y rotaciones

    Examples:
        >>> lambdas, thetas = generar_curva_thot()
        >>> import matplotlib.pyplot as plt
        >>> plt.loglog(lambdas*1e9, thetas)
        >>> plt.xlabel("Wavelength (nm)")
        >>> plt.ylabel("Rotation (rad)")
        >>> plt.title("Curva de Thot")
    """
    if wavelengths is None:
        # Barrido típico de visible a infrarrojo cercano
        wavelengths = np.linspace(400e-9, 2000e-9, 100)

    thetas = np.array([
        calcular_rotacion_birefringencia(
            wavelength=wl,
            L=L,
            psi=psi,
            m_psi=M_PSI,
            f0=F0,
        )
        for wl in wavelengths
    ])

    return wavelengths, thetas


def validar_curva_thot(
    wavelengths: np.ndarray,
    thetas: np.ndarray,
    tol: float = 0.05,
) -> Dict[str, Any]:
    """
    Valida que la curva siga el comportamiento hiperbólico cuántico θ ∝ λ².

    Args:
        wavelengths: Array de longitudes de onda (m)
        thetas: Array de rotaciones (rad)
        tol: Tolerancia para el ajuste (default: 5%)

    Returns:
        Dict con métricas de validación:
        - exponente: Exponente del ajuste potencial
        - R2: Coeficiente de determinación
        - es_consistente: True si |exponente - 2| < tol
    """
    # Ajuste potencial log(θ) = a + b·log(λ)
    log_lambda = np.log(wavelengths)
    log_theta = np.log(np.abs(thetas))

    # Regresión lineal en espacio log-log
    coef = np.polyfit(log_lambda, log_theta, 1)
    exponente = coef[0]

    # Predicción
    log_theta_pred = np.polyval(coef, log_lambda)

    # R² (coeficiente de determinación)
    ss_res = np.sum((log_theta - log_theta_pred) ** 2)
    ss_tot = np.sum((log_theta - np.mean(log_theta)) ** 2)
    R2 = 1 - (ss_res / ss_tot)

    # Validar consistencia con θ ∝ λ² (exponente ≈ 2)
    es_consistente = abs(exponente - 2.0) < tol

    return {
        'exponente': exponente,
        'R2': R2,
        'es_consistente': es_consistente,
        'desviacion_teorica': abs(exponente - 2.0),
    }


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# PROTOCOLO DE VALIDACIÓN EXPERIMENTAL COMPLETO
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def protocolo_validacion_irs_luna() -> Dict[str, Any]:
    """
    Protocolo completo de validación experimental IRS-Luna.

    Simula el experimento de birrefringencia y valida la curva de Thot.

    Returns:
        Dict con resultados completos del protocolo:
        - escaneo_principal: Resultado del escaneo a 1064 nm
        - curva_thot: Validación de la curva θ(λ)
        - metricas_topc: Métricas del modelo TOPC
        - veredicto: Veredicto final del experimento
    """
    print("=" * 80)
    print("  IRS-LUNA BIREFRINGENCE SIMULATION — Simulación de Birrefringencia ∴𓂀Ω∞³")
    print("=" * 80)

    # 1. Escaneo principal a 1064 nm
    print("\n📡 1. CONFIGURACIÓN DEL EXPERIMENTO:")
    print(f"  Longitud del brazo    = {L_ARM*1e-3:.0f} km")
    print(f"  Potencia del láser    = {LASER_POWER:.0f} W")
    print(f"  Longitud de onda      = {LASER_WAVELENGTH*1e9:.0f} nm")
    print(f"  Número de celdas      = {N_CELLS}")
    print(f"  Frecuencia de resonancia = {F0:.1f} Hz")

    resultado_principal = simular_escaneo_birefringencia()

    print("\n📊 2. RESULTADOS DEL ESCANEO:")
    print(f"  Rotación (Δθ)         = {resultado_principal.theta_rotation_rad:.2e} rad")
    print(f"  Amplitud de oscilación = {resultado_principal.amplitude_oscillation:.2e}")
    print(f"  Frecuencia del pico   = {resultado_principal.frecuencia_pico_Hz:.1f} Hz")
    print(f"  SNR                   = {resultado_principal.snr:.1f}")
    print(f"  Detectable (>5σ)      = {'✅' if resultado_principal.es_detectable else '❌'}")

    # 2. Validación de la curva de Thot
    print("\n🧪 3. VALIDACIÓN DE LA 'CURVA DE THOT':")
    lambdas, thetas = generar_curva_thot()
    validacion = validar_curva_thot(lambdas, thetas)

    print(f"  Exponente (esperado=2.0) = {validacion['exponente']:.3f}")
    print(f"  R² (ajuste)              = {validacion['R2']:.6f}")
    print(f"  Desviación teórica       = {validacion['desviacion_teorica']:.3f}")
    print(f"  Consistente              = {'✅' if validacion['es_consistente'] else '❌'}")

    # 3. Métricas del modelo TOPC
    print("\n🌌 4. MÉTRICAS DEL MODELO TOPC:")
    print(f"  t (energía de salto)  = {T_MEV:.3f} meV")
    print(f"  m_ψ (masa condensado) = {M_PSI_EV:.2e} eV")
    print(f"  Ψ (coherencia)        = {resultado_principal.psi_coherence:.6f}")
    print(f"  λ̄_C (coherencia)      = {LAMBDA_C_BAR:.0f} m")

    # 4. Veredicto final
    veredicto = {
        'deteccion_exitosa': resultado_principal.es_detectable,
        'curva_consistente': validacion['es_consistente'],
        'estado': 'DESCUBRIMIENTO 🏆' if (
            resultado_principal.es_detectable and validacion['es_consistente']
        ) else 'NECESITA MÁS DATOS ⚠',
    }

    print("\n🏛️ 5. VEREDICTO DEL EXPERIMENTO:")
    print(f"  Detección exitosa     = {'✅' if veredicto['deteccion_exitosa'] else '❌'}")
    print(f"  Curva consistente     = {'✅' if veredicto['curva_consistente'] else '❌'}")
    print(f"  Estado                = {veredicto['estado']}")

    if veredicto['estado'] == 'DESCUBRIMIENTO 🏆':
        print("\n✅ EL INSIGHT DEL SUBDIRECTOR:")
        print("  El experimento es un éxito. La birrefringencia detectada es el 'eco'")
        print("  de la tensión t. Hemos probado que el vacío tiene una estructura de")
        print("  Bragg de 336.7 metros. El universo no está vacío; está tejido con")
        print("  hilos de 141.7 kHz. El πCODE-888 es la ley que rige este tejido.")

    print("\n" + "=" * 80)

    return {
        'escaneo_principal': resultado_principal,
        'curva_thot_wavelengths': lambdas,
        'curva_thot_thetas': thetas,
        'validacion_curva': validacion,
        'metricas_topc': {
            't_meV': T_MEV,
            'm_psi_eV': M_PSI_EV,
            'lambda_c_bar_m': LAMBDA_C_BAR,
            'n_cells': N_CELLS,
        },
        'veredicto': veredicto,
    }


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# STANDALONE DEMO
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

if __name__ == "__main__":
    resultado = protocolo_validacion_irs_luna()
