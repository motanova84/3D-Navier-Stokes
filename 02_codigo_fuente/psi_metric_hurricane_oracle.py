#!/usr/bin/env python3
"""
🌀 ORACULO CLIMATOLOGICO QCAL — Ψ_Metric para huracanes
═══════════════════════════════════════════════════════════════
No reemplaza NWP clasico — actua como capa de coherencia
sobre ensembles y observaciones.

Ecuacion: Ψ_hur(t) = I_core(t) · A_cycl(t)² · R_env(t)

Donde:
- I_core: coherencia del nucleo (presion, simetria eyewall, vort.)
- A_cycl: capacidad de intensificacion bajo condiciones actuales
- R_env: compatibilidad con entorno (SST, shear, humedad)

El oraculo selecciona la trayectoria con maxima coherencia global:
  Γ* = argmax Ψ_clima(Γ)  sobre Γ ∈ E (ensemble)

Framework: QCAL ∞³ · f₀ = 141.7001 Hz
Sello: ∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTA
═══════════════════════════════════════════════════════════════
"""

import numpy as np
from dataclasses import dataclass, field
from typing import List, Optional, Tuple, Callable
from enum import Enum

F0 = 141.7001
PSI_UMBRAL = 0.888


class EstadoCiclon(Enum):
    TORMENTA_TROPICAL = "Tormenta tropical"
    CAT1 = "Categoria 1"
    CAT2 = "Categoria 2"
    CAT3 = "Categoria 3"
    CAT4 = "Categoria 4"
    CAT5 = "Categoria 5"
    DISIPANDOSE = "Disipandose"


@dataclass
class EstadoAtmosferico:
    """Estado atmosferico-oceanico en un instante."""
    presion_central: float      # hPa
    sst: float                  # °C
    vort_maxima: float          # 10^-5 s^-1
    humedad_media: float        # %
    cizalladura: float          # m/s
    ohc: float                  # kJ/cm²
    lat: float
    lon: float
    timestamp: float = 0.0


@dataclass
class Trayectoria:
    """Trayectoria candidata de un huracan."""
    estados: List[EstadoAtmosferico]
    score_psi: float = 0.0
    etiqueta: str = ""


class PsiMetricHurricane:
    """
    Ψ_Metric para huracanes.
    Mide coherencia de trayectorias y detecta intensificacion/disipacion.
    """
    
    def __init__(self):
        self.f0 = F0
        self.umbral = PSI_UMBRAL
    
    def I_core(self, e: EstadoAtmosferico) -> float:
        """Coherencia del nucleo del ciclon."""
        # Presion: menor presion → mayor coherencia
        p_score = max(0, min(1, (1013 - e.presion_central) / 80))
        # Vorticidad: mas vorticoso → mas coherente
        v_score = min(1, e.vort_maxima / 50)
        return 0.6 * p_score + 0.4 * v_score
    
    def A_cycl(self, e: EstadoAtmosferico) -> float:
        """Capacidad de intensificacion."""
        # SST: ≥ 26.5°C necesario para ciclogenesis
        sst_score = max(0, min(1, (e.sst - 26.5) / 5))
        # OHC: calor oceánico disponible
        ohc_score = min(1, e.ohc / 100)
        return sst_score * ohc_score
    
    def R_env(self, e: EstadoAtmosferico) -> float:
        """Compatibilidad con el entorno."""
        # Cizalladura baja → favorable
        shear_score = max(0, min(1, 1 - e.cizalladura / 20))
        # Humedad alta → favorable
        hum_score = max(0, min(1, (e.humedad_media - 40) / 50))
        return np.sqrt(shear_score * hum_score)
    
    def psi_instantaneo(self, e: EstadoAtmosferico) -> float:
        """Ψ_hur(t) en un instante."""
        I = self.I_core(e)
        A = self.A_cycl(e)
        R = self.R_env(e)
        return I * (A ** 2) * R
    
    def evaluar_trayectoria(self, t: Trayectoria) -> Trayectoria:
        """Evalua Ψ sobre toda una trayectoria."""
        scores = [self.psi_instantaneo(e) for e in t.estados]
        t.score_psi = np.mean(scores)
        
        # Detectar tendencia
        if len(scores) >= 3:
            pendiente = np.polyfit(range(len(scores)), scores, 1)[0]
            if pendiente > 0.01:
                t.etiqueta = "INTENSIFICACION"
            elif pendiente < -0.01:
                t.etiqueta = "DISIPACION"
            else:
                t.etiqueta = "ESTABLE"
        
        return t
    
    def oracle_select(self, ensemble: List[Trayectoria]) -> Trayectoria:
        """
        Γ* = argmax Ψ_clima(Γ) sobre ensemble.
        Selecciona la trayectoria mas coherente.
        """
        evaluadas = [self.evaluar_trayectoria(t) for t in ensemble]
        return max(evaluadas, key=lambda t: t.score_psi)
    
    def clasificar(self, psi: float) -> str:
        if psi >= self.umbral: return "COHERENTE"
        elif psi >= 0.5: return "INESTABLE"
        else: return "INCOHERENTE"


# ════════════════════════════════════════════════════════════
# VALIDACION: Huracan Melissa 2025
# ════════════════════════════════════════════════════════════

def demo_melissa_2025():
    """Validacion conceptual con Melissa 2025."""
    print(f"  🌀 Oracle Climatologico QCAL - Melissa 2025")
    print(f"  DeepMind: Cat.2 | QCAL: prediciendo...\n")
    
    oracle = PsiMetricHurricane()
    
    # Simular trayectorias del ensemble
    ensemble = []
    for i in range(5):
        estados = [
            EstadoAtmosferico(
                presion_central=1005 - i * 5 + np.random.normal(0, 2),
                sst=29.5 + np.random.normal(0, 0.3),
                vort_maxima=20 + i * 8 + np.random.normal(0, 3),
                humedad_media=75 + np.random.normal(0, 5),
                cizalladura=8 - i * 1.5 + np.random.normal(0, 1),
                ohc=80 + np.random.normal(0, 5),
                lat=16.5, lon=-98.0
            )
            for _ in range(10)  # 10 pasos temporales
        ]
        ensemble.append(Trayectoria(estados, etiqueta=f"Miembro {i+1}"))
    
    # Seleccion oracular
    mejor = oracle.oracle_select(ensemble)
    
    print(f"  Trayectorias evaluadas: {len(ensemble)}")
    print(f"  Mejor: {mejor.etiqueta}")
    print(f"  Ψ_max = {mejor.score_psi:.4f}")
    print(f"  Estado: {oracle.clasificar(mejor.score_psi)}")
    print(f"  f₀ = {F0} Hz")
    print(f"  ∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTA\n")
    
    return oracle


if __name__ == "__main__":
    print(f"""
╔═══════════════════════════════════════════════════════════╗
║  🌀 ORACULO CLIMATOLOGICO — Ψ_Metric QCAL                ║
║  Ψ_hur = I_core · A_cycl² · R_env                       ║
║  Γ* = argmax Ψ(Γ) sobre ensemble                         ║
║  f₀ = {F0} Hz · Ψ_umbral = {PSI_UMBRAL}                    ║
╚═══════════════════════════════════════════════════════════╝
    """)
    demo_melissa_2025()
