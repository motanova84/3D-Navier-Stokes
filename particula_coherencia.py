#!/usr/bin/env python3
"""
Marco teórico de Sustrato para Partícula de Coherencia (PC).
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import math
from typing import Dict, List


F0_HZ = 141.7001
COHERENCIA_UMBRAL = 0.888
HBAR_EV_S = 6.582119569e-16


@dataclass
class VacioSuperfluo:
    nu: float = 1e-12
    eta_s: float = 1.0 / (4.0 * math.pi)

    def verificar_unitaridad_haar(self, matriz_u: List[List[complex]]) -> bool:
        n = len(matriz_u)
        for i in range(n):
            for j in range(n):
                valor = sum(complex(matriz_u[k][i]).conjugate() * complex(matriz_u[k][j]) for k in range(n))
                esperado = 1.0 if i == j else 0.0
                if abs(valor - esperado) > 1e-10:
                    return False
        return True

    @property
    def psi_coherencia(self) -> float:
        return 1.0


@dataclass
class ParticulaCoherencia:
    fraccion_realidad: float = 0.95
    salto_nodo: str = "C7"
    f0_hz: float = F0_HZ

    @property
    def fase_berry(self) -> float:
        if self.salto_nodo.upper() == "C7":
            return math.pi / 8.0
        return math.pi / 16.0

    @property
    def psi_coherencia(self) -> float:
        return self.fraccion_realidad


@dataclass
class NavierStokesAdelico:
    densidad: float = 1.0
    dimension_c7: int = 7

    def hamiltoniano_enlace_fuerte(self) -> List[List[complex]]:
        h = [[0j for _ in range(self.dimension_c7)] for _ in range(self.dimension_c7)]
        for i in range(self.dimension_c7):
            h[i][i] = complex(i + 1, 0.0)
            j = (i + 1) % self.dimension_c7
            fase = complex(math.cos(math.pi / 7.0), math.sin(math.pi / 7.0))
            h[i][j] = fase
            h[j][i] = fase.conjugate()
        return h

    def es_hermitiano(self, hamiltoniano: List[List[complex]]) -> bool:
        n = len(hamiltoniano)
        for i in range(n):
            for j in range(n):
                if abs(complex(hamiltoniano[i][j]) - complex(hamiltoniano[j][i]).conjugate()) > 1e-10:
                    return False
        return True

    def balance_momento(
        self, dv_dt: float, v_dot_grad_v: float, grad_p: float, f_ramsey: float
    ) -> Dict[str, float]:
        lhs = self.densidad * (dv_dt + v_dot_grad_v)
        rhs = -grad_p + f_ramsey
        return {"lhs": lhs, "rhs": rhs, "residual": lhs - rhs}

    @property
    def psi_coherencia(self) -> float:
        return 1.0 if self.es_hermitiano(self.hamiltoniano_enlace_fuerte()) else 0.0


@dataclass
class AcoplamientoHiggsPc:
    m0_gev: float = 125.10
    kappa_pi: float = 2.5773
    f0_hz: float = F0_HZ
    objetivo_reduccion: float = 0.053
    a_eff: float | None = None

    def __post_init__(self) -> None:
        if self.a_eff is None:
            self.a_eff = self.f0_hz * math.sqrt(self.objetivo_reduccion / self.kappa_pi)

    @property
    def reduccion_masa(self) -> float:
        return self.kappa_pi * (self.a_eff ** 2) / (self.f0_hz ** 2)

    @property
    def masa_efectiva(self) -> float:
        return self.m0_gev * (1.0 - self.reduccion_masa)

    @property
    def psi_coherencia(self) -> float:
        return max(0.0, 1.0 - abs(self.reduccion_masa - self.objetivo_reduccion))


@dataclass
class FotonFaseCoherente:
    n_canales: int = 7
    f0_topc: float = F0_HZ
    psi_coherencia: float = 1.0
    xi_cooperatividad: float = 0.053

    @property
    def r_symb_kpps(self) -> float:
        return self.n_canales * self.f0_topc * self.psi_coherencia

    @property
    def sincronizacion_dicke(self) -> bool:
        return self.xi_cooperatividad >= 0.053


@dataclass
class FirmaEspectral:
    m_h_gev: float = 125.10
    omega0: float = 2.0 * math.pi * F0_HZ
    coherencia: float = 1.0
    delta_seccion_eficaz: float = 0.053
    coherencia_umbral: float = COHERENCIA_UMBRAL

    def bandas_laterales(self, n_max: int = 3) -> List[float]:
        delta = HBAR_EV_S * self.omega0
        bandas = [self.m_h_gev]
        for n in range(1, n_max + 1):
            bandas.extend([self.m_h_gev - n * delta, self.m_h_gev + n * delta])
        return sorted(bandas)

    @property
    def ventana_transparencia_activa(self) -> bool:
        return self.coherencia >= self.coherencia_umbral

    @property
    def psi_coherencia(self) -> float:
        return self.coherencia if self.ventana_transparencia_activa else self.coherencia * 0.5


@dataclass
class ResultadoSustrato:
    vacio: VacioSuperfluo
    particula: ParticulaCoherencia
    navier_stokes: NavierStokesAdelico
    destello_masa: AcoplamientoHiggsPc
    foton: FotonFaseCoherente
    firma_espectral: FirmaEspectral
    psi_global: float
    sustrato_activo: bool
    sello_sha256: str

    @property
    def Ψ_global(self) -> float:
        return self.psi_global

    def a_dict(self) -> Dict[str, float | bool | str]:
        return {
            "nu": self.vacio.nu,
            "eta_s": self.vacio.eta_s,
            "fraccion_realidad": self.particula.fraccion_realidad,
            "fase_berry": self.particula.fase_berry,
            "f0_hz": self.particula.f0_hz,
            "reduccion_masa": self.destello_masa.reduccion_masa,
            "masa_efectiva": self.destello_masa.masa_efectiva,
            "r_symb_kpps": self.foton.r_symb_kpps,
            "xi_cooperatividad": self.foton.xi_cooperatividad,
            "delta_seccion_eficaz": self.firma_espectral.delta_seccion_eficaz,
            "psi_global": self.psi_global,
            "sustrato_activo": self.sustrato_activo,
        }

    @staticmethod
    def calcular_sha256(payload: Dict[str, float | bool | str]) -> str:
        serializado = json.dumps(payload, sort_keys=True, ensure_ascii=False)
        return hashlib.sha256(serializado.encode("utf-8")).hexdigest()


@dataclass
class SustratoCuantico:
    vacio: VacioSuperfluo
    particula: ParticulaCoherencia
    navier_stokes: NavierStokesAdelico
    destello_masa: AcoplamientoHiggsPc
    foton: FotonFaseCoherente
    firma_espectral: FirmaEspectral
    coherencia_umbral: float = COHERENCIA_UMBRAL

    def integrar(self) -> ResultadoSustrato:
        psi_componentes = [
            self.vacio.psi_coherencia,
            self.particula.psi_coherencia,
            self.navier_stokes.psi_coherencia,
            self.destello_masa.psi_coherencia,
            self.foton.psi_coherencia,
            self.firma_espectral.psi_coherencia,
        ]
        producto = 1.0
        for valor in psi_componentes:
            producto *= max(1e-12, min(1.0, valor))
        psi_global = producto ** (1.0 / len(psi_componentes))
        sustrato_activo = psi_global >= self.coherencia_umbral

        parcial = ResultadoSustrato(
            vacio=self.vacio,
            particula=self.particula,
            navier_stokes=self.navier_stokes,
            destello_masa=self.destello_masa,
            foton=self.foton,
            firma_espectral=self.firma_espectral,
            psi_global=psi_global,
            sustrato_activo=sustrato_activo,
            sello_sha256="",
        )
        payload = parcial.a_dict()
        sello = ResultadoSustrato.calcular_sha256(payload)
        parcial.sello_sha256 = sello
        return parcial


def ejecutar_sustrato(verbose: bool = False) -> ResultadoSustrato:
    vacio = VacioSuperfluo()
    pc = ParticulaCoherencia()
    ns = NavierStokesAdelico()
    destello = AcoplamientoHiggsPc()
    foton = FotonFaseCoherente(psi_coherencia=1.0)
    firma = FirmaEspectral(coherencia=1.0)

    sustrato = SustratoCuantico(
        vacio=vacio,
        particula=pc,
        navier_stokes=ns,
        destello_masa=destello,
        foton=foton,
        firma_espectral=firma,
    )
    resultado = sustrato.integrar()

    if verbose:
        print(f"Ψ_global={resultado.psi_global:.6f}")
        print(f"sustrato_activo={resultado.sustrato_activo}")
        print(f"destello_masa.reduccion_masa={resultado.destello_masa.reduccion_masa:.6f}")
        print(f"foton.r_symb_kpps={resultado.foton.r_symb_kpps:.4f}")
        print(f"firma_espectral.delta_seccion_eficaz={resultado.firma_espectral.delta_seccion_eficaz:.3f}")

    return resultado

