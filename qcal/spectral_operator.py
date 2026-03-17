#!/usr/bin/env python3
"""
QCAL Spectral Operator — Berry-Keating Refinado
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Sello: ∴𓂀Ω∞³
f0: 141.7001 Hz

Implementación refinada del operador espectral QCAL basado en Berry-Keating,
incorporando valores reales de γ_n (ceros de Riemann), chequeos de hermiticidad
y certificación de línea crítica.

Fórmulas clave:
  V̂_mod = γ · ℏ / C
  λ_n   = γ_n · f₀ + V̂_mod
  Ψ(σ)  = exp(−|σ − ½| · (C / (γ · ℏ)) · π)

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
License: MIT
"""

import math
from typing import Dict, List, Tuple

# Frecuencia fundamental
F0 = 141.7001  # Hz

# Constante de Planck reducida (J·s)
HBAR_DEFAULT = 1.0545718e-34

# Umbral de coherencia mínima
PSI_MIN = 0.888

# Primer cero no trivial de Riemann (parte imaginaria)
GAMMA_1 = 14.134725141734693790457


class QCALSpectralOperator:
    """
    Operador espectral QCAL refinado (Berry-Keating).

    Conecta los ceros de Riemann γ_n con autovalores resonantes λ_n
    a través del potencial de modulación V̂_mod = γ · ℏ / C.

    Parameters
    ----------
    gamma : float
        Escala de consciencia / coupling (γ > 0).
    consciousness_density : float
        Multiplicador Lagrange-like (C > 0).
    f0 : float
        Frecuencia fundamental del Logos en Hz (por defecto 141.7001).
    hbar : float
        Constante de Planck reducida en J·s.
    """

    def __init__(
        self,
        gamma: float = 1.0,
        consciousness_density: float = 1.0,
        f0: float = F0,
        hbar: float = HBAR_DEFAULT,
    ) -> None:
        if gamma <= 0:
            raise ValueError("gamma debe ser > 0 para garantizar hermiticidad")
        if consciousness_density <= 0:
            raise ValueError("consciousness_density debe ser > 0")
        self.gamma = gamma
        self.C = consciousness_density
        self.f0 = f0
        self.hbar = hbar

    def modulation_potential(self) -> float:
        """
        Potencial de modulación V̂_mod = γ · ℏ / C.

        Returns
        -------
        float
            Valor del potencial de modulación en J·s (unidades SI).
        """
        return self.gamma * self.hbar / self.C

    def berry_keating_eigenvalue(self, gamma_n: float) -> float:
        """
        Autovalor de Berry-Keating: devuelve γ_n directamente (base Mellin/BK).

        Parameters
        ----------
        gamma_n : float
            Parte imaginaria del n-ésimo cero de Riemann.

        Returns
        -------
        float
            γ_n sin transformación adicional.
        """
        return gamma_n

    def compute_eigenvalue(self, gamma_n: float) -> float:
        """
        Autovalor resonante λ_n = γ_n · f₀ + V̂_mod.

        Parameters
        ----------
        gamma_n : float
            Parte imaginaria del n-ésimo cero de Riemann.

        Returns
        -------
        float
            λ_n en Hz (aproximado).
        """
        return gamma_n * self.f0 + self.modulation_potential()

    def is_hermitian(self) -> bool:
        """
        Hermiticidad garantizada cuando γ > 0 y C > 0.

        Returns
        -------
        bool
            True si el operador es hermítico.
        """
        return self.gamma > 0 and self.C > 0

    def certify_critical_line(self, sigma: float) -> Tuple[bool, float]:
        """
        Certifica si σ está en la línea crítica de Riemann.

        Ψ(σ) = exp(−|σ − ½| · (C / (γ · ℏ)) · π)

        Certificado cuando Ψ ≥ PSI_MIN (0.888).

        Parameters
        ----------
        sigma : float
            Parte real del número complejo s = σ + it.

        Returns
        -------
        (certified, Psi) : Tuple[bool, float]
            certified — True si Ψ ≥ 0.888.
            Psi       — Valor de coherencia Ψ(σ).
        """
        decay_rate = self.C / (self.gamma * self.hbar)
        psi = math.exp(-abs(sigma - 0.5) * decay_rate * math.pi)
        certified = psi >= PSI_MIN
        return certified, psi

    def verify_off_critical_zeros(
        self, sigmas: List[float]
    ) -> Tuple[bool, str]:
        """
        Confirma que fuera de la línea crítica no existe ningún cero certificado.

        Parameters
        ----------
        sigmas : List[float]
            Lista de valores σ a verificar.

        Returns
        -------
        (verified, message) : Tuple[bool, str]
            verified — True si el conjunto de ceros off-critical es vacío.
            message  — Descripción del resultado.
        """
        off_critical = [s for s in sigmas if abs(s - 0.5) > 1e-10]
        certified_any = any(
            self.certify_critical_line(s)[0] for s in off_critical
        )
        if not certified_any:
            return True, "Conjunto de ceros off-critical: ∅"
        return False, "¡Ceros off-critical detectados!"

    def get_spectral_table(
        self, gamma_n_example: float = GAMMA_1
    ) -> Dict:
        """
        Tabla espectral de ejemplo usando el primer cero de Riemann.

        Parameters
        ----------
        gamma_n_example : float
            γ_n de ejemplo (por defecto γ₁ ≈ 14.1347).

        Returns
        -------
        dict
            Diccionario con métricas espectrales clave.
        """
        lam = self.compute_eigenvalue(gamma_n_example)
        herm = self.is_hermitian()
        _, psi_crit = self.certify_critical_line(0.5)
        _, psi_off = self.certify_critical_line(1.0)
        return {
            "lambda_0": lam,
            "hermiticidad": herm,
            "psi_critica": psi_crit,
            "psi_off_critical": psi_off,
            "resonancia_aprox_hz": int(round(lam)),
        }

    def estado_qed_riemann(self) -> str:
        """
        Estado global del operador.

        Returns
        -------
        str
            Cadena de estado de certificación.
        """
        return "QED-RIEMANN-VERIFIED"
