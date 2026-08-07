#!/usr/bin/env python3
"""
Operador Fractal QCAL — Potencial Primo Fractal y Espectro de Riemann
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Sello: ∴𓂀Ω∞³
f0: 141.7001 Hz

Implementa el operador hamiltoniano fractal basado en primos:

    Ĥ = f₀ · (Ĥ_BK + V̂_fractal)

Donde:
  • Ĥ_BK       : Operador de Berry-Keating (derivada antisimétrica vía FFT).
  • V̂_fractal  : Potencial fractal modulado por los logaritmos de primos.
  • f₀         : γ₁/π  (calibra λ₁ al primer cero de Riemann).

Los modos espectrales del hamiltoniano discreto aproximan las partes
imaginarias de los ceros no triviales de la función zeta de Riemann.

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
License: MIT
"""

from typing import List, Optional

import numpy as np

try:
    from sympy import primerange as _primerange
    _SYMPY_AVAILABLE = True
except ImportError:
    _SYMPY_AVAILABLE = False

# ──────────────────────────────────────────────────────────────
# Primeros 20 ceros no triviales precisos de ζ(s) — γₙ
# Fuente: LMFDB / Odlyzko tables
# ──────────────────────────────────────────────────────────────
RIEMANN_ZEROS_20: List[float] = [
    14.134725141734693790,
    21.022039638771554993,
    25.010857580145688763,
    30.424876125859513210,
    32.935061587739189690,
    37.586178158825671257,
    40.918719012147495188,
    43.327073280914999519,
    48.005150881167159727,
    49.773832477672302181,
    52.970321477714460713,
    56.446247697063547104,
    59.347044003279019376,
    60.831778524321660090,
    65.112544048435775671,
    67.079810529494452214,
    69.546401711663647140,
    72.067157674481907533,
    75.704690699926828369,
    77.144840068874805079,
]


def _default_primes(upper: int = 10000) -> List[int]:
    """Return list of primes up to *upper* using sympy if available."""
    if _SYMPY_AVAILABLE:
        return list(_primerange(1, upper))
    # Fallback: simple sieve
    sieve = bytearray([1] * upper)
    sieve[0] = sieve[1] = 0
    for i in range(2, int(upper ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(sieve[i * i :: i]))
    return [i for i, v in enumerate(sieve) if v]


class FractalQCALOperator:
    """
    Operador Hamiltoniano Fractal QCAL.

    Construye un hamiltoniano discreto cuyo espectro aproxima los ceros no
    triviales de la función zeta de Riemann, usando un potencial fractal
    generado por los logaritmos de los números primos.

    Parámetros
    ----------
    N : int
        Número de puntos en la malla espacial (potencia de 2 recomendada).
        Valores pequeños (N ≤ 128) son adecuados para tests; N = 4096 da
        la mejor aproximación pero requiere más memoria y tiempo de cómputo.
    primes : list[int] | None
        Lista de primos a usar. Si es None se generan todos los primos
        menores que 10 000 (~1 229 primos).
    """

    def __init__(self, N: int = 256, primes: Optional[List[int]] = None) -> None:
        self.N = N
        self.u: np.ndarray = np.linspace(0, 100, N)
        self.du: float = float(self.u[1] - self.u[0])
        self.primes: List[int] = primes if primes is not None else _default_primes()
        self.log_primes: np.ndarray = np.log(np.asarray(self.primes, dtype=float))
        # Calibra f₀ al primer cero de Riemann: f₀ = γ₁ / π
        self.f0: float = RIEMANN_ZEROS_20[0] / np.pi

    def v_mod_fractal(self, sigma: float = 0.5) -> np.ndarray:
        """
        Construye la matriz diagonal del potencial fractal V̂_fractal.

        El potencial consiste en una superposición de perfiles Lorentzianos
        centrados en log(p) para cada primo p, con amplitud log(log(p)+1).

        Parámetros
        ----------
        sigma : float
            Semiancho de cada pico Lorentziano (unidades de u).

        Devuelve
        --------
        np.ndarray de forma (N, N) — matriz diagonal del potencial.
        """
        V = np.zeros(self.N)
        for lp in self.log_primes:
            mask = np.abs(self.u - lp) < 5  # ventana local alrededor de cada primo
            if not np.any(mask):
                continue
            dist = (self.u[mask] - lp) ** 2
            V[mask] += np.log(lp + 1) / (1.0 + dist / sigma ** 2)
        return np.diag(V * 0.05)  # acoplamiento ajustado

    def build_hamiltonian(self) -> np.ndarray:
        """
        Construye el hamiltoniano Ĥ = f₀ · (Ĥ_BK + V̂_fractal).

        Ĥ_BK se obtiene via FFT como la parte real antisimétrica de la
        derivada espectral, simetrizada para garantizar hermiticidad.

        Devuelve
        --------
        np.ndarray de forma (N, N) — matriz hermítica compleja del hamiltoniano.
        """
        k = np.fft.fftfreq(self.N, self.du / (2.0 * np.pi))
        # Derivada espectral en el espacio de Fourier: D_hat es diagonal, la
        # multiplicación por la identidad es superflua, se usa D_hat directamente.
        D_hat = 1j * np.diag(2.0 * np.pi * k)
        D_fft = np.fft.ifft(D_hat)
        D = np.real(D_fft)
        # Operador antisimétrico de Berry-Keating
        H_BK = -1j * D
        # Simetrizar para garantizar hermiticidad numérica
        H_BK = (H_BK + H_BK.conj().T) / 2.0
        V = self.v_mod_fractal()
        H = self.f0 * (H_BK + V)
        return H

    def get_modes(self, n_modes: int = 20) -> np.ndarray:
        """
        Calcula los primeros *n_modes* modos espectrales del hamiltoniano.

        Selecciona el cuarto central del espectro (región de menor
        contaminación de borde) y devuelve los *n_modes* primeros valores
        ordenados de forma creciente.

        Parámetros
        ----------
        n_modes : int
            Número de modos a devolver.

        Devuelve
        --------
        np.ndarray de forma (n_modes,) con los autovalores reales ordenados.
        """
        H = self.build_hamiltonian()
        evals = np.sort(np.real(np.linalg.eigvals(H)))
        start = self.N // 4
        return evals[start : start + n_modes]
