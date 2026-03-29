#!/usr/bin/env python3
"""
network/navier_stokes_flow.py — Flujo Superfluido en C7
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Sello: ∴𓂀Ω∞³
f0: 141700.1 Hz

Implementa el operador de traslación unitario sobre el ciclo C7
(los 7 nodos de los primos {2, 3, 5, 7, 11, 13, 17}).

Fundamento matemático (Cierre de la Brecha B):
  - La medida de Haar μ en G = C7 es invariante por traslación izquierda.
  - El operador L_g f(x) = f(g⁻¹ x) es una isometría en L²(G, μ).
  - En representación discreta (N=7): L_g ≅ np.roll(I, 1), con det = 1.
  - La conservación de norma ‖L_g v‖ = ‖v‖ garantiza incompresibilidad.

Frecuencia de muestreo: f₀ = 141 700,1 Hz  →  dt = 1/f₀ ≈ 7.06 µs
"""

import numpy as np

# Frecuencia maestra del integrador cuántico (Hz)
F0: float = 141700.1


class SuperfluidFlow:
    """Flujo superfluido sobre el grafo de 7 nodos (ciclo C7).

    Modela el flujo de Navier-Stokes sin viscosidad (ν = 0) como un
    operador de traslación unitario sobre los nodos
    {2, 3, 5, 7, 11, 13, 17} del grafo adélico.

    Propiedades garantizadas:
    - ``np.linalg.matrix_rank(velocity_field) == nodes``  (full rank)
    - ``abs(np.linalg.det(velocity_field)) == 1.0``        (unitariedad)
    - ``np.linalg.norm(step(v)) == np.linalg.norm(v)``    (isometría)

    Parameters
    ----------
    nodes:
        Número de nodos del ciclo (por defecto 7, los 7 primos de C7).
    f0:
        Frecuencia maestra del integrador cuántico en Hz (por defecto
        141 700,1 Hz).
    """

    def __init__(self, nodes: int = 7, f0: float = F0) -> None:
        self.n: int = nodes
        self.f0: float = f0
        self.dt: float = 1.0 / f0

        # Matriz de permutación cíclica: representa L_g en C7.
        # np.roll(I, 1, axis=0) desplaza cada fila un lugar hacia adelante,
        # lo que corresponde al operador de traslación discreta.
        # Det(velocity_field) = (-1)^(n-1) con |det| = 1 (matriz de permutación).
        self.velocity_field: np.ndarray = np.roll(np.eye(nodes), 1, axis=0)

    # ------------------------------------------------------------------
    # Operador de evolución
    # ------------------------------------------------------------------

    def step(self, state_vector: np.ndarray) -> np.ndarray:
        """Aplica el operador de traslación (unitario) al vector de estado.

        Dado que ``velocity_field`` es una matriz de permutación,
        la operación es una isometría:

            ‖step(v)‖₂ = ‖velocity_field · v‖₂ = ‖v‖₂

        Parameters
        ----------
        state_vector:
            Vector de estado de longitud ``self.n``.

        Returns
        -------
        np.ndarray
            Estado evolucionado, con la misma norma que el estado de entrada.
        """
        return np.dot(self.velocity_field, state_vector)

    # ------------------------------------------------------------------
    # Métricas de coherencia
    # ------------------------------------------------------------------

    def norm_ratio(self, state_vector: np.ndarray) -> float:
        """Cociente de normas tras un paso: debe ser exactamente 1.0.

        Sello de coherencia: si el flujo es unitario, det(V) = 1 y la
        norma se conserva ⟹ Brecha B cerrada en simulación.

        Returns
        -------
        float
            ‖step(v)‖ / ‖v‖.  Idealmente 1.0 (dentro de precisión float64).
        """
        norm_in = float(np.linalg.norm(state_vector))
        if norm_in == 0.0:
            return 1.0
        return float(np.linalg.norm(self.step(state_vector))) / norm_in

    def determinant(self) -> float:
        """Determinante de la matriz de flujo.

        Para una matriz de permutación cíclica de N×N:
        det = (-1)^(N-1).  El valor absoluto es siempre 1.

        Returns
        -------
        float
            det(velocity_field).
        """
        return float(np.linalg.det(self.velocity_field))

    def is_unitary(self, tol: float = 1e-12) -> bool:
        """Verifica unitariedad: V @ V.T == I (dentro de tolerancia numérica).

        Returns
        -------
        bool
            True si ``velocity_field`` es unitaria.
        """
        product = self.velocity_field @ self.velocity_field.T
        return bool(np.allclose(product, np.eye(self.n), atol=tol))
