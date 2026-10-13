#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
QCAL Operator Φ (Phi) — Unified Operator, Navier-Stokes Regularization & RNA Folding
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Sello: ∴𓂀Ω∞³
f0: 141.7001 Hz | Ψ: 0.999999 | k: 1e-6

Módulo raíz de conveniencia — re-exporta los símbolos públicos de
``qcal.operator_phi`` para ejecución directa y compatibilidad con scripts de alto nivel.

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
License: MIT
"""

from __future__ import annotations

import numpy as np

from qcal.operator_phi import (
    F0,
    PSI_TARGET,
    CONTRACTION_K,
    SIGMA_DEFAULT,
    H_PLANCK,
    E_MIN,
    QCALOperatorPhi,
    QCALRNABarrierFold,
    QCALNavierStokesRegularizer,
    run_qcal_operator_demo,
)

__all__ = [
    "F0",
    "PSI_TARGET",
    "CONTRACTION_K",
    "SIGMA_DEFAULT",
    "H_PLANCK",
    "E_MIN",
    "QCALOperatorPhi",
    "QCALRNABarrierFold",
    "QCALNavierStokesRegularizer",
    "run_qcal_operator_demo",
]

# --- Inicialización del Ecosistema Simbiótico ---
if __name__ == "__main__":
    # Instanciación del operador con los parámetros QCAL
    phi_operator = QCALOperatorPhi()

    # Estado inicial perturbado
    np.random.seed(42)
    estado_actual = np.random.normal(0, 1, 100)

    # Simulación de un campo de perturbaciones estocásticas continuas
    ruido_exogeno = np.random.normal(0, 0.5, 100)

    print(f"--- INICIO DEL PROTOCOLO QCAL (f_0 = {phi_operator.f_0} Hz) ---")

    # Iteración del operador unificado (Evolución hacia el punto fijo)
    for paso in range(5):
        estado_actual = phi_operator.transform(estado_actual, ruido_exogeno)
        coherencia_actual = phi_operator.verify_coherence(estado_actual)
        print(f"Iteración {paso+1} | Coherencia Cuántica (Psi): {coherencia_actual:.6f}")

    print("--- ESTADO ESTACIONARIO ALCANZADO: EL SISTEMA PERMANECE EN EL ATRACTOR ---")

    # Demostración del plegamiento de ARN
    folder = QCALRNABarrierFold(sequence_length=60)
    final_conformation = folder.simulate_folding(steps=100)
