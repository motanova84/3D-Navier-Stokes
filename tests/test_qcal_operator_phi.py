#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Tests for QCAL Operator Φ (Phi) and RNA Barrier Fold.

Tests cover:
  1. Constantes fundamentales (F0, PSI_TARGET, CONTRACTION_K, H_PLANCK, E_MIN)
  2. QCALOperatorPhi (transform, verify_coherence, energy_min, effective_viscosity)
  3. QCALRNABarrierFold (initialize_random_chain, compute_native_attractor, apply_operator_phi, simulate_folding)
  4. QCALNavierStokesRegularizer (critical_enstrophy, enstrophy_derivative_bound, is_bounded, spectral_transfer_filter)
  5. Demostración completa (run_qcal_operator_demo)

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
License: MIT
"""

import math
import os
import sys
import unittest

import numpy as np

# Ensure repository root is on path
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from qcal.operator_phi import (
    CONTRACTION_K,
    E_MIN,
    F0,
    H_PLANCK,
    PSI_TARGET,
    SIGMA_DEFAULT,
    QCALNavierStokesRegularizer,
    QCALOperatorPhi,
    QCALRNABarrierFold,
    run_qcal_operator_demo,
)


class TestQCALConstants(unittest.TestCase):
    """Pruebas para las constantes fundamentales de QCAL."""

    def test_f0_value(self) -> None:
        """La frecuencia base f₀ debe ser 141.7001 Hz."""
        self.assertAlmostEqual(F0, 141.7001, places=4)

    def test_psi_target_value(self) -> None:
        """El objetivo de coherencia debe ser 0.999999."""
        self.assertAlmostEqual(PSI_TARGET, 0.999999, places=6)

    def test_contraction_k_value(self) -> None:
        """La constante de contracción de Banach debe ser 1e-6."""
        self.assertEqual(CONTRACTION_K, 1e-6)

    def test_sigma_default_value(self) -> None:
        """El margen de imperfección estocástico es 1.0 - PSI_TARGET."""
        self.assertAlmostEqual(SIGMA_DEFAULT, 1e-6, places=8)

    def test_planck_constant(self) -> None:
        """Constante de Planck h."""
        self.assertAlmostEqual(H_PLANCK, 6.62607015e-34, delta=1e-40)

    def test_e_min(self) -> None:
        """Energía mínima teórica E_min = h · f₀ · Ψ."""
        expected = H_PLANCK * F0 * PSI_TARGET
        self.assertAlmostEqual(E_MIN, expected, delta=1e-40)
        self.assertGreater(E_MIN, 0.0)


class TestQCALOperatorPhi(unittest.TestCase):
    """Pruebas unitarias para QCALOperatorPhi."""

    def setUp(self) -> None:
        self.op = QCALOperatorPhi()

    def test_default_initialization(self) -> None:
        """Verifica inicialización con parámetros QCAL por defecto."""
        self.assertEqual(self.op.f_0, 141.7001)
        self.assertEqual(self.op.psi, 0.999999)
        self.assertEqual(self.op.k, 1e-6)
        self.assertAlmostEqual(self.op.sigma, 1e-6, places=8)

    def test_custom_initialization(self) -> None:
        """Verifica inicialización con parámetros personalizados."""
        custom_op = QCALOperatorPhi(f_0=888.0, psi_target=0.99, contraction_k=1e-4)
        self.assertEqual(custom_op.f_0, 888.0)
        self.assertEqual(custom_op.psi, 0.99)
        self.assertEqual(custom_op.k, 1e-4)
        self.assertAlmostEqual(custom_op.sigma, 0.01, places=8)

    def test_transform_shape(self) -> None:
        """Transform mantiene las dimensiones del vector de entrada."""
        x = np.random.normal(0, 1, 100)
        noise = np.random.normal(0, 0.5, 100)
        x_next = self.op.transform(x, noise)
        self.assertEqual(x_next.shape, (100,))

    def test_transform_empty(self) -> None:
        """Transform con entrada vacía retorna arreglo vacío."""
        x = np.array([])
        noise = np.array([])
        x_next = self.op.transform(x, noise)
        self.assertEqual(len(x_next), 0)

    def test_contraction_towards_attractor(self) -> None:
        """Las iteraciones sucesivas contraen fuertemente el estado hacia el atractor x*=0."""
        np.random.seed(42)
        x = np.ones(50) * 10.0
        noise = np.zeros(50)  # Sin ruido para aislar la contracción determinista
        x_step = self.op.transform(x, noise)
        # x_next = k * x + (1-k)*0 = 1e-6 * 10 = 1e-5
        self.assertAlmostEqual(float(np.mean(x_step)), 10.0 * 1e-6, places=8)

    def test_verify_coherence_bounds(self) -> None:
        """La coherencia nunca excede psi_target y es no negativa."""
        state_perfect = np.zeros(100)
        coh_high = self.op.verify_coherence(state_perfect)
        self.assertLessEqual(coh_high, self.op.psi)
        self.assertGreaterEqual(coh_high, 0.0)

        state_noisy = np.random.normal(0, 10.0, 100)
        coh_low = self.op.verify_coherence(state_noisy)
        self.assertGreaterEqual(coh_low, 0.0)
        self.assertLessEqual(coh_low, self.op.psi)

    def test_energy_min_method(self) -> None:
        """Cálculo de energía mínima h · f₀ · Ψ."""
        e_min = self.op.energy_min()
        self.assertAlmostEqual(e_min, H_PLANCK * 141.7001 * 0.999999, delta=1e-40)

    def test_effective_viscosity(self) -> None:
        """La viscosidad efectiva es positiva y modulada armónicamente."""
        nu_0 = 1e-3
        nu_eff = self.op.effective_viscosity(nu_0, t=0.0, u_norm=1.0)
        self.assertGreater(nu_eff, 0.0)
        # La modulación debe estar acotada por nu_0 * (1 ± sigma)
        self.assertLessEqual(nu_eff, nu_0 * (1.0 + self.op.sigma + 1e-12))
        self.assertGreaterEqual(nu_eff, nu_0 * (1.0 - self.op.sigma - 1e-12))


class TestQCALRNABarrierFold(unittest.TestCase):
    """Pruebas para el algoritmo de plegamiento de ARN QCAL."""

    def setUp(self) -> None:
        self.folder = QCALRNABarrierFold(sequence_length=40)

    def test_initialization(self) -> None:
        """Verifica longitud y parámetros del plegador."""
        self.assertEqual(self.folder.length, 40)
        self.assertEqual(self.folder.f_0, 141.7001)
        self.assertEqual(self.folder.psi, 0.999999)
        self.assertEqual(self.folder.k, 1e-6)

    def test_initialize_random_chain(self) -> None:
        """La conformación inicial tiene dimensiones (length, 3)."""
        chain = self.folder.initialize_random_chain(seed=123)
        self.assertEqual(chain.shape, (40, 3))
        # Reproducibilidad con la misma semilla
        chain2 = self.folder.initialize_random_chain(seed=123)
        np.testing.assert_array_equal(chain, chain2)

    def test_compute_native_attractor(self) -> None:
        """El atractor nativo helicoidal tiene dimensiones (length, 3)."""
        attractor = self.folder.compute_native_attractor()
        self.assertEqual(attractor.shape, (40, 3))
        # Radio x-y constante de la hélice = 3.0
        radii = np.sqrt(attractor[:, 0] ** 2 + attractor[:, 1] ** 2)
        np.testing.assert_allclose(radii, 3.0, rtol=1e-5)

    def test_apply_operator_phi(self) -> None:
        """Un paso de operador mantiene dimensiones y actualiza conformación."""
        chain = self.folder.initialize_random_chain(seed=42)
        chain_next = self.folder.apply_operator_phi(chain, t_step=0.01)
        self.assertEqual(chain_next.shape, (40, 3))
        self.assertFalse(np.array_equal(chain, chain_next))

    def test_simulate_folding(self) -> None:
        """Simulación de plegamiento completa."""
        final_coords = self.folder.simulate_folding(steps=20, verbose=False)
        self.assertEqual(final_coords.shape, (40, 3))
        self.assertFalse(np.any(np.isnan(final_coords)))


class TestQCALNavierStokesRegularizer(unittest.TestCase):
    """Pruebas para la regularización de Navier-Stokes y acotamiento de enstropía."""

    def setUp(self) -> None:
        self.reg = QCALNavierStokesRegularizer(
            nu_0=1e-3,
            f_0=141.7001,
            psi_target=0.999999,
            c1=1.0,
            c2=1e-4,
        )

    def test_critical_enstrophy(self) -> None:
        """Cálculo analítico de Ω_crit = (C₂ f₀² / C₁)²."""
        expected_ratio = (1e-4 * (141.7001 ** 2)) / 1.0
        expected_crit = expected_ratio ** 2
        self.assertAlmostEqual(self.reg.critical_enstrophy, expected_crit, places=4)

    def test_enstrophy_derivative_bound_in_attractor(self) -> None:
        """Para Ω < Ω_crit, dΩ/dt < 0 en régimen lineal (el atractor confina la enstropía)."""
        crit = self.reg.critical_enstrophy
        omega_sub = crit * 0.5
        d_omega = self.reg.enstrophy_derivative_bound(omega_sub)
        self.assertLess(d_omega, 0.0)
        self.assertTrue(self.reg.is_bounded(omega_sub))

    def test_enstrophy_derivative_bound_nonlinear(self) -> None:
        """En régimen no lineal hiperbólico (dissipation ∝ Ω²), dΩ/dt < 0 para Ω grande."""
        crit = self.reg.critical_enstrophy
        omega_super = max(10.0, crit * 2.0)
        d_omega = self.reg.enstrophy_derivative_bound(omega_super, nonlinear_dissipation=True)
        self.assertLess(d_omega, 0.0)
        self.assertTrue(self.reg.is_bounded(omega_super, nonlinear_dissipation=True))

    def test_enstrophy_derivative_bound_zero(self) -> None:
        """Para Ω = 0, la cota es 0."""
        self.assertEqual(self.reg.enstrophy_derivative_bound(0.0), 0.0)
        self.assertTrue(self.reg.is_bounded(0.0))

    def test_spectral_transfer_filter(self) -> None:
        """Filtro armónico W(k, f₀): W(0) = 1, W(k→∞) → 0, monótonamente decreciente."""
        k = np.array([0.0, 100.0, 1000.0, 10000.0])
        w = self.reg.spectral_transfer_filter(k)
        self.assertAlmostEqual(w[0], 1.0)
        for i in range(len(w) - 1):
            self.assertGreater(w[i], w[i + 1])
        self.assertGreater(w[-1], 0.0)
        self.assertLess(w[-1], 0.01)

    def test_spectral_step(self) -> None:
        """Avanza paso espectral atenuando frecuencias altas."""
        k = np.linspace(0, 5000, 50)
        u_spectral = np.ones(50)
        u_filtered = self.reg.spectral_step(u_spectral, k)
        self.assertEqual(len(u_filtered), 50)
        self.assertAlmostEqual(u_filtered[0], 1.0)
        self.assertLess(u_filtered[-1], u_filtered[0])


class TestQCALOperatorDemo(unittest.TestCase):
    """Prueba de la función de demostración general."""

    def test_run_demo(self) -> None:
        res = run_qcal_operator_demo()
        self.assertEqual(res["f_0"], 141.7001)
        self.assertEqual(res["psi_target"], 0.999999)
        self.assertEqual(len(res["coherencias"]), 5)
        self.assertTrue(res["is_bounded_in_attractor"])
        self.assertGreater(res["energy_min"], 0.0)


if __name__ == "__main__":
    unittest.main()
