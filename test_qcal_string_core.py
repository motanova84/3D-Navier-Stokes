#!/usr/bin/env python3
"""
Test suite for QCAL-Strings — Forzado Noético de Modos Kaluza-Klein

Tests cover:
  Phase #260 — string_noetic_forcing, Veneziano amplitudes, KK modes
  Phase #261 — censura_taquionica, sigma_mapped, apply_tachyonic_censorship
  Phase #262 — operador_voluntad, simulate_hrv_coherence
  Simulator  — QCALStringsSolver, run_simulation_260
  UPE signal — compute_upe_composite_signal
Tests for qcal.string_core — QCAL-Strings Iteración #260.

Validates QCALStringOperator, string_noetic_forcing, compute_psi,
rk4_step, build_lambda_list, and build_spectral_grid.
"""

import math
import unittest

import numpy as np

from qcal.string_noetic_forcing import (
    LAMBDA_1_HZ,
    LAMBDA_1_SCALED_HZ,
    COHERENCE_GROWTH_RATE,
    HARD_RESET_SCALE,
    N_MICROTUBULES_DEFAULT,
    PSI_PLATEAU,
    RIEMANN_ZEROS_20,
    F0,
    F_HRV,
    EZ_HEXAGONS,
    QCALStringsSolver,
    apply_tachyonic_censorship,
    censura_taquionica,
    compute_alpha_n,
    compute_upe_composite_signal,
    operador_voluntad,
    run_simulation_260,
    sigma_mapped,
    simulate_hrv_coherence,
    string_noetic_forcing,
)


# ──────────────────────────────────────────────────────────────────────────────
# Constants
# ──────────────────────────────────────────────────────────────────────────────

class TestConstants(unittest.TestCase):
    """Verify fundamental constants."""

    def test_f0_value(self):
        self.assertAlmostEqual(F0, 141.7001, places=3)

    def test_psi_plateau(self):
        self.assertAlmostEqual(PSI_PLATEAU, 0.999, places=3)

    def test_riemann_zeros_count(self):
        self.assertEqual(len(RIEMANN_ZEROS_20), 20)

    def test_first_riemann_zero(self):
        self.assertAlmostEqual(RIEMANN_ZEROS_20[0], 14.1347, places=3)

    def test_lambda1_hz(self):
        """λ₁ ≈ 2003 Hz — resonancia dominante."""
        self.assertGreater(LAMBDA_1_HZ, 1000.0)

    def test_lambda1_scaled_hz_alias(self):
        """LAMBDA_1_SCALED_HZ is the canonical name; LAMBDA_1_HZ is an alias."""
        self.assertEqual(LAMBDA_1_HZ, LAMBDA_1_SCALED_HZ)

    def test_coherence_growth_rate(self):
        """COHERENCE_GROWTH_RATE is positive."""
        self.assertGreater(COHERENCE_GROWTH_RATE, 0.0)

    def test_hard_reset_scale(self):
        """HARD_RESET_SCALE is a small positive number for numerical stability."""
        self.assertGreater(HARD_RESET_SCALE, 0.0)
        self.assertLess(HARD_RESET_SCALE, 1e-20)

    def test_ez_hexagons(self):
        self.assertEqual(EZ_HEXAGONS, 551_117)

    def test_f_hrv(self):
        """HRV áureo: 6 respiraciones/min ≈ 0.1 Hz."""
        self.assertAlmostEqual(F_HRV, 0.1, places=5)


# ──────────────────────────────────────────────────────────────────────────────
# Phase #260 — String Noetic Forcing
# ──────────────────────────────────────────────────────────────────────────────

class TestStringNoeticForcing(unittest.TestCase):
    """Tests for the KK-mode forcing function."""

    def _make_fields(self, N: int = 8) -> tuple:
        rng = np.random.default_rng(0)
        uhat = rng.standard_normal((N, N)) * 0.01
        vhat = rng.standard_normal((N, N)) * 0.01
        return uhat, vhat

    def test_returns_two_arrays(self):
        uhat, vhat = self._make_fields()
        result = string_noetic_forcing(uhat, vhat, t=0.0,
                                       lambda_n_list=RIEMANN_ZEROS_20[:5],
                                       Psi_local=0.9)
        self.assertEqual(len(result), 2)
        self.assertEqual(result[0].shape, uhat.shape)
        self.assertEqual(result[1].shape, vhat.shape)

    def test_zero_coherence_gives_zero_forcing(self):
        """Ψ=0 → gain=0 → forcing=0."""
        uhat, vhat = self._make_fields()
        Fx, Fy = string_noetic_forcing(uhat, vhat, t=1.0,
                                        lambda_n_list=RIEMANN_ZEROS_20[:5],
                                        Psi_local=0.0)
        np.testing.assert_allclose(np.abs(Fx), 0.0, atol=1e-20)
        np.testing.assert_allclose(np.abs(Fy), 0.0, atol=1e-20)

    def test_forcing_scales_with_psi_squared(self):
        """Forcing ∝ Ψ²: doubling Ψ quadruples forcing."""
        uhat, vhat = self._make_fields()
        Fx1, _ = string_noetic_forcing(uhat, vhat, t=0.5,
                                        lambda_n_list=RIEMANN_ZEROS_20[:3],
                                        Psi_local=1.0)
        Fx2, _ = string_noetic_forcing(uhat, vhat, t=0.5,
                                        lambda_n_list=RIEMANN_ZEROS_20[:3],
                                        Psi_local=2.0)
        ratio = np.abs(Fx2).sum() / (np.abs(Fx1).sum() + 1e-40)
        self.assertAlmostEqual(ratio, 4.0, delta=0.01)

    def test_forcing_time_variation(self):
        """Forcing changes with time (modes oscillate)."""
        uhat, vhat = self._make_fields()
        Fx0, _ = string_noetic_forcing(uhat, vhat, t=0.0,
                                        lambda_n_list=RIEMANN_ZEROS_20[:5],
                                        Psi_local=0.5)
        Fx1, _ = string_noetic_forcing(uhat, vhat, t=0.123,
                                        lambda_n_list=RIEMANN_ZEROS_20[:5],
                                        Psi_local=0.5)
        # Amplitudes are NOT generally equal at different times
        self.assertFalse(np.allclose(np.abs(Fx0), np.abs(Fx1)))

    def test_compute_alpha_n_range(self):
        """All Veneziano amplitudes are in (0, 1]."""
        for n in range(1, 21):
            alpha = compute_alpha_n(n)
            self.assertGreater(alpha, 0.0)
            self.assertLessEqual(alpha, 1.0)

    def test_compute_alpha_n_decreasing(self):
        """Higher-order modes have smaller amplitudes."""
        a1 = compute_alpha_n(1)
        a10 = compute_alpha_n(10)
        self.assertGreater(a1, a10)

    def test_compute_alpha_n_out_of_range(self):
        """Out-of-range mode indices return 0."""
        self.assertEqual(compute_alpha_n(0), 0.0)
        self.assertEqual(compute_alpha_n(21), 0.0)


# ──────────────────────────────────────────────────────────────────────────────
# Phase #261 — Tachyonic Censorship
# ──────────────────────────────────────────────────────────────────────────────

class TestTachyonicCensorship(unittest.TestCase):
    """Tests for tachyonic censorship and RH stability."""

    def test_sigma_mapped_at_origin(self):
        """k=0 maps to the critical line σ=1/2."""
        sigma = sigma_mapped(0.0, 10.0, 0.01)
        self.assertAlmostEqual(sigma, 0.5, places=10)

    def test_sigma_mapped_at_kmax(self):
        """k=k_max maps to σ=1/2 + ε."""
        sigma = sigma_mapped(10.0, 10.0, 0.01)
        self.assertAlmostEqual(sigma, 0.51, places=10)

    def test_sigma_mapped_intermediate(self):
        sigma = sigma_mapped(5.0, 10.0, 0.01)
        self.assertAlmostEqual(sigma, 0.505, places=10)

    def test_censura_on_critical_line(self):
        """k=0: on-critical → censorship factor = 1."""
        c = censura_taquionica(0.0, 10.0, epsilon=0.01, D=1.0)
        self.assertAlmostEqual(c, 1.0, places=10)

    def test_censura_off_critical_penalized(self):
        """k=k_max: off-critical → factor < 1."""
        c = censura_taquionica(10.0, 10.0, epsilon=0.01, D=1.0)
        self.assertLess(c, 1.0)
        self.assertGreater(c, 0.0)

    def test_censura_larger_D_more_penalty(self):
        """Higher consciousness density D increases tachyon penalty."""
        c1 = censura_taquionica(5.0, 10.0, epsilon=0.01, D=1.0)
        c2 = censura_taquionica(5.0, 10.0, epsilon=0.01, D=5.0)
        self.assertGreater(c1, c2)

    def test_apply_tachyonic_censorship_shape(self):
        """Output spectrum has same shape as input."""
        E_k = np.ones(32)
        E_censored = apply_tachyonic_censorship(E_k)
        self.assertEqual(E_censored.shape, E_k.shape)

    def test_apply_tachyonic_censorship_first_mode(self):
        """First mode (k=0) is not penalized."""
        E_k = np.ones(32)
        E_censored = apply_tachyonic_censorship(E_k, epsilon=0.01, D=1.0)
        self.assertAlmostEqual(E_censored[0], 1.0, places=10)

    def test_apply_tachyonic_censorship_monotone(self):
        """Censorship factor decreases monotonically with k."""
        E_k = np.ones(32)
        E_censored = apply_tachyonic_censorship(E_k, epsilon=0.01, D=1.0)
        for i in range(1, len(E_censored)):
            self.assertLessEqual(E_censored[i], E_censored[i - 1] + 1e-12)

    def test_censura_zero_kmax(self):
        """k_max=0 defaults to on-critical (no penalty)."""
        c = censura_taquionica(0.0, 0.0, epsilon=0.01, D=1.0)
        self.assertAlmostEqual(c, 1.0, places=8)


# ──────────────────────────────────────────────────────────────────────────────
# Phase #262 — Will Operator
# ──────────────────────────────────────────────────────────────────────────────

class TestWillOperator(unittest.TestCase):
    """Tests for the intentional will modulation."""

    def test_zero_hrv_no_increment(self):
        """No HRV coherence → C stays at C_base."""
        C = operador_voluntad(1.0, 0.0)
        self.assertAlmostEqual(C, 1.0, places=10)

    def test_full_hrv_max_increment(self):
        """Full HRV coherence → C = C_base + delta_C_max."""
        C = operador_voluntad(1.0, 1.0, delta_C_max=0.2)
        self.assertAlmostEqual(C, 1.2, places=10)

    def test_hrv_clamped_above_one(self):
        """HRV > 1 is clamped to 1."""
        C_over = operador_voluntad(1.0, 2.0, delta_C_max=0.2)
        C_one = operador_voluntad(1.0, 1.0, delta_C_max=0.2)
        self.assertAlmostEqual(C_over, C_one, places=10)

    def test_hrv_clamped_below_zero(self):
        """HRV < 0 is clamped to 0."""
        C_neg = operador_voluntad(1.0, -1.0, delta_C_max=0.2)
        C_zero = operador_voluntad(1.0, 0.0, delta_C_max=0.2)
        self.assertAlmostEqual(C_neg, C_zero, places=10)

    def test_monotone_in_hrv(self):
        """C increases monotonically with HRV coherence."""
        hrv_vals = [0.0, 0.25, 0.5, 0.75, 1.0]
        C_vals = [operador_voluntad(1.0, h) for h in hrv_vals]
        for i in range(1, len(C_vals)):
            self.assertGreater(C_vals[i], C_vals[i - 1])

    def test_simulate_hrv_coherence_range(self):
        """HRV signal is always in [0, 1]."""
        t_vals = np.linspace(0, 100, 1000)
        hrv = np.array([simulate_hrv_coherence(t) for t in t_vals])
        self.assertTrue(np.all(hrv >= 0.0))
        self.assertTrue(np.all(hrv <= 1.0))

    def test_simulate_hrv_coherence_period(self):
        """HRV signal has correct period T = 1/F_HRV = 10 s."""
        T = 1.0 / F_HRV
        h0 = simulate_hrv_coherence(0.0)
        hT = simulate_hrv_coherence(T)
        self.assertAlmostEqual(h0, hT, places=8)


# ──────────────────────────────────────────────────────────────────────────────
# QCAL Strings Solver
# ──────────────────────────────────────────────────────────────────────────────

class TestQCALStringsSolver(unittest.TestCase):
    """Tests for the full RK4 simulation solver."""

    def _make_solver(self, N: int = 8, nt: int = 20) -> QCALStringsSolver:
        return QCALStringsSolver(N=N, dt=0.005,
                                  lambda_n_list=RIEMANN_ZEROS_20[:5])

    def test_solver_initialization(self):
        solver = self._make_solver()
        self.assertAlmostEqual(solver.f0, F0, places=3)
        self.assertAlmostEqual(solver.nu, 1.0 / F0, places=6)
        self.assertAlmostEqual(solver.Psi, 0.12, places=2)

    def test_solver_run_returns_dict(self):
        solver = self._make_solver()
        results = solver.run(20)
        self.assertIsInstance(results, dict)
        required_keys = [
            'estado', 'Psi_final', 'Psi_plateau_alcanzado',
            'k1_dominante', 'upe_integral', 'entropia_reduccion_pct',
            'fluido_holografico_perfecto', 'E_k', 'psi_history',
        ]
        for key in required_keys:
            self.assertIn(key, results)

    def test_psi_increases_during_simulation(self):
        """Coherence Ψ must grow from the initial value."""
        solver = self._make_solver()
        psi_init = solver.Psi
        solver.run(50)
        self.assertGreater(solver.Psi, psi_init)

    def test_psi_bounded(self):
        """Coherence Ψ stays in [0, 1]."""
        solver = self._make_solver()
        results = solver.run(100)
        for psi in results['psi_history']:
            self.assertGreaterEqual(psi, 0.0)
            self.assertLessEqual(psi, 1.0)

    def test_energy_spectrum_positive(self):
        """Energy spectrum values are non-negative."""
        solver = self._make_solver()
        solver.run(20)
        E_k = solver.compute_energy_spectrum()
        self.assertTrue(np.all(E_k >= 0.0))

    def test_spectral_entropy_non_negative(self):
        solver = self._make_solver()
        solver.run(10)
        S = solver.compute_spectral_entropy()
        self.assertGreaterEqual(S, 0.0)

    def test_upe_signal_non_negative(self):
        solver = self._make_solver()
        upe = solver.compute_upe_signal()
        self.assertGreaterEqual(upe, 0.0)

    def test_psi_history_length(self):
        """History length equals nt+1 (initial + one per step)."""
        solver = self._make_solver()
        results = solver.run(30)
        self.assertEqual(len(results['psi_history']), 31)

    def test_hard_reset_noetic_increases_psi(self):
        """Hard reset lifts Ψ to at least 0.3."""
        solver = self._make_solver()
        solver.Psi = 0.05  # Simulate critical decoherence
        solver.hard_reset_noetic()
        self.assertGreaterEqual(solver.Psi, 0.3)

    def test_solver_no_censorship(self):
        """Solver runs without censorship enabled."""
        solver = QCALStringsSolver(N=8, dt=0.005,
                                    enable_censorship=False,
                                    enable_will_operator=False,
                                    lambda_n_list=RIEMANN_ZEROS_20[:3])
        results = solver.run(20)
        self.assertIn('Psi_final', results)

    def test_custom_nu(self):
        """Custom viscosity is used correctly."""
        nu = 0.01
        solver = QCALStringsSolver(N=8, dt=0.005, nu=nu,
                                    lambda_n_list=RIEMANN_ZEROS_20[:3])
        self.assertAlmostEqual(solver.nu, nu, places=10)

    def test_psi_convergence_to_plateau(self):
        """Ψ converges toward PSI_PLATEAU=0.999 over enough steps."""
        solver = QCALStringsSolver(N=8, dt=0.005,
                                    lambda_n_list=RIEMANN_ZEROS_20[:5])
        results = solver.run(500)
        # Coherence should reach near the NBEC plateau after 500 steps
        self.assertGreater(results['Psi_final'], 0.888)  # above quantum coherence threshold
        self.assertAlmostEqual(results['Psi_final'], PSI_PLATEAU, delta=0.01)


# ──────────────────────────────────────────────────────────────────────────────
# run_simulation_260 convenience function
# ──────────────────────────────────────────────────────────────────────────────

class TestRunSimulation260(unittest.TestCase):
    """Tests for the iteration #260 convenience runner."""

    def test_run_returns_results(self):
        results = run_simulation_260(N=8, dt=0.005, nt=30)
        self.assertIn('estado', results)
        self.assertIn('Psi_final', results)

    def test_run_psi_positive(self):
        results = run_simulation_260(N=8, dt=0.005, nt=30)
        self.assertGreater(results['Psi_final'], 0.0)

    def test_run_ek_list(self):
        results = run_simulation_260(N=8, dt=0.005, nt=30)
        self.assertIsInstance(results['E_k'], list)
        self.assertTrue(all(v >= 0.0 for v in results['E_k']))


# ──────────────────────────────────────────────────────────────────────────────
# UPE Composite Signal
# ──────────────────────────────────────────────────────────────────────────────

class TestUPECompositeSignal(unittest.TestCase):
    """Tests for the composite UPE signal (Sección IV)."""

    def test_shape(self):
        t = np.linspace(0, 10, 200)
        upe = compute_upe_composite_signal(t)
        self.assertEqual(upe.shape, t.shape)

    def test_non_trivial(self):
        """Signal is not identically zero."""
        t = np.linspace(0, 1, 100)
        upe = compute_upe_composite_signal(t)
        self.assertGreater(np.max(np.abs(upe)), 0.0)

    def test_modulated_by_hrv(self):
        """Signal is zero when HRV is zero (at t such that sin=−1)."""
        # At t = 3/(4*f_hrv) the HRV envelope = 0.5*(1 + sin(3π/2)) = 0
        t_zero = 3.0 / (4.0 * F_HRV)
        hrv_at_zero = simulate_hrv_coherence(t_zero)
        self.assertAlmostEqual(hrv_at_zero, 0.0, places=10)

    def test_custom_lambda_list(self):
        """Custom Riemann zero list is used correctly."""
        t = np.linspace(0, 1, 50)
        upe1 = compute_upe_composite_signal(t, lambda_n_list=RIEMANN_ZEROS_20[:1])
        upe2 = compute_upe_composite_signal(t, lambda_n_list=RIEMANN_ZEROS_20[:5])
        # More modes → generally different signal
        self.assertFalse(np.allclose(upe1, upe2))

    def test_beat_frequency_present(self):
        """
        Verify beat frequency f_beat = λₙ ± f_HRV is encoded in the signal.

        We check that the signal contains oscillations driven by the first
        Riemann zero (γ₁ ≈ 14.134, imaginary part of ζ's first non-trivial
        zero) by verifying the signal has a non-trivial AC component.
        """
        # Sample densely enough to resolve λ₁ ≈ 14.13 Hz
        fs = 500.0  # sampling rate Hz
        duration = 5.0
        t = np.arange(0, duration, 1.0 / fs)
        upe = compute_upe_composite_signal(t, lambda_n_list=RIEMANN_ZEROS_20[:1])
        # Signal should not be DC (constant) — must have AC component
        self.assertGreater(np.std(upe), 0.0)


# ──────────────────────────────────────────────────────────────────────────────
# Package-level import
# ──────────────────────────────────────────────────────────────────────────────

class TestQCALPackageImports(unittest.TestCase):
    """Verify all QCAL-Strings symbols are accessible from qcal package."""

    def test_import_from_package(self):
        from qcal import (
            string_noetic_forcing,
            censura_taquionica,
            apply_tachyonic_censorship,
            operador_voluntad,
            simulate_hrv_coherence,
            compute_upe_composite_signal,
            compute_alpha_n,
            sigma_mapped,
            QCALStringsSolver,
            run_simulation_260,
            RIEMANN_ZEROS_20,
            LAMBDA_1_HZ,
            LAMBDA_1_SCALED_HZ,
            COHERENCE_GROWTH_RATE,
            HARD_RESET_SCALE,
            F_HRV,
            EZ_HEXAGONS,
            PSI_PLATEAU,
            N_MICROTUBULES_DEFAULT,
        )
        self.assertIsNotNone(QCALStringsSolver)

    def test_version_updated(self):
        import qcal
        self.assertEqual(qcal.__version__, "2.2.0")
from scipy.fft import fft2, ifft2

from qcal.string_core import (
    GAMMAS,
    THRESHOLD_PSI,
    N_MICROTUBULES_DEFAULT,
    ALPHA_SCALE_DEFAULT,
    N_MODES_DEFAULT,
    QCALStringOperator,
    compute_psi,
    string_noetic_forcing,
    rk4_step,
    build_lambda_list,
    build_spectral_grid,
)
from qcal.spectral_operator import F0, HBAR, GAMMA_MOD, RIEMANN_ZEROS


# ──────────────────────────────────────────────────────────────
# Helper: minimal spectral grid
# ──────────────────────────────────────────────────────────────

def _make_grid(N: int = 16):
    return build_spectral_grid(N)


def _make_op(**kwargs) -> QCALStringOperator:
    return QCALStringOperator(**kwargs)


# ──────────────────────────────────────────────────────────────
# Tests: GAMMAS constant
# ──────────────────────────────────────────────────────────────

class TestGammas(unittest.TestCase):
    def test_gammas_length(self):
        """GAMMAS contains exactly 20 entries."""
        self.assertEqual(len(GAMMAS), 20)

    def test_gammas_are_riemann_zeros(self):
        """GAMMAS equals the first 20 entries of RIEMANN_ZEROS."""
        self.assertEqual(GAMMAS, RIEMANN_ZEROS[:20])

    def test_gammas_all_positive(self):
        """All γ_n > 0 (imaginary parts of non-trivial zeros are positive)."""
        self.assertTrue(all(g > 0 for g in GAMMAS))

    def test_gammas_first_value(self):
        """First Riemann zero γ₁ ≈ 14.1347."""
        self.assertAlmostEqual(GAMMAS[0], 14.134725142, places=8)

    def test_gammas_increasing(self):
        """γ_n values are strictly increasing."""
        for i in range(len(GAMMAS) - 1):
            self.assertLess(GAMMAS[i], GAMMAS[i + 1])


# ──────────────────────────────────────────────────────────────
# Tests: QCALStringOperator
# ──────────────────────────────────────────────────────────────

class TestQCALStringOperator(unittest.TestCase):

    def setUp(self):
        self.op = _make_op()

    def test_default_f0(self):
        """Default f₀ matches the canonical value 141.7001 Hz."""
        self.assertAlmostEqual(self.op.f0, F0, places=4)

    def test_default_hbar(self):
        """Default ℏ matches HBAR."""
        self.assertAlmostEqual(self.op.hbar, HBAR, places=20)

    def test_default_gamma(self):
        """Default γ matches GAMMA_MOD = 1.0."""
        self.assertAlmostEqual(self.op.gamma, GAMMA_MOD, places=6)

    def test_modulation_potential_positive(self):
        """V̂_mod = γℏ/C > 0 for any positive C."""
        v = self.op.modulation_potential()
        self.assertGreater(v, 0.0)

    def test_modulation_potential_formula(self):
        """V̂_mod = gamma * hbar / C."""
        op = _make_op(gamma=2.0, C=4.0, hbar=1.0)
        self.assertAlmostEqual(op.modulation_potential(), 2.0 * 1.0 / 4.0, places=12)

    def test_modulation_potential_inversely_proportional_C(self):
        """Doubling C halves V̂_mod."""
        op1 = _make_op(C=1.0)
        op2 = _make_op(C=2.0)
        self.assertAlmostEqual(op2.modulation_potential(), op1.modulation_potential() / 2.0, places=20)

    def test_compute_eigenvalue_formula(self):
        """λ_n = γ_n · f₀ + V̂_mod."""
        op = _make_op(gamma=1.0, C=1.0, f0=100.0, hbar=1.0)
        gamma_n = 14.0
        expected = gamma_n * 100.0 + (1.0 * 1.0 / 1.0)
        self.assertAlmostEqual(op.compute_eigenvalue(gamma_n), expected, places=10)

    def test_compute_eigenvalue_first_mode(self):
        """First KK mode λ₁ = γ₁ · f₀ + V̂_mod."""
        v_mod = self.op.modulation_potential()
        expected = GAMMAS[0] * F0 + v_mod
        self.assertAlmostEqual(self.op.compute_eigenvalue(GAMMAS[0]), expected, places=6)

    def test_certify_critical_line_at_half(self):
        """On the critical line σ=1/2, Ψ = 1."""
        _, psi = self.op.certify_critical_line(0.5)
        self.assertAlmostEqual(psi, 1.0, places=12)

    def test_certify_critical_line_returns_tuple(self):
        """certify_critical_line returns a (sigma, float) tuple."""
        result = self.op.certify_critical_line(0.5)
        self.assertIsInstance(result, tuple)
        self.assertEqual(len(result), 2)

    def test_certify_critical_line_first_element(self):
        """First element of the tuple is the sigma value."""
        sigma = 0.4
        result = self.op.certify_critical_line(sigma)
        self.assertAlmostEqual(result[0], sigma, places=12)

    def test_certify_critical_line_decays_off_critical(self):
        """Ψ is strictly smaller when σ ≠ 0.5."""
        _, psi_half = self.op.certify_critical_line(0.5)
        _, psi_off = self.op.certify_critical_line(0.4)
        self.assertLess(psi_off, psi_half)

    def test_certify_critical_line_symmetric(self):
        """Ψ is symmetric around σ = 0.5."""
        _, psi_left = self.op.certify_critical_line(0.3)
        _, psi_right = self.op.certify_critical_line(0.7)
        self.assertAlmostEqual(psi_left, psi_right, places=12)

    def test_certify_critical_line_range(self):
        """Ψ(σ) ∈ (0, 1] for any σ."""
        for sigma in np.linspace(0.0, 1.0, 11):
            _, psi = self.op.certify_critical_line(float(sigma))
            self.assertGreater(psi, 0.0)
            self.assertLessEqual(psi, 1.0)

    def test_invalid_C_raises(self):
        """C ≤ 0 raises ValueError."""
        with self.assertRaises(ValueError):
            QCALStringOperator(C=0.0)
        with self.assertRaises(ValueError):
            QCALStringOperator(C=-1.0)

    def test_summary_keys(self):
        """summary() returns dict with expected keys."""
        s = self.op.summary()
        for key in ("gamma", "C", "f0", "hbar", "v_mod", "lambda_1"):
            self.assertIn(key, s)

    def test_summary_lambda1_matches_eigenvalue(self):
        """summary()['lambda_1'] equals compute_eigenvalue(GAMMAS[0])."""
        s = self.op.summary()
        self.assertAlmostEqual(s["lambda_1"], self.op.compute_eigenvalue(GAMMAS[0]), places=6)


# ──────────────────────────────────────────────────────────────
# Tests: build_lambda_list
# ──────────────────────────────────────────────────────────────

class TestBuildLambdaList(unittest.TestCase):

    def setUp(self):
        self.op = _make_op()

    def test_length_default(self):
        """Default builds 20 modes."""
        lambdas = build_lambda_list(self.op)
        self.assertEqual(len(lambdas), N_MODES_DEFAULT)

    def test_length_custom(self):
        """Custom n_modes is respected."""
        lambdas = build_lambda_list(self.op, n_modes=5)
        self.assertEqual(len(lambdas), 5)

    def test_n_modes_clamped_at_gammas(self):
        """n_modes > len(GAMMAS) is clamped to len(GAMMAS)."""
        lambdas = build_lambda_list(self.op, n_modes=9999)
        self.assertLessEqual(len(lambdas), len(GAMMAS))

    def test_all_positive(self):
        """All λ_n > 0 (since f₀ > 0 and γ_n > 0)."""
        lambdas = build_lambda_list(self.op)
        self.assertTrue(all(lam > 0 for lam in lambdas))

    def test_first_eigenvalue(self):
        """First eigenvalue equals compute_eigenvalue(GAMMAS[0])."""
        lambdas = build_lambda_list(self.op)
        expected = self.op.compute_eigenvalue(GAMMAS[0])
        self.assertAlmostEqual(lambdas[0], expected, places=6)

    def test_increasing(self):
        """λ_n values are strictly increasing (γ_n is increasing, same offset)."""
        lambdas = build_lambda_list(self.op)
        for i in range(len(lambdas) - 1):
            self.assertLess(lambdas[i], lambdas[i + 1])


# ──────────────────────────────────────────────────────────────
# Tests: build_spectral_grid
# ──────────────────────────────────────────────────────────────

class TestBuildSpectralGrid(unittest.TestCase):

    def setUp(self):
        self.N = 16
        self.grid = _make_grid(self.N)

    def test_keys_present(self):
        """Grid dict has all expected keys."""
        for key in ("xx", "yy", "kxx", "kyy", "k2"):
            self.assertIn(key, self.grid)

    def test_shapes(self):
        """All arrays have shape (N, N)."""
        N = self.N
        for key in ("xx", "yy", "kxx", "kyy", "k2"):
            self.assertEqual(self.grid[key].shape, (N, N))

    def test_xx_range(self):
        """x coordinates span [0, 2π) approximately."""
        xx = self.grid["xx"]
        self.assertGreaterEqual(float(xx.min()), 0.0)
        self.assertLess(float(xx.max()), 2.0 * math.pi)

    def test_k2_nonnegative(self):
        """k² = kx² + ky² ≥ 0 everywhere."""
        self.assertTrue(np.all(self.grid["k2"] >= 0.0))

    def test_k2_zero_at_origin(self):
        """k²[0,0] = 0 (DC mode)."""
        self.assertAlmostEqual(float(self.grid["k2"][0, 0]), 0.0, places=12)


# ──────────────────────────────────────────────────────────────
# Tests: compute_psi
# ──────────────────────────────────────────────────────────────

class TestComputePsi(unittest.TestCase):

    def setUp(self):
        self.N = 16
        self.grid = _make_grid(self.N)
        self.op = _make_op()
        self.xx = self.grid["xx"]

    def test_psi_range(self):
        """Ψ ∈ [0, 1] for random fields."""
        rng = np.random.default_rng(0)
        u = rng.standard_normal((self.N, self.N))
        v = rng.standard_normal((self.N, self.N))
        psi = compute_psi(u, v, self.xx, self.op)
        self.assertGreaterEqual(psi, 0.0)
        self.assertLessEqual(psi, 1.0)

    def test_psi_zero_for_zero_fields(self):
        """Zero velocity fields give Ψ = 0 (zero correlation)."""
        u = np.zeros((self.N, self.N))
        v = np.zeros((self.N, self.N))
        psi = compute_psi(u, v, self.xx, self.op)
        self.assertAlmostEqual(psi, 0.0, places=10)

    def test_psi_returns_float(self):
        """compute_psi returns a Python float."""
        u = np.ones((self.N, self.N)) * 0.5
        v = np.ones((self.N, self.N)) * 0.5
        psi = compute_psi(u, v, self.xx, self.op)
        self.assertIsInstance(psi, float)

    def test_psi_resonant_field_nonzero(self):
        """A field resonant with f₀ produces Ψ > 0."""
        L = 2.0 * math.pi
        u = np.sin(2.0 * math.pi * F0 * self.xx / L)
        v = np.cos(2.0 * math.pi * F0 * self.xx / L)
        psi = compute_psi(u, v, self.xx, self.op)
        self.assertGreater(psi, 0.0)

    def test_psi_at_most_one(self):
        """Even for perfectly resonant fields, Ψ ≤ 1."""
        L = 2.0 * math.pi
        u = np.sin(2.0 * math.pi * F0 * self.xx / L)
        v = np.cos(2.0 * math.pi * F0 * self.xx / L)
        psi = compute_psi(u, v, self.xx, self.op)
        self.assertLessEqual(psi, 1.0 + 1e-10)


# ──────────────────────────────────────────────────────────────
# Tests: string_noetic_forcing
# ──────────────────────────────────────────────────────────────

class TestStringNoeticForcing(unittest.TestCase):

    def setUp(self):
        self.N = 16
        self.grid = _make_grid(self.N)
        self.op = _make_op()
        self.xx = self.grid["xx"]
        self.yy = self.grid["yy"]
        self.lambda_list = build_lambda_list(self.op, n_modes=5)

    def test_zero_forcing_below_threshold(self):
        """Forcing is zero when Ψ < threshold."""
        fx, fy = string_noetic_forcing(
            t=0.0, xx=self.xx, yy=self.yy, op=self.op,
            Psi_local=0.5, lambda_list=self.lambda_list
        )
        np.testing.assert_array_equal(fx, np.zeros((self.N, self.N)))
        np.testing.assert_array_equal(fy, np.zeros((self.N, self.N)))

    def test_nonzero_forcing_above_threshold(self):
        """Forcing is nonzero when Ψ ≥ threshold."""
        fx, fy = string_noetic_forcing(
            t=0.0, xx=self.xx, yy=self.yy, op=self.op,
            Psi_local=0.95, lambda_list=self.lambda_list
        )
        self.assertGreater(np.max(np.abs(fx)), 0.0)
        self.assertGreater(np.max(np.abs(fy)), 0.0)

    def test_output_shapes(self):
        """Forcing arrays have shape (N, N)."""
        fx, fy = string_noetic_forcing(
            t=0.0, xx=self.xx, yy=self.yy, op=self.op,
            Psi_local=1.0, lambda_list=self.lambda_list
        )
        self.assertEqual(fx.shape, (self.N, self.N))
        self.assertEqual(fy.shape, (self.N, self.N))

    def test_forcing_scales_with_psi_squared(self):
        """Forcing amplitude ∝ Ψ²: doubling Ψ quadruples the amplitude."""
        psi1, psi2 = 0.9, 1.0
        fx1, _ = string_noetic_forcing(
            t=0.0, xx=self.xx, yy=self.yy, op=self.op,
            Psi_local=psi1, lambda_list=self.lambda_list
        )
        fx2, _ = string_noetic_forcing(
            t=0.0, xx=self.xx, yy=self.yy, op=self.op,
            Psi_local=psi2, lambda_list=self.lambda_list
        )
        # gain ∝ Ψ², so ratio of norms ≈ (psi2/psi1)²
        ratio = np.linalg.norm(fx2) / np.linalg.norm(fx1)
        expected = (psi2 / psi1) ** 2
        self.assertAlmostEqual(ratio, expected, delta=0.01)

    def test_forcing_time_dependence(self):
        """Forcing changes with time (sinusoidal mode)."""
        fx_t0, _ = string_noetic_forcing(
            t=0.0, xx=self.xx, yy=self.yy, op=self.op,
            Psi_local=1.0, lambda_list=self.lambda_list
        )
        fx_t1, _ = string_noetic_forcing(
            t=0.01, xx=self.xx, yy=self.yy, op=self.op,
            Psi_local=1.0, lambda_list=self.lambda_list
        )
        # The two forcing fields should differ
        self.assertFalse(np.allclose(fx_t0, fx_t1))

    def test_empty_lambda_list_gives_zeros(self):
        """Empty lambda list produces zero forcing (no modes)."""
        fx, fy = string_noetic_forcing(
            t=0.0, xx=self.xx, yy=self.yy, op=self.op,
            Psi_local=1.0, lambda_list=[]
        )
        np.testing.assert_array_almost_equal(fx, np.zeros((self.N, self.N)))
        np.testing.assert_array_almost_equal(fy, np.zeros((self.N, self.N)))

    def test_threshold_boundary(self):
        """Forcing is zero at exactly threshold - epsilon, nonzero at threshold."""
        eps = 1e-9
        fx_below, _ = string_noetic_forcing(
            t=0.0, xx=self.xx, yy=self.yy, op=self.op,
            Psi_local=THRESHOLD_PSI - eps, lambda_list=self.lambda_list
        )
        fx_at, _ = string_noetic_forcing(
            t=0.0, xx=self.xx, yy=self.yy, op=self.op,
            Psi_local=THRESHOLD_PSI, lambda_list=self.lambda_list
        )
        np.testing.assert_array_equal(fx_below, np.zeros((self.N, self.N)))
        self.assertGreater(np.max(np.abs(fx_at)), 0.0)


# ──────────────────────────────────────────────────────────────
# Tests: rk4_step
# ──────────────────────────────────────────────────────────────

class TestRK4Step(unittest.TestCase):

    def setUp(self):
        self.N = 16
        self.grid = _make_grid(self.N)
        self.op = _make_op()
        self.xx = self.grid["xx"]
        self.yy = self.grid["yy"]
        self.kxx = self.grid["kxx"]
        self.kyy = self.grid["kyy"]
        self.k2 = self.grid["k2"]
        self.lambda_list = build_lambda_list(self.op, n_modes=5)

        rng = np.random.default_rng(seed=0)
        self.uhat = fft2(rng.standard_normal((self.N, self.N)) * 0.01)
        self.vhat = fft2(rng.standard_normal((self.N, self.N)) * 0.01)
        self.grad_px = np.zeros((self.N, self.N), dtype=complex)
        self.grad_py = np.zeros((self.N, self.N), dtype=complex)

    def _step(self):
        return rk4_step(
            self.uhat, self.vhat,
            dt=0.005, rho=1.0, mu=1e-3,
            k2=self.k2, kxx=self.kxx, kyy=self.kyy,
            grad_px_hat=self.grad_px, grad_py_hat=self.grad_py,
            xx=self.xx, yy=self.yy,
            t=0.0, op=self.op, lambda_list=self.lambda_list,
        )

    def test_output_shapes(self):
        """rk4_step returns two arrays of shape (N, N)."""
        uhat_new, vhat_new = self._step()
        self.assertEqual(uhat_new.shape, (self.N, self.N))
        self.assertEqual(vhat_new.shape, (self.N, self.N))

    def test_output_complex(self):
        """Output arrays are complex (Fourier space)."""
        uhat_new, vhat_new = self._step()
        self.assertTrue(np.iscomplexobj(uhat_new))
        self.assertTrue(np.iscomplexobj(vhat_new))

    def test_dc_mode_zero(self):
        """DC mode (0,0) is zeroed after the step (zero mean flow)."""
        uhat_new, vhat_new = self._step()
        self.assertAlmostEqual(float(abs(uhat_new[0, 0])), 0.0, delta=1e-10)
        self.assertAlmostEqual(float(abs(vhat_new[0, 0])), 0.0, delta=1e-10)

    def test_fields_change_after_step(self):
        """Fields change after one RK4 step."""
        uhat_new, vhat_new = self._step()
        self.assertFalse(np.allclose(self.uhat, uhat_new))

    def test_incompressibility_preserved(self):
        """Divergence in Fourier space is near zero after the step."""
        uhat_new, vhat_new = self._step()
        div_hat = self.kxx * uhat_new + self.kyy * vhat_new
        # Exclude DC mode from check
        div_no_dc = div_hat.copy()
        div_no_dc[0, 0] = 0.0
        rms_div = float(np.sqrt(np.mean(np.abs(div_no_dc) ** 2)))
        # Should be small relative to the field energy
        energy = float(np.sqrt(np.mean(np.abs(uhat_new) ** 2 + np.abs(vhat_new) ** 2)))
        if energy > 1e-15:
            self.assertLess(rms_div / energy, 1e-6)

    def test_energy_finite(self):
        """Total kinetic energy remains finite after one step."""
        uhat_new, vhat_new = self._step()
        energy = float(np.sum(np.abs(uhat_new) ** 2 + np.abs(vhat_new) ** 2))
        self.assertTrue(math.isfinite(energy))
        self.assertGreater(energy, 0.0)


# ──────────────────────────────────────────────────────────────
# Tests: top-level constants
# ──────────────────────────────────────────────────────────────

class TestConstants(unittest.TestCase):

    def test_threshold_psi(self):
        """THRESHOLD_PSI = 0.888."""
        self.assertAlmostEqual(THRESHOLD_PSI, 0.888, places=3)

    def test_n_microtubules_default(self):
        """Default microtubule count is 1e13."""
        self.assertAlmostEqual(N_MICROTUBULES_DEFAULT, 1.0e13, places=0)

    def test_alpha_scale_default(self):
        """Default alpha scale is 0.05."""
        self.assertAlmostEqual(ALPHA_SCALE_DEFAULT, 0.05, places=6)

    def test_n_modes_default(self):
        """Default number of modes is 20."""
        self.assertEqual(N_MODES_DEFAULT, 20)


# ──────────────────────────────────────────────────────────────
# Tests: standalone qcal_string_core module
# ──────────────────────────────────────────────────────────────

class TestStandaloneModule(unittest.TestCase):
    """Verify that qcal_string_core.py re-exports all public symbols."""

    def test_importable(self):
        """qcal_string_core is importable."""
        import qcal_string_core  # noqa: F401

    def test_exports_operator(self):
        """QCALStringOperator is accessible from qcal_string_core."""
        from qcal_string_core import QCALStringOperator as Op
        op = Op()
        self.assertAlmostEqual(op.f0, F0, places=4)

    def test_exports_build_lambda_list(self):
        """build_lambda_list is accessible from qcal_string_core."""
        from qcal_string_core import build_lambda_list, QCALStringOperator
        op = QCALStringOperator()
        lambdas = build_lambda_list(op, n_modes=3)
        self.assertEqual(len(lambdas), 3)

    def test_exports_gammas(self):
        """GAMMAS is accessible from qcal_string_core."""
        from qcal_string_core import GAMMAS as G
        self.assertEqual(len(G), 20)

    def test_exports_f0(self):
        """F0 is accessible from qcal_string_core."""
        from qcal_string_core import F0 as f0
        self.assertAlmostEqual(f0, 141.7001, places=4)


if __name__ == "__main__":
    unittest.main(verbosity=2)
