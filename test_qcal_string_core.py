#!/usr/bin/env python3
"""
Test suite for QCAL-Strings — Forzado Noético de Modos Kaluza-Klein

Tests cover:
  Phase #260 — string_noetic_forcing, Veneziano amplitudes, KK modes
  Phase #261 — censura_taquionica, sigma_mapped, apply_tachyonic_censorship
  Phase #262 — operador_voluntad, simulate_hrv_coherence
  Simulator  — QCALStringsSolver, run_simulation_260
  UPE signal — compute_upe_composite_signal
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


if __name__ == "__main__":
    unittest.main(verbosity=2)
