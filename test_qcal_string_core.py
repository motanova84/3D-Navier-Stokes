#!/usr/bin/env python3
"""
Tests for qcal.string_core — QCAL-Strings Iteración #260.

Validates QCALStringOperator, string_noetic_forcing, compute_psi,
rk4_step, build_lambda_list, and build_spectral_grid.
"""

import math
import unittest

import numpy as np
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
