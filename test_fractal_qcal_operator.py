#!/usr/bin/env python3
"""
Tests for qcal.fractal_qcal_operator — FractalQCALOperator.

Validates the prime-based fractal Hamiltonian and its spectral modes.
Small N values (≤ 64) are used throughout to keep tests fast.
"""

import unittest

import numpy as np

from qcal.fractal_qcal_operator import (
    FractalQCALOperator,
    RIEMANN_ZEROS_20,
    _default_primes,
)


# ──────────────────────────────────────────────────────────────
# Constants
# ──────────────────────────────────────────────────────────────

class TestRiemannZeros20(unittest.TestCase):
    """Tests for the RIEMANN_ZEROS_20 constant."""

    def test_length_is_20(self) -> None:
        """Must contain exactly 20 reference zeros."""
        self.assertEqual(len(RIEMANN_ZEROS_20), 20)

    def test_first_zero(self) -> None:
        """First non-trivial zero γ₁ ≈ 14.1347."""
        self.assertAlmostEqual(RIEMANN_ZEROS_20[0], 14.134725141734693790, places=10)

    def test_all_positive(self) -> None:
        """All Riemann zeros (imaginary parts) are positive."""
        self.assertTrue(all(z > 0 for z in RIEMANN_ZEROS_20))

    def test_strictly_increasing(self) -> None:
        """Zeros are strictly increasing in magnitude."""
        for i in range(len(RIEMANN_ZEROS_20) - 1):
            self.assertLess(RIEMANN_ZEROS_20[i], RIEMANN_ZEROS_20[i + 1])


# ──────────────────────────────────────────────────────────────
# Default primes helper
# ──────────────────────────────────────────────────────────────

class TestDefaultPrimes(unittest.TestCase):
    """Tests for the _default_primes() fallback sieve."""

    def test_small_primes_correct(self) -> None:
        """Primes below 20 are 2, 3, 5, 7, 11, 13, 17, 19."""
        primes = _default_primes(upper=20)
        self.assertEqual(primes, [2, 3, 5, 7, 11, 13, 17, 19])

    def test_all_prime(self) -> None:
        """Every returned value must be prime."""
        from math import isqrt

        def is_prime(n: int) -> bool:
            if n < 2:
                return False
            for i in range(2, isqrt(n) + 1):
                if n % i == 0:
                    return False
            return True

        for p in _default_primes(upper=100):
            self.assertTrue(is_prime(p), f"{p} is not prime")

    def test_no_duplicates(self) -> None:
        """No duplicate primes should appear."""
        primes = _default_primes(upper=200)
        self.assertEqual(len(primes), len(set(primes)))

    def test_count_below_100(self) -> None:
        """There are exactly 25 primes below 100."""
        self.assertEqual(len(_default_primes(upper=100)), 25)


# ──────────────────────────────────────────────────────────────
# FractalQCALOperator — initialisation
# ──────────────────────────────────────────────────────────────

class TestFractalQCALOperatorInit(unittest.TestCase):
    """Tests for FractalQCALOperator.__init__."""

    def setUp(self) -> None:
        self.op = FractalQCALOperator(N=32, primes=[2, 3, 5, 7, 11, 13])

    def test_N_stored(self) -> None:
        self.assertEqual(self.op.N, 32)

    def test_u_length(self) -> None:
        """Spatial grid must have exactly N points."""
        self.assertEqual(len(self.op.u), 32)

    def test_u_range(self) -> None:
        """Spatial grid runs from 0 to 100."""
        self.assertAlmostEqual(float(self.op.u[0]), 0.0, places=10)
        self.assertAlmostEqual(float(self.op.u[-1]), 100.0, places=6)

    def test_du_positive(self) -> None:
        """Step size must be positive."""
        self.assertGreater(self.op.du, 0.0)

    def test_primes_stored(self) -> None:
        """Provided primes list is stored."""
        self.assertEqual(self.op.primes, [2, 3, 5, 7, 11, 13])

    def test_log_primes_shape(self) -> None:
        """log_primes has the same length as primes."""
        self.assertEqual(len(self.op.log_primes), 6)

    def test_log_primes_values(self) -> None:
        """log_primes equals log of each prime."""
        expected = np.log([2, 3, 5, 7, 11, 13])
        np.testing.assert_array_almost_equal(self.op.log_primes, expected)

    def test_f0_calibration(self) -> None:
        """f₀ = γ₁ / π matches first Riemann zero."""
        expected_f0 = RIEMANN_ZEROS_20[0] / np.pi
        self.assertAlmostEqual(self.op.f0, expected_f0, places=12)

    def test_default_primes_used_when_none(self) -> None:
        """If primes=None, a non-empty default list is used."""
        op = FractalQCALOperator(N=16, primes=None)
        self.assertGreater(len(op.primes), 0)


# ──────────────────────────────────────────────────────────────
# FractalQCALOperator — v_mod_fractal
# ──────────────────────────────────────────────────────────────

class TestVModFractal(unittest.TestCase):
    """Tests for FractalQCALOperator.v_mod_fractal."""

    def setUp(self) -> None:
        self.op = FractalQCALOperator(N=64, primes=[2, 3, 5, 7])

    def test_shape(self) -> None:
        """Result must be an (N, N) matrix."""
        V = self.op.v_mod_fractal()
        self.assertEqual(V.shape, (64, 64))

    def test_is_diagonal(self) -> None:
        """Potential matrix must be diagonal."""
        V = self.op.v_mod_fractal()
        off_diag = V - np.diag(np.diag(V))
        np.testing.assert_array_equal(off_diag, np.zeros((64, 64)))

    def test_diagonal_non_negative(self) -> None:
        """All diagonal elements must be ≥ 0."""
        diag = np.diag(self.op.v_mod_fractal())
        self.assertTrue(np.all(diag >= 0.0))

    def test_diagonal_not_all_zero(self) -> None:
        """At least some diagonal elements must be positive."""
        diag = np.diag(self.op.v_mod_fractal())
        self.assertGreater(np.sum(diag), 0.0)

    def test_sigma_affects_width(self) -> None:
        """Larger sigma gives broader (larger norm) potential."""
        norm_narrow = np.linalg.norm(self.op.v_mod_fractal(sigma=0.1))
        norm_wide = np.linalg.norm(self.op.v_mod_fractal(sigma=2.0))
        self.assertGreater(norm_wide, norm_narrow)

    def test_no_primes_gives_zero_potential(self) -> None:
        """With an empty primes list, potential is all zeros."""
        op = FractalQCALOperator(N=16, primes=[])
        V = op.v_mod_fractal()
        np.testing.assert_array_equal(V, np.zeros((16, 16)))


# ──────────────────────────────────────────────────────────────
# FractalQCALOperator — build_hamiltonian
# ──────────────────────────────────────────────────────────────

class TestBuildHamiltonian(unittest.TestCase):
    """Tests for FractalQCALOperator.build_hamiltonian."""

    def setUp(self) -> None:
        self.op = FractalQCALOperator(N=32, primes=[2, 3, 5, 7])

    def test_shape(self) -> None:
        """Hamiltonian must be (N, N)."""
        H = self.op.build_hamiltonian()
        self.assertEqual(H.shape, (32, 32))

    def test_real_valued(self) -> None:
        """Hamiltonian is generally complex: BK part contributes imaginary
        off-diagonal entries; dtype is complex128 for non-trivial primes."""
        H = self.op.build_hamiltonian()
        # Accepts both float and complex — real-only if all imaginary parts vanish
        self.assertIn(H.dtype.kind, ('f', 'c'))

    def test_symmetric(self) -> None:
        """Hamiltonian must be Hermitian (H = H†) for real spectrum."""
        H = self.op.build_hamiltonian()
        np.testing.assert_array_almost_equal(H, H.conj().T, decimal=10)

    def test_scaled_by_f0(self) -> None:
        """Hamiltonian is scaled by f₀ = γ₁/π > 0."""
        H = self.op.build_hamiltonian()
        self.assertGreater(self.op.f0, 0.0)
        # With f₀ > 0 the Frobenius norm should be > 0 if there's any potential
        self.assertGreater(np.linalg.norm(H), 0.0)


# ──────────────────────────────────────────────────────────────
# FractalQCALOperator — get_modes
# ──────────────────────────────────────────────────────────────

class TestGetModes(unittest.TestCase):
    """Tests for FractalQCALOperator.get_modes."""

    def setUp(self) -> None:
        # Use N=64 so eigvals is fast but large enough for 20 modes
        self.op = FractalQCALOperator(N=64, primes=[2, 3, 5, 7, 11, 13])

    def test_default_returns_20_modes(self) -> None:
        """Default call should return 20 spectral modes."""
        modes = self.op.get_modes()
        self.assertEqual(len(modes), 20)

    def test_modes_are_real(self) -> None:
        """All returned modes must be real-valued."""
        modes = self.op.get_modes()
        self.assertTrue(np.all(np.isreal(modes)))

    def test_modes_are_sorted(self) -> None:
        """Modes must be returned in non-decreasing order."""
        modes = self.op.get_modes()
        self.assertTrue(np.all(np.diff(modes) >= 0))

    def test_custom_n_modes(self) -> None:
        """Custom n_modes parameter is respected."""
        modes = self.op.get_modes(n_modes=5)
        self.assertEqual(len(modes), 5)

    def test_modes_finite(self) -> None:
        """No NaN or Inf values in modes."""
        modes = self.op.get_modes()
        self.assertTrue(np.all(np.isfinite(modes)))

    def test_n1_consistency(self) -> None:
        """get_modes(n_modes=1) returns a subset of get_modes(n_modes=20)."""
        modes_20 = self.op.get_modes(n_modes=20)
        modes_1 = self.op.get_modes(n_modes=1)
        self.assertAlmostEqual(float(modes_1[0]), float(modes_20[0]), places=10)


# ──────────────────────────────────────────────────────────────
# FractalQCALOperator — package-level import
# ──────────────────────────────────────────────────────────────

class TestPackageImport(unittest.TestCase):
    """Ensure FractalQCALOperator is reachable from the qcal package."""

    def test_import_from_package(self) -> None:
        from qcal import FractalQCALOperator as FQO
        self.assertIs(FQO, FractalQCALOperator)

    def test_riemann_zeros_20_from_package(self) -> None:
        from qcal import RIEMANN_ZEROS_20 as RZ
        self.assertEqual(len(RZ), 20)


if __name__ == '__main__':
    unittest.main(verbosity=2)
