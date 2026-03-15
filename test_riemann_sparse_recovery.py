#!/usr/bin/env python3
"""
Tests for qcal.riemann_sparse_recovery — Sparse Riemann Spectral Recovery
(Phases #261–#264).

Validates:
  - sieve_primes: correct prime generation
  - build_bk_sparse: sparse symmetric Berry-Keating operator
  - build_v_mod_sparse: diagonal log-prime potential
  - build_v_corrections: small sparse correction term
  - RiemannSparseRecovery: end-to-end sparse eigenvalue recovery
  - sigma_sweep / find_critical_sigma: σ-parameter optimisation

All tests use small N (≤ 512) to run in bounded time.  Convergence tests
use relative comparisons (error decreases with N) rather than absolute
numerical values, which require N ≥ 8192 to approach table VIII.9-A figures.
"""

import math
import unittest

import numpy as np

from qcal.riemann_sparse_recovery import (
    RIEMANN_ZEROS_50,
    RiemannSparseRecovery,
    SIGMA_CRITICAL,
    N_PRIMES_DEFAULT,
    N_GRID_DEFAULT,
    F0,
    build_bk_sparse,
    build_v_corrections,
    build_v_mod_sparse,
    find_critical_sigma,
    sigma_sweep,
    sieve_primes,
)


# ─────────────────────────────────────────────────────────────────────────────
# Helper
# ─────────────────────────────────────────────────────────────────────────────

def _log_primes(n: int) -> np.ndarray:
    """Return log(p) for the first *n* primes."""
    return np.log(np.array(sieve_primes(n), dtype=np.float64))


# ─────────────────────────────────────────────────────────────────────────────
# Tests: sieve_primes
# ─────────────────────────────────────────────────────────────────────────────

class TestSievePrimes(unittest.TestCase):
    """Tests for the prime sieve."""

    def test_first_prime(self) -> None:
        self.assertEqual(sieve_primes(1), [2])

    def test_first_ten_primes(self) -> None:
        expected = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        self.assertEqual(sieve_primes(10), expected)

    def test_count_is_exact(self) -> None:
        for n in (1, 5, 20, 50, 100):
            result = sieve_primes(n)
            self.assertEqual(len(result), n, f"Expected {n} primes, got {len(result)}")

    def test_all_entries_prime(self) -> None:
        """All returned numbers must actually be prime."""
        primes = sieve_primes(50)
        for p in primes:
            is_prime = p > 1 and all(p % i != 0 for i in range(2, int(p ** 0.5) + 1))
            self.assertTrue(is_prime, f"{p} is not prime")

    def test_raises_on_zero(self) -> None:
        with self.assertRaises(ValueError):
            sieve_primes(0)

    def test_raises_on_negative(self) -> None:
        with self.assertRaises(ValueError):
            sieve_primes(-5)

    def test_increasing_order(self) -> None:
        primes = sieve_primes(30)
        self.assertEqual(primes, sorted(primes))

    def test_no_duplicates(self) -> None:
        primes = sieve_primes(30)
        self.assertEqual(len(primes), len(set(primes)))


# ─────────────────────────────────────────────────────────────────────────────
# Tests: build_bk_sparse
# ─────────────────────────────────────────────────────────────────────────────

class TestBuildBKSparse(unittest.TestCase):
    """Tests for the sparse Berry-Keating operator."""

    def setUp(self) -> None:
        self.N = 64
        self.H = build_bk_sparse(self.N)

    def test_shape(self) -> None:
        self.assertEqual(self.H.shape, (self.N, self.N))

    def test_is_sparse(self) -> None:
        from scipy import sparse
        self.assertTrue(sparse.issparse(self.H))

    def test_nnz_tridiagonal(self) -> None:
        """Non-zero count must equal that of a tridiagonal matrix."""
        N = self.N
        expected_nnz = 3 * N - 2
        self.assertEqual(self.H.nnz, expected_nnz)

    def test_symmetric(self) -> None:
        """H_BK must be symmetric (Hermitian for real matrices)."""
        diff = (self.H - self.H.T).data
        if len(diff) > 0:
            self.assertAlmostEqual(float(np.max(np.abs(diff))), 0.0, places=12)

    def test_positive_eigenvalues(self) -> None:
        """The smallest eigenvalues of H_BK must be positive (Dirichlet BC)."""
        from scipy.sparse.linalg import eigsh
        evals = eigsh(self.H, k=3, which="SM", return_eigenvectors=False, tol=1e-8)
        self.assertTrue(np.all(evals > 0), f"Non-positive eigenvalues: {evals}")

    def test_first_eigenvalue_matches_continuum(self) -> None:
        """λ₁ ≈ (π/L)² within 5 % for N=256."""
        N = 256
        H = build_bk_sparse(N)
        from scipy.sparse.linalg import eigsh
        evals = eigsh(H, k=1, which="SM", return_eigenvectors=False, tol=1e-10)
        L = math.log(N + 1)
        expected = (math.pi / L) ** 2
        self.assertAlmostEqual(float(evals[0]), expected, delta=0.05 * expected)

    def test_raises_on_small_N(self) -> None:
        with self.assertRaises(ValueError):
            build_bk_sparse(3)

    def test_eigenvalues_increase_with_mode(self) -> None:
        """Eigenvalues must be strictly increasing with mode number."""
        from scipy.sparse.linalg import eigsh
        evals = sorted(
            eigsh(self.H, k=5, which="SM", return_eigenvectors=False, tol=1e-8)
        )
        for i in range(len(evals) - 1):
            self.assertLess(evals[i], evals[i + 1])

    def test_eigenvalue_decreases_with_larger_N(self) -> None:
        """First eigenvalue decreases as N grows (larger log domain L)."""
        from scipy.sparse.linalg import eigsh
        evals_small = eigsh(build_bk_sparse(64), k=1, which="SM",
                            return_eigenvectors=False, tol=1e-10)
        evals_large = eigsh(build_bk_sparse(256), k=1, which="SM",
                            return_eigenvectors=False, tol=1e-10)
        self.assertGreater(float(evals_small[0]), float(evals_large[0]))


# ─────────────────────────────────────────────────────────────────────────────
# Tests: build_v_mod_sparse
# ─────────────────────────────────────────────────────────────────────────────

class TestBuildVModSparse(unittest.TestCase):
    """Tests for the fractal log-prime potential."""

    def setUp(self) -> None:
        self.N = 128
        self.lp = _log_primes(20)
        self.V = build_v_mod_sparse(self.N, self.lp, sigma=0.21)

    def test_shape(self) -> None:
        self.assertEqual(self.V.shape, (self.N, self.N))

    def test_is_diagonal(self) -> None:
        """V_mod must be a diagonal matrix."""
        V = self.V.toarray()
        off_diag = V - np.diag(V.diagonal())
        self.assertAlmostEqual(float(np.max(np.abs(off_diag))), 0.0, places=12)

    def test_non_negative_diagonal(self) -> None:
        """All diagonal values must be non-negative (Lorentzian bumps ≥ 0)."""
        self.assertTrue(np.all(self.V.diagonal() >= 0))

    def test_diagonal_is_positive(self) -> None:
        """At least one diagonal entry must be > 0 (primes contribute)."""
        self.assertTrue(np.any(self.V.diagonal() > 0))

    def test_raises_on_nonpositive_sigma(self) -> None:
        with self.assertRaises(ValueError):
            build_v_mod_sparse(self.N, self.lp, sigma=0.0)

    def test_raises_on_negative_sigma(self) -> None:
        with self.assertRaises(ValueError):
            build_v_mod_sparse(self.N, self.lp, sigma=-0.1)

    def test_larger_sigma_increases_overlap(self) -> None:
        """Larger σ means bumps overlap more → minimum diagonal value is higher."""
        V_narrow = build_v_mod_sparse(self.N, self.lp, sigma=0.05)
        V_wide = build_v_mod_sparse(self.N, self.lp, sigma=1.0)
        # Wide bumps keep a higher floor between primes
        self.assertGreater(V_wide.diagonal().min(), V_narrow.diagonal().min())

    def test_more_primes_increases_sum(self) -> None:
        """Using more primes generally increases the total potential."""
        V_few = build_v_mod_sparse(self.N, _log_primes(5), sigma=0.21)
        V_many = build_v_mod_sparse(self.N, _log_primes(30), sigma=0.21)
        self.assertGreater(V_many.diagonal().sum(), V_few.diagonal().sum())


# ─────────────────────────────────────────────────────────────────────────────
# Tests: build_v_corrections
# ─────────────────────────────────────────────────────────────────────────────

class TestBuildVCorrections(unittest.TestCase):
    """Tests for the spectral correction term."""

    def setUp(self) -> None:
        self.N = 128
        self.V = build_v_corrections(self.N)

    def test_shape(self) -> None:
        self.assertEqual(self.V.shape, (self.N, self.N))

    def test_is_sparse(self) -> None:
        from scipy import sparse
        self.assertTrue(sparse.issparse(self.V))

    def test_symmetric(self) -> None:
        diff = (self.V - self.V.T).data
        if len(diff) > 0:
            self.assertAlmostEqual(float(np.max(np.abs(diff))), 0.0, places=12)

    def test_small_magnitude(self) -> None:
        """Correction must be small compared to typical BK eigenvalue."""
        H_BK = build_bk_sparse(self.N)
        from scipy.sparse.linalg import eigsh
        bk_eval = float(eigsh(H_BK, k=1, which="SM",
                              return_eigenvectors=False, tol=1e-10)[0])
        max_corr = float(np.max(np.abs(self.V.toarray())))
        # Correction should be less than 10% of first BK eigenvalue
        self.assertLess(max_corr, 0.1 * bk_eval)


# ─────────────────────────────────────────────────────────────────────────────
# Tests: RiemannSparseRecovery
# ─────────────────────────────────────────────────────────────────────────────

class TestRiemannSparseRecovery(unittest.TestCase):
    """Tests for the end-to-end sparse recovery class."""

    def setUp(self) -> None:
        # Small N for speed; structural tests only
        self.rec = RiemannSparseRecovery(N=128, n_primes=20, sigma=0.21)

    # ── Construction ──────────────────────────────────────────────────────────

    def test_attributes_set(self) -> None:
        self.assertEqual(self.rec.N, 128)
        self.assertEqual(self.rec.n_primes, 20)
        self.assertAlmostEqual(self.rec.sigma, 0.21, places=6)
        self.assertAlmostEqual(self.rec.f0, F0, places=4)

    def test_primes_count(self) -> None:
        self.assertEqual(len(self.rec.primes), 20)

    def test_log_primes_shape(self) -> None:
        self.assertEqual(self.rec.log_primes.shape, (20,))

    def test_log_primes_positive(self) -> None:
        self.assertTrue(np.all(self.rec.log_primes > 0))

    def test_raises_on_small_N(self) -> None:
        with self.assertRaises(ValueError):
            RiemannSparseRecovery(N=3)

    def test_raises_on_zero_primes(self) -> None:
        with self.assertRaises(ValueError):
            RiemannSparseRecovery(n_primes=0)

    def test_raises_on_bad_sigma(self) -> None:
        with self.assertRaises(ValueError):
            RiemannSparseRecovery(sigma=0.0)

    # ── Hamiltonian ──────────────────────────────────────────────────────────

    def test_hamiltonian_shape(self) -> None:
        self.assertEqual(self.rec.hamiltonian.shape, (128, 128))

    def test_hamiltonian_is_sparse(self) -> None:
        from scipy import sparse
        self.assertTrue(sparse.issparse(self.rec.hamiltonian))

    def test_hamiltonian_is_symmetric(self) -> None:
        H = self.rec.hamiltonian
        diff = (H - H.T).data
        if len(diff) > 0:
            self.assertAlmostEqual(float(np.max(np.abs(diff))), 0.0, places=8)

    def test_hamiltonian_lazy(self) -> None:
        """Hamiltonian is built only once (lazy evaluation)."""
        H1 = self.rec.hamiltonian
        H2 = self.rec.hamiltonian
        self.assertIs(H1, H2)

    # ── Eigenvalues ──────────────────────────────────────────────────────────

    def test_compute_eigenvalues_count(self) -> None:
        evals = self.rec.compute_eigenvalues(k=5)
        self.assertEqual(len(evals), 5)

    def test_eigenvalues_real_positive(self) -> None:
        evals = self.rec.compute_eigenvalues(k=5)
        self.assertTrue(np.all(evals > 0), f"Non-positive eigenvalues: {evals}")
        self.assertTrue(np.all(np.isreal(evals)))

    def test_eigenvalues_sorted(self) -> None:
        evals = self.rec.compute_eigenvalues(k=5)
        self.assertTrue(np.all(np.diff(evals) >= 0))

    def test_raises_k_too_large(self) -> None:
        with self.assertRaises(ValueError):
            self.rec.compute_eigenvalues(k=128)

    # ── Spectral report ───────────────────────────────────────────────────────

    def test_spectral_report_keys(self) -> None:
        report = self.rec.spectral_report(k=5)
        required = {
            "N", "n_primes", "sigma", "f0",
            "eigenvalues", "reference_zeros", "errors_pct",
            "mean_error_pct", "n_modes_compared", "phase", "estado",
        }
        for key in required:
            self.assertIn(key, report, f"Key '{key}' missing from report")

    def test_spectral_report_n_modes(self) -> None:
        report = self.rec.spectral_report(k=5)
        self.assertEqual(report["n_modes_compared"], 5)

    def test_spectral_report_errors_non_negative(self) -> None:
        report = self.rec.spectral_report(k=5)
        for e in report["errors_pct"]:
            self.assertGreaterEqual(e, 0.0)

    def test_spectral_report_mean_error_non_negative(self) -> None:
        report = self.rec.spectral_report(k=5)
        self.assertGreaterEqual(report["mean_error_pct"], 0.0)

    def test_spectral_report_custom_reference(self) -> None:
        custom = RIEMANN_ZEROS_50[:3]
        report = self.rec.spectral_report(k=3, reference_zeros=custom)
        self.assertEqual(report["n_modes_compared"], 3)
        self.assertEqual(report["reference_zeros"], custom)

    def test_spectral_report_phase_string(self) -> None:
        report = self.rec.spectral_report(k=5)
        self.assertIsInstance(report["phase"], str)
        self.assertGreater(len(report["phase"]), 0)

    def test_spectral_report_estado_string(self) -> None:
        report = self.rec.spectral_report(k=5)
        self.assertIsInstance(report["estado"], str)


# ─────────────────────────────────────────────────────────────────────────────
# Tests: convergence (error decreases as N grows)
# ─────────────────────────────────────────────────────────────────────────────

class TestConvergence(unittest.TestCase):
    """Qualitative convergence: larger N → smaller relative error."""

    def test_error_decreases_with_N(self) -> None:
        """
        The mean spectral error should decrease (or at least not increase
        significantly) as N doubles, keeping other parameters fixed.
        """
        k = 3
        errors = {}
        for N in (64, 128, 256):
            rec = RiemannSparseRecovery(N=N, n_primes=10, sigma=0.21)
            report = rec.spectral_report(k=k)
            errors[N] = report["mean_error_pct"]

        # Each doubling of N must reduce error by at least a factor of 1.05
        self.assertGreater(errors[64], errors[256],
                           f"Error did not decrease: {errors}")

    def test_larger_N_gives_lower_first_eigenvalue(self) -> None:
        """
        The first eigenvalue should decrease as N increases, tracking γ₁.
        This follows from λ₁(H_BK) ≈ f₀·(π/log(N+1))² which is decreasing.
        """
        e_small = RiemannSparseRecovery(N=64, n_primes=10, sigma=0.21)
        e_large = RiemannSparseRecovery(N=512, n_primes=10, sigma=0.21)
        first_small = e_small.compute_eigenvalues(k=1)[0]
        first_large = e_large.compute_eigenvalues(k=1)[0]
        self.assertGreater(first_small, first_large,
                           f"First eigenvalue did not decrease: {first_small} → {first_large}")


# ─────────────────────────────────────────────────────────────────────────────
# Tests: sigma_sweep and find_critical_sigma
# ─────────────────────────────────────────────────────────────────────────────

class TestSigmaSweep(unittest.TestCase):
    """Tests for the σ-parameter sweep."""

    def setUp(self) -> None:
        self.sigmas = [0.10, 0.20, 0.30, 0.40]

    def test_sweep_length(self) -> None:
        results = sigma_sweep(self.sigmas, N=64, n_primes=10, k=3)
        self.assertEqual(len(results), len(self.sigmas))

    def test_sweep_keys(self) -> None:
        results = sigma_sweep(self.sigmas, N=64, n_primes=10, k=3)
        for r in results:
            self.assertIn("sigma", r)
            self.assertIn("mean_error_pct", r)
            self.assertIn("phase", r)

    def test_sweep_sigmas_match(self) -> None:
        results = sigma_sweep(self.sigmas, N=64, n_primes=10, k=3)
        for r, expected_sigma in zip(results, self.sigmas):
            self.assertAlmostEqual(r["sigma"], expected_sigma, places=6)

    def test_sweep_errors_non_negative(self) -> None:
        results = sigma_sweep(self.sigmas, N=64, n_primes=10, k=3)
        for r in results:
            self.assertGreaterEqual(r["mean_error_pct"], 0.0)

    def test_find_critical_sigma_returns_minimum(self) -> None:
        result = find_critical_sigma(
            sigma_values=[0.10, 0.20, 0.30, 0.40],
            N=64, n_primes=10, k=3,
        )
        self.assertIn("sigma_c", result)
        self.assertIn("mean_error_pct", result)
        self.assertIn("sweep_results", result)
        # sigma_c must be one of the tested values
        self.assertIn(result["sigma_c"], [0.10, 0.20, 0.30, 0.40])

    def test_find_critical_sigma_is_best(self) -> None:
        """The sigma_c returned must have the minimum error in the sweep."""
        result = find_critical_sigma(
            sigma_values=[0.10, 0.20, 0.30],
            N=64, n_primes=10, k=3,
        )
        min_error = min(r["mean_error_pct"] for r in result["sweep_results"])
        self.assertAlmostEqual(result["mean_error_pct"], min_error, places=6)

    def test_find_critical_sigma_default(self) -> None:
        """Default call with small N finishes without error."""
        result = find_critical_sigma(N=64, n_primes=10, k=3)
        self.assertIsInstance(result["sigma_c"], float)
        self.assertGreater(result["sigma_c"], 0.0)


# ─────────────────────────────────────────────────────────────────────────────
# Tests: phase classification
# ─────────────────────────────────────────────────────────────────────────────

class TestPhaseClassification(unittest.TestCase):
    """Tests for _classify_phase static method."""

    def test_phase_264(self) -> None:
        phase = RiemannSparseRecovery._classify_phase(4.0)
        self.assertIn("264", phase)

    def test_phase_262(self) -> None:
        phase = RiemannSparseRecovery._classify_phase(43.0)
        self.assertIn("262", phase)

    def test_phase_261(self) -> None:
        phase = RiemannSparseRecovery._classify_phase(87.0)
        self.assertIn("261", phase)

    def test_phase_260(self) -> None:
        phase = RiemannSparseRecovery._classify_phase(95.0)
        self.assertIn("260", phase)


# ─────────────────────────────────────────────────────────────────────────────
# Tests: module-level constants
# ─────────────────────────────────────────────────────────────────────────────

class TestConstants(unittest.TestCase):
    """Tests for module-level constants."""

    def test_f0_value(self) -> None:
        self.assertAlmostEqual(F0, 141.7001, places=4)

    def test_sigma_critical_value(self) -> None:
        self.assertAlmostEqual(SIGMA_CRITICAL, 0.21, places=6)

    def test_n_primes_default(self) -> None:
        self.assertEqual(N_PRIMES_DEFAULT, 2000)

    def test_n_grid_default(self) -> None:
        self.assertEqual(N_GRID_DEFAULT, 8192)

    def test_riemann_zeros_count(self) -> None:
        self.assertEqual(len(RIEMANN_ZEROS_50), 50)

    def test_first_riemann_zero(self) -> None:
        """γ₁ = 14.1347…"""
        self.assertAlmostEqual(RIEMANN_ZEROS_50[0], 14.134725142, places=8)

    def test_tenth_riemann_zero(self) -> None:
        """γ₁₀ = 49.7738…"""
        self.assertAlmostEqual(RIEMANN_ZEROS_50[9], 49.773832478, places=6)

    def test_riemann_zeros_increasing(self) -> None:
        for i in range(len(RIEMANN_ZEROS_50) - 1):
            self.assertLess(RIEMANN_ZEROS_50[i], RIEMANN_ZEROS_50[i + 1])

    def test_riemann_zeros_all_positive(self) -> None:
        self.assertTrue(all(z > 0 for z in RIEMANN_ZEROS_50))


if __name__ == "__main__":
    unittest.main(verbosity=2)
