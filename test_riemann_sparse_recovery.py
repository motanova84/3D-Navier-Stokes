#!/usr/bin/env python3
"""
Tests para QCAL-Strings — Módulo riemann_sparse_recovery
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Pruebas unitarias para qcal.riemann_sparse_recovery:
- build_bk_sparse: Hamiltoniano Berry-Keating
- build_vmod_sparse: Potencial log-primo
- build_sparse_hamiltonian: Hamiltoniano completo
- extract_eigenvalues: Extracción de autovalores
- compute_spectral_errors: Errores espectrales
- recover_riemann_spectrum: API de alto nivel

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
License: MIT
"""

import unittest
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).parent))

from qcal.riemann_sparse_recovery import (
    build_bk_sparse,
    build_vmod_sparse,
    build_sparse_hamiltonian,
    extract_eigenvalues,
    compute_spectral_errors,
    recover_riemann_spectrum,
    _get_first_n_primes,
    SIGMA_CRITICAL,
    N_PRIMES_DEFAULT,
    N_GRID_DEFAULT,
    F0,
    RIEMANN_ZEROS,
)

try:
    from scipy import sparse
    _SCIPY = True
except ImportError:
    _SCIPY = False


# ─────────────────────────────────────────────────────────────────────────────
# Tests: constantes
# ─────────────────────────────────────────────────────────────────────────────

class TestModuleConstants(unittest.TestCase):

    def test_f0(self):
        self.assertAlmostEqual(F0, 141.7001, places=4)

    def test_sigma_critical(self):
        self.assertAlmostEqual(SIGMA_CRITICAL, 0.21, places=4)

    def test_n_primes_default(self):
        self.assertEqual(N_PRIMES_DEFAULT, 2000)

    def test_n_grid_default(self):
        self.assertEqual(N_GRID_DEFAULT, 8192)

    def test_riemann_zeros_length(self):
        self.assertEqual(len(RIEMANN_ZEROS), 50)

    def test_riemann_zeros_first(self):
        self.assertAlmostEqual(RIEMANN_ZEROS[0], 14.134725, places=4)


# ─────────────────────────────────────────────────────────────────────────────
# Tests: generación de primos
# ─────────────────────────────────────────────────────────────────────────────

class TestGetFirstNPrimes(unittest.TestCase):

    def test_empty(self):
        self.assertEqual(_get_first_n_primes(0), [])

    def test_first_5(self):
        primes = _get_first_n_primes(5)
        self.assertEqual(primes, [2, 3, 5, 7, 11])

    def test_count(self):
        for n in [1, 10, 50]:
            primes = _get_first_n_primes(n)
            self.assertEqual(len(primes), n)

    def test_all_prime(self):
        import math
        primes = _get_first_n_primes(20)
        for p in primes:
            is_prime = p > 1 and all(p % i != 0 for i in range(2, int(math.sqrt(p)) + 1))
            self.assertTrue(is_prime, f"{p} no es primo")


# ─────────────────────────────────────────────────────────────────────────────
# Tests: build_bk_sparse
# ─────────────────────────────────────────────────────────────────────────────

@unittest.skipUnless(_SCIPY, "scipy no disponible")
class TestBuildBKSparseRecovery(unittest.TestCase):

    def test_shape(self):
        for N in [16, 32, 64]:
            H = build_bk_sparse(N)
            self.assertEqual(H.shape, (N, N))

    def test_sparse_type(self):
        H = build_bk_sparse(32)
        self.assertTrue(sparse.issparse(H))

    def test_csr_format(self):
        H = build_bk_sparse(32)
        self.assertEqual(H.format, "csr")

    def test_no_nan(self):
        H = build_bk_sparse(32)
        self.assertFalse(np.any(np.isnan(H.data)))

    def test_no_inf(self):
        H = build_bk_sparse(32)
        self.assertFalse(np.any(np.isinf(H.data)))

    def test_bandwidth_3(self):
        # BK es tridiagonal: sólo diagonal ±1
        N = 16
        H = build_bk_sparse(N)
        H_dense = H.toarray()
        for i in range(N):
            for j in range(N):
                if abs(i - j) > 1:
                    self.assertAlmostEqual(H_dense[i, j], 0.0, places=10,
                                           msg=f"H[{i},{j}] != 0")


# ─────────────────────────────────────────────────────────────────────────────
# Tests: build_vmod_sparse
# ─────────────────────────────────────────────────────────────────────────────

@unittest.skipUnless(_SCIPY, "scipy no disponible")
class TestBuildVmodSparseRecovery(unittest.TestCase):

    def setUp(self):
        import math
        primes = [2, 3, 5, 7, 11, 13]
        self.log_primes = np.array([math.log(p) for p in primes])

    def test_shape(self):
        V = build_vmod_sparse(32, self.log_primes)
        self.assertEqual(V.shape, (32, 32))

    def test_diagonal_positive(self):
        V = build_vmod_sparse(32, self.log_primes)
        self.assertTrue(np.all(V.diagonal() >= 0))

    def test_off_diagonal_zero(self):
        N = 16
        V = build_vmod_sparse(N, self.log_primes)
        V_dense = V.toarray()
        for i in range(N):
            for j in range(N):
                if i != j:
                    self.assertAlmostEqual(V_dense[i, j], 0.0, places=10)

    def test_sigma_scales_values(self):
        # Wider sigma spreads Gaussian peaks → generally larger maximum values
        V_narrow = build_vmod_sparse(32, self.log_primes, sigma=0.01)
        V_wide = build_vmod_sparse(32, self.log_primes, sigma=1.0)
        max_narrow = float(np.max(V_narrow.diagonal()))
        max_wide = float(np.max(V_wide.diagonal()))
        self.assertGreater(max_wide, max_narrow)


# ─────────────────────────────────────────────────────────────────────────────
# Tests: build_sparse_hamiltonian
# ─────────────────────────────────────────────────────────────────────────────

@unittest.skipUnless(_SCIPY, "scipy no disponible")
class TestBuildSparseHamiltonian(unittest.TestCase):

    def test_shape(self):
        N = 64
        H = build_sparse_hamiltonian(N=N, n_primes=16)
        self.assertEqual(H.shape, (N, N))

    def test_sparse(self):
        H = build_sparse_hamiltonian(N=32, n_primes=16)
        self.assertTrue(sparse.issparse(H))

    def test_f0_scaling(self):
        H1 = build_sparse_hamiltonian(N=32, n_primes=8, f0=1.0)
        H2 = build_sparse_hamiltonian(N=32, n_primes=8, f0=2.0)
        # H2 debe ser aprox 2x H1 en magnitud (antes de la perturbación GUE)
        scale1 = float(np.max(np.abs(H1.data)))
        scale2 = float(np.max(np.abs(H2.data)))
        self.assertGreater(scale2, scale1)


# ─────────────────────────────────────────────────────────────────────────────
# Tests: extract_eigenvalues
# ─────────────────────────────────────────────────────────────────────────────

@unittest.skipUnless(_SCIPY, "scipy no disponible")
class TestExtractEigenvalues(unittest.TestCase):

    def setUp(self):
        self.H = build_sparse_hamiltonian(N=64, n_primes=16)

    def test_count(self):
        k = 5
        evals = extract_eigenvalues(self.H, k=k)
        self.assertEqual(len(evals), k)

    def test_sorted(self):
        evals = extract_eigenvalues(self.H, k=5)
        self.assertTrue(np.all(np.diff(evals) >= 0))

    def test_positive(self):
        evals = extract_eigenvalues(self.H, k=5)
        self.assertTrue(np.all(evals > 0))

    def test_finite(self):
        evals = extract_eigenvalues(self.H, k=5)
        self.assertTrue(np.all(np.isfinite(evals)))


# ─────────────────────────────────────────────────────────────────────────────
# Tests: compute_spectral_errors
# ─────────────────────────────────────────────────────────────────────────────

class TestComputeSpectralErrors(unittest.TestCase):

    def test_perfect_match(self):
        ref = [14.134725, 21.022040, 25.010858]
        evals = np.array(ref)
        result = compute_spectral_errors(evals, reference=ref)
        self.assertAlmostEqual(result["mean_error_pct"], 0.0, places=3)

    def test_10pct_error(self):
        ref = [10.0, 20.0, 30.0]
        evals = np.array([11.0, 22.0, 33.0])
        result = compute_spectral_errors(evals, reference=ref)
        self.assertAlmostEqual(result["mean_error_pct"], 10.0, places=2)

    def test_keys(self):
        result = compute_spectral_errors(np.array([14.0, 21.0]),
                                          reference=[14.134725, 21.022040])
        for key in ["errors_pct", "mean_error_pct", "max_error_pct", "estado"]:
            self.assertIn(key, result)

    def test_estado_anclaje(self):
        ref = [14.134725]
        evals = np.array([14.134725])
        result = compute_spectral_errors(evals, reference=ref)
        self.assertEqual(result["estado"], "ANCLAJE-INMUTABLE")

    def test_estado_convergiendo(self):
        ref = [14.134725]
        evals = np.array([20.0])  # >5% error
        result = compute_spectral_errors(evals, reference=ref)
        self.assertEqual(result["estado"], "CONVERGIENDO")

    def test_default_reference(self):
        evals = np.array(RIEMANN_ZEROS[:5])
        result = compute_spectral_errors(evals)
        self.assertAlmostEqual(result["mean_error_pct"], 0.0, places=3)


# ─────────────────────────────────────────────────────────────────────────────
# Tests: recover_riemann_spectrum (integración)
# ─────────────────────────────────────────────────────────────────────────────

@unittest.skipUnless(_SCIPY, "scipy no disponible")
class TestRecoverRiemannSpectrum(unittest.TestCase):

    def test_returns_dict(self):
        result = recover_riemann_spectrum(N=64, n_primes=16, k=3)
        self.assertIsInstance(result, dict)

    def test_required_keys(self):
        result = recover_riemann_spectrum(N=64, n_primes=16, k=3)
        for key in ["eigenvalues", "errors_pct", "mean_error_pct",
                    "max_error_pct", "estado", "N", "n_primes", "sigma", "f0"]:
            self.assertIn(key, result)

    def test_eigenvalues_count(self):
        k = 3
        result = recover_riemann_spectrum(N=64, n_primes=16, k=k)
        self.assertEqual(len(result["eigenvalues"]), k)

    def test_metadata(self):
        result = recover_riemann_spectrum(N=64, n_primes=16, k=3, f0=F0)
        self.assertEqual(result["N"], 64)
        self.assertEqual(result["n_primes"], 16)
        self.assertAlmostEqual(result["f0"], F0, places=4)


if __name__ == "__main__":
    unittest.main(verbosity=2)
