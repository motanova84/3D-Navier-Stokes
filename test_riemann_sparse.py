#!/usr/bin/env python3
"""
Tests para QCAL-Strings — Recuperación Espectral Sparse de Riemann (#261–#264)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Pruebas unitarias para qcal.riemann_sparse:
- Construcción del Hamiltoniano Berry-Keating sparse
- Potencial V_mod log-primo
- RiemannSparseRecovery: extracción de autovalores
- Barrido de sigma (punto dulce espectral)
- Certificación Fase #264 (error < 5%)

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
License: MIT
"""

import unittest
import math
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).parent))

from qcal.riemann_sparse import (
    build_bk_sparse,
    build_vmod_sparse,
    build_vcorrections_sparse,
    RiemannSparseRecovery,
    sigma_sweep,
    certificar_fase264,
    SIGMA_C,
    F0,
    N_MODES,
    ERROR_ANCLAJE,
    RIEMANN_ZEROS_50,
    _sieve_primes,
    _get_primes,
)

try:
    from scipy import sparse
    _SCIPY = True
except ImportError:
    _SCIPY = False


# ─────────────────────────────────────────────────────────────────────────────
# Tests: constantes
# ─────────────────────────────────────────────────────────────────────────────

class TestConstants(unittest.TestCase):

    def test_f0(self):
        self.assertAlmostEqual(F0, 141.7001, places=4)

    def test_sigma_c(self):
        self.assertAlmostEqual(SIGMA_C, 0.21, places=4)

    def test_n_modes(self):
        self.assertEqual(N_MODES, 50)

    def test_error_anclaje(self):
        self.assertAlmostEqual(ERROR_ANCLAJE, 5.0, places=1)

    def test_riemann_zeros_length(self):
        self.assertEqual(len(RIEMANN_ZEROS_50), 50)

    def test_riemann_zeros_first(self):
        self.assertAlmostEqual(RIEMANN_ZEROS_50[0], 14.134725, places=4)

    def test_riemann_zeros_tenth(self):
        self.assertAlmostEqual(RIEMANN_ZEROS_50[9], 49.773832, places=4)


# ─────────────────────────────────────────────────────────────────────────────
# Tests: criba de primos
# ─────────────────────────────────────────────────────────────────────────────

class TestPrimes(unittest.TestCase):

    def test_sieve_small(self):
        primes = _sieve_primes(10)
        self.assertEqual(primes, [2, 3, 5, 7])

    def test_sieve_limit_1(self):
        primes = _sieve_primes(1)
        self.assertEqual(primes, [])

    def test_get_primes_10(self):
        primes = _get_primes(10)
        self.assertEqual(len(primes), 10)
        self.assertEqual(primes[0], 2)
        self.assertEqual(primes[-1], 29)

    def test_get_primes_128(self):
        primes = _get_primes(128)
        self.assertEqual(len(primes), 128)
        self.assertTrue(all(isinstance(p, int) for p in primes))

    def test_get_primes_zero(self):
        primes = _get_primes(0)
        self.assertEqual(primes, [])


# ─────────────────────────────────────────────────────────────────────────────
# Tests: construcción del Hamiltoniano
# ─────────────────────────────────────────────────────────────────────────────

@unittest.skipUnless(_SCIPY, "scipy no disponible")
class TestBuildBKSparse(unittest.TestCase):

    def test_shape(self):
        N = 32
        H = build_bk_sparse(N)
        self.assertEqual(H.shape, (N, N))

    def test_is_sparse(self):
        H = build_bk_sparse(64)
        self.assertTrue(sparse.issparse(H))

    def test_tridiagonal_structure(self):
        N = 16
        H = build_bk_sparse(N)
        H_dense = H.toarray()
        # Solo diagonal y vecinos deben ser no cero
        for i in range(N):
            for j in range(N):
                if abs(i - j) > 1:
                    self.assertAlmostEqual(H_dense[i, j], 0.0, places=10)

    def test_dtype_float(self):
        H = build_bk_sparse(16)
        self.assertEqual(H.dtype, float)

    def test_no_nan(self):
        H = build_bk_sparse(32)
        self.assertFalse(np.any(np.isnan(H.data)))

    def test_diagonal_mostly_positive(self):
        # Interior elements should be positive; boundary can differ due to
        # periodic conditions in the log-mesh construction
        N = 16
        H = build_bk_sparse(N)
        diag = H.diagonal()
        # At least the interior elements (excluding first and last) are positive
        self.assertTrue(np.all(diag[1:-1] > 0))


@unittest.skipUnless(_SCIPY, "scipy no disponible")
class TestBuildVmodSparse(unittest.TestCase):

    def test_shape(self):
        N = 32
        primes = [2, 3, 5, 7, 11]
        V = build_vmod_sparse(N, primes, sigma=0.21)
        self.assertEqual(V.shape, (N, N))

    def test_diagonal_only(self):
        N = 16
        primes = [2, 3, 5]
        V = build_vmod_sparse(N, primes)
        V_dense = V.toarray()
        for i in range(N):
            for j in range(N):
                if i != j:
                    self.assertAlmostEqual(V_dense[i, j], 0.0, places=10)

    def test_positive_values(self):
        N = 32
        primes = list(range(2, 20, 2))  # algunos valores
        primes = [p for p in [2, 3, 5, 7, 11, 13, 17, 19] if p]
        V = build_vmod_sparse(N, primes)
        self.assertTrue(np.all(V.diagonal() >= 0))

    def test_normalization(self):
        N = 32
        primes_few = [2, 3]
        primes_many = list(range(2, 50, 2))
        primes_many = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        V_few = build_vmod_sparse(N, primes_few)
        V_many = build_vmod_sparse(N, primes_many)
        # Con más primos, la escala no debe dispararse gracias a la normalización
        max_few = float(np.max(np.abs(V_few.diagonal())))
        max_many = float(np.max(np.abs(V_many.diagonal())))
        # Ambos deben ser comparables (normalización por P)
        self.assertLess(max_many, max_few * 10)


@unittest.skipUnless(_SCIPY, "scipy no disponible")
class TestBuildVCorrectionsSparse(unittest.TestCase):

    def test_shape(self):
        V = build_vcorrections_sparse(32)
        self.assertEqual(V.shape, (32, 32))

    def test_reproducible(self):
        V1 = build_vcorrections_sparse(16, alpha=0.01)
        V2 = build_vcorrections_sparse(16, alpha=0.01)
        np.testing.assert_array_equal(V1.diagonal(), V2.diagonal())

    def test_alpha_scaling(self):
        V1 = build_vcorrections_sparse(16, alpha=0.01)
        V2 = build_vcorrections_sparse(16, alpha=0.1)
        max1 = float(np.max(np.abs(V1.diagonal())))
        max2 = float(np.max(np.abs(V2.diagonal())))
        self.assertGreater(max2, max1)


# ─────────────────────────────────────────────────────────────────────────────
# Tests: RiemannSparseRecovery
# ─────────────────────────────────────────────────────────────────────────────

@unittest.skipUnless(_SCIPY, "scipy no disponible")
class TestRiemannSparseRecovery(unittest.TestCase):
    """Tests de recuperación espectral con N pequeño para velocidad."""

    def setUp(self):
        # N pequeño para tests rápidos
        self.rec = RiemannSparseRecovery(N=256, n_primes=64, sigma=0.21, alpha=0.01)

    def test_instantiation(self):
        self.assertEqual(self.rec.N, 256)
        self.assertEqual(self.rec.n_primes, 64)
        self.assertAlmostEqual(self.rec.sigma, 0.21, places=4)

    def test_recover_returns_dict(self):
        result = self.rec.recover(n_modes=5)
        self.assertIsInstance(result, dict)

    def test_recover_keys(self):
        result = self.rec.recover(n_modes=5)
        required_keys = [
            "eigenvalues", "riemann_zeros", "errors_pct",
            "mean_error_pct", "max_error_pct", "estado",
            "N", "n_primes", "sigma"
        ]
        for key in required_keys:
            self.assertIn(key, result)

    def test_eigenvalues_shape(self):
        n = 5
        result = self.rec.recover(n_modes=n)
        self.assertEqual(len(result["eigenvalues"]), n)

    def test_eigenvalues_positive(self):
        result = self.rec.recover(n_modes=5)
        self.assertTrue(np.all(result["eigenvalues"] > 0))

    def test_errors_pct_positive(self):
        result = self.rec.recover(n_modes=5)
        self.assertTrue(np.all(result["errors_pct"] >= 0))

    def test_estado_values(self):
        result = self.rec.recover(n_modes=5)
        self.assertIn(result["estado"], ["ANCLAJE-INMUTABLE", "CONVERGIENDO"])

    def test_hamiltonian_cached(self):
        # Segunda llamada usa caché
        self.rec.recover(n_modes=3)
        H_first = self.rec._H
        self.rec.recover(n_modes=3)
        H_second = self.rec._H
        self.assertIs(H_first, H_second)

    def test_metadata_in_result(self):
        result = self.rec.recover(n_modes=5)
        self.assertEqual(result["N"], 256)
        self.assertEqual(result["n_primes"], 64)
        self.assertAlmostEqual(result["sigma"], 0.21, places=4)


# ─────────────────────────────────────────────────────────────────────────────
# Tests: sigma_sweep
# ─────────────────────────────────────────────────────────────────────────────

@unittest.skipUnless(_SCIPY, "scipy no disponible")
class TestSigmaSweep(unittest.TestCase):

    def test_returns_list(self):
        results = sigma_sweep(N=64, n_primes=16, sigma_values=[0.1, 0.21], n_modes=3)
        self.assertIsInstance(results, list)
        self.assertEqual(len(results), 2)

    def test_result_keys(self):
        results = sigma_sweep(N=64, n_primes=16, sigma_values=[0.21], n_modes=3)
        r = results[0]
        self.assertIn("sigma", r)
        self.assertIn("mean_error_pct", r)
        self.assertIn("estado", r)

    def test_sigma_c_in_results(self):
        sigma_values = [0.10, SIGMA_C, 0.30]
        results = sigma_sweep(N=64, n_primes=16, sigma_values=sigma_values, n_modes=3)
        sigmas = [r["sigma"] for r in results]
        self.assertIn(SIGMA_C, sigmas)

    def test_default_sigma_values(self):
        results = sigma_sweep(N=64, n_primes=16, n_modes=3)
        self.assertGreater(len(results), 0)


# ─────────────────────────────────────────────────────────────────────────────
# Tests: certificar_fase264
# ─────────────────────────────────────────────────────────────────────────────

@unittest.skipUnless(_SCIPY, "scipy no disponible")
class TestCertificarFase264(unittest.TestCase):
    """Tests de la función de certificación (N pequeño para velocidad)."""

    def test_returns_dict(self):
        result = certificar_fase264(N=256, n_primes=64, n_modes=5)
        self.assertIsInstance(result, dict)

    def test_keys(self):
        result = certificar_fase264(N=256, n_primes=64, n_modes=5)
        self.assertIn("certificado", result)
        self.assertIn("mean_error_pct", result)
        self.assertIn("fase", result)
        self.assertIn("estado", result)

    def test_fase_label(self):
        result = certificar_fase264(N=256, n_primes=64, n_modes=5)
        self.assertEqual(result["fase"], "FASE_264")

    def test_certificado_is_bool(self):
        result = certificar_fase264(N=256, n_primes=64, n_modes=5)
        self.assertIsInstance(result["certificado"], bool)

    def test_error_pct_positive(self):
        result = certificar_fase264(N=256, n_primes=64, n_modes=5)
        self.assertGreater(result["mean_error_pct"], 0.0)

    def test_error_pct_finite(self):
        result = certificar_fase264(N=256, n_primes=64, n_modes=5)
        self.assertTrue(np.isfinite(result["mean_error_pct"]))


if __name__ == "__main__":
    unittest.main(verbosity=2)
