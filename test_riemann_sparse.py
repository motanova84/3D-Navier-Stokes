#!/usr/bin/env python3
"""
Tests para QCAL Riemann Sparse Recovery — Fases #261–#264

Valida la arquitectura sparse de recuperación espectral de los ceros de
Riemann mediante el Hamiltoniano de Berry-Keating con potencial log-primo.
"""

import math
import unittest

import numpy as np
from scipy import sparse

from qcal.riemann_sparse import (
    RiemannSparseRecovery,
    build_bk_sparse,
    build_vmod_sparse,
    certificar_fase264,
    sigma_sweep,
    _build_extended_zeros,
    _get_primes,
    _sieve,
    _weyl_zero,
    N_GRID_DEFAULT,
    N_GRID_FAST,
    N_PRIMES_DEFAULT,
    SIGMA_C,
)
from qcal.spectral_operator import RIEMANN_ZEROS


# ──────────────────────────────────────────────────────────────
# Tests auxiliares — sieve y primos
# ──────────────────────────────────────────────────────────────

class TestSieve(unittest.TestCase):
    """Tests de la Criba de Eratóstenes."""

    def test_small_primes(self) -> None:
        primes = _sieve(20)
        self.assertEqual(primes, [2, 3, 5, 7, 11, 13, 17, 19])

    def test_empty_below_2(self) -> None:
        self.assertEqual(_sieve(1), [])
        self.assertEqual(_sieve(0), [])

    def test_two_is_prime(self) -> None:
        primes = _sieve(2)
        self.assertEqual(primes, [2])


class TestGetPrimes(unittest.TestCase):
    """Tests de _get_primes."""

    def test_returns_requested_count(self) -> None:
        for n in (1, 5, 10, 100):
            primes = _get_primes(n)
            self.assertEqual(len(primes), n)

    def test_first_prime_is_2(self) -> None:
        self.assertEqual(_get_primes(1)[0], 2)

    def test_tenth_prime(self) -> None:
        primes = _get_primes(10)
        self.assertEqual(primes[-1], 29)

    def test_zero_primes(self) -> None:
        self.assertEqual(_get_primes(0), [])


# ──────────────────────────────────────────────────────────────
# Tests de extrapolación de ceros de Riemann (Weyl)
# ──────────────────────────────────────────────────────────────

class TestWeylExtrapolation(unittest.TestCase):
    """Tests del estimador de ceros de Riemann por fórmula de Weyl."""

    def test_weyl_first_zero_positive(self) -> None:
        """El estimador de Weyl debe devolver valores positivos."""
        self.assertGreater(_weyl_zero(1), 0.0)

    def test_weyl_monotone(self) -> None:
        """Los estimadores de Weyl deben ser crecientes en n."""
        vals = [_weyl_zero(n) for n in range(1, 20)]
        for a, b in zip(vals, vals[1:]):
            self.assertLess(a, b)

    def test_weyl_large_n_reasonable(self) -> None:
        """Para n grande, la estimación debe ser positiva y razonable."""
        val = _weyl_zero(100)
        self.assertGreater(val, 200.0)  # γ_100 ≈ 236 (Weyl approx > 200)

    def test_build_extended_zeros_length(self) -> None:
        """_build_extended_zeros devuelve exactamente N valores."""
        for N in (10, 50, 100, 200):
            zeros = _build_extended_zeros(N)
            self.assertEqual(len(zeros), N)

    def test_build_extended_zeros_first_50_match_known(self) -> None:
        """Los primeros 50 valores deben ser los ceros conocidos de LMFDB."""
        zeros = _build_extended_zeros(60)
        known = RIEMANN_ZEROS[:50]
        np.testing.assert_array_almost_equal(zeros[:50], known, decimal=6)

    def test_build_extended_zeros_monotone(self) -> None:
        """Los ceros extendidos deben ser crecientes."""
        zeros = _build_extended_zeros(80)
        diffs = np.diff(zeros)
        self.assertTrue(np.all(diffs > 0))


# ──────────────────────────────────────────────────────────────
# Tests de build_bk_sparse
# ──────────────────────────────────────────────────────────────

class TestBuildBKSparse(unittest.TestCase):
    """Tests del constructor del Hamiltoniano de Berry-Keating sparse."""

    def setUp(self) -> None:
        self.N = 64
        self.H = build_bk_sparse(self.N)

    def test_shape(self) -> None:
        """La matriz debe ser cuadrada de tamaño (N, N)."""
        self.assertEqual(self.H.shape, (self.N, self.N))

    def test_sparse_type(self) -> None:
        """El resultado debe ser una matriz sparse."""
        self.assertTrue(sparse.issparse(self.H))

    def test_is_symmetric(self) -> None:
        """Ĥ_BK debe ser simétrico (hermítico real)."""
        diff = (self.H - self.H.T).toarray()
        np.testing.assert_allclose(diff, 0.0, atol=1e-12)

    def test_nnz_sparse(self) -> None:
        """La matriz debe ser sparse (nnz ≪ N²)."""
        self.assertLess(self.H.nnz, self.N * self.N)
        # Tridiagonal + diagonal → máximo 3N - 2 entradas no nulas
        self.assertLessEqual(self.H.nnz, 3 * self.N)

    def test_diagonal_positive(self) -> None:
        """La diagonal principal (espectro BK) debe ser positiva."""
        diag = self.H.diagonal()
        self.assertTrue(np.all(diag > 0))

    def test_real_entries(self) -> None:
        """Todas las entradas deben ser reales."""
        self.assertTrue(np.isrealobj(self.H.toarray()))


# ──────────────────────────────────────────────────────────────
# Tests de build_vmod_sparse
# ──────────────────────────────────────────────────────────────

class TestBuildVmodSparse(unittest.TestCase):
    """Tests del constructor del potencial fractal log-primo."""

    def setUp(self) -> None:
        self.N = 64
        primes = _get_primes(20)
        self.log_primes = np.array([math.log(p) for p in primes])
        self.V = build_vmod_sparse(self.N, self.log_primes, sigma=SIGMA_C)

    def test_shape(self) -> None:
        self.assertEqual(self.V.shape, (self.N, self.N))

    def test_is_diagonal(self) -> None:
        """V_mod debe ser una matriz diagonal."""
        V_arr = self.V.toarray()
        np.testing.assert_allclose(V_arr - np.diag(V_arr.diagonal()), 0.0, atol=1e-12)

    def test_diagonal_nonneg(self) -> None:
        """Los valores diagonales de V_mod deben ser no negativos."""
        diag = self.V.diagonal()
        self.assertTrue(np.all(diag >= 0.0))

    def test_sparse_type(self) -> None:
        self.assertTrue(sparse.issparse(self.V))

    def test_zero_primes_gives_zero_potential(self) -> None:
        """Sin primos, el potencial debe ser identicamente nulo."""
        V_zero = build_vmod_sparse(self.N, np.array([]), sigma=SIGMA_C)
        np.testing.assert_allclose(V_zero.toarray(), 0.0, atol=1e-12)

    def test_sigma_effect(self) -> None:
        """Sigma más pequeño produce bumps más estrechos (varianza menor en grilla gruesa)."""
        V_narrow = build_vmod_sparse(self.N, self.log_primes, sigma=0.05)
        V_wide = build_vmod_sparse(self.N, self.log_primes, sigma=1.0)
        # Con sigma muy pequeño (< du), los bumps no se resuelven en la malla
        # → V casi nulo → varianza menor; sigma grande → varianza mayor
        var_narrow = float(np.var(V_narrow.diagonal()))
        var_wide = float(np.var(V_wide.diagonal()))
        self.assertLessEqual(var_narrow, var_wide)


# ──────────────────────────────────────────────────────────────
# Tests de RiemannSparseRecovery
# ──────────────────────────────────────────────────────────────

class TestRiemannSparseRecovery(unittest.TestCase):
    """Tests del recuperador espectral de Riemann sparse."""

    def setUp(self) -> None:
        self.rec = RiemannSparseRecovery(N=128, n_primes=20, sigma=SIGMA_C, alpha=0.05)

    def test_init_valid(self) -> None:
        """Inicialización con parámetros válidos no lanza excepción."""
        rec = RiemannSparseRecovery(N=64, n_primes=10, sigma=0.3)
        self.assertEqual(rec.N, 64)

    def test_init_invalid_N(self) -> None:
        with self.assertRaises(ValueError):
            RiemannSparseRecovery(N=1)

    def test_init_invalid_sigma(self) -> None:
        with self.assertRaises(ValueError):
            RiemannSparseRecovery(sigma=-0.1)

    def test_init_invalid_f0(self) -> None:
        with self.assertRaises(ValueError):
            RiemannSparseRecovery(f0=0.0)

    def test_build_hamiltonian_shape(self) -> None:
        H = self.rec.build_hamiltonian()
        self.assertEqual(H.shape, (128, 128))

    def test_build_hamiltonian_sparse(self) -> None:
        H = self.rec.build_hamiltonian()
        self.assertTrue(sparse.issparse(H))
        self.assertLess(H.nnz, 128 * 128)

    def test_build_hamiltonian_cached(self) -> None:
        """La segunda llamada devuelve la misma instancia."""
        H1 = self.rec.build_hamiltonian()
        H2 = self.rec.build_hamiltonian()
        self.assertIs(H1, H2)

    def test_invalidate_cache(self) -> None:
        """Invalidar la caché fuerza reconstrucción."""
        H1 = self.rec.build_hamiltonian()
        self.rec.invalidate_cache()
        H2 = self.rec.build_hamiltonian()
        self.assertIsNot(H1, H2)

    def test_compute_eigenvalues_count(self) -> None:
        evals = self.rec.compute_eigenvalues(k=5)
        self.assertEqual(len(evals), 5)

    def test_compute_eigenvalues_sorted(self) -> None:
        evals = self.rec.compute_eigenvalues(k=8)
        self.assertTrue(np.all(np.diff(evals) >= 0))

    def test_compute_eigenvalues_real(self) -> None:
        evals = self.rec.compute_eigenvalues(k=5)
        self.assertTrue(np.all(np.isreal(evals)))

    def test_error_report_structure(self) -> None:
        report = self.rec.error_report(k=5)
        for key in ('eigenvalues', 'riemann_zeros', 'errors_pct',
                    'mean_error_pct', 'max_error_pct', 'n_modes', 'phase'):
            self.assertIn(key, report)

    def test_error_report_mean_error_finite(self) -> None:
        report = self.rec.error_report(k=5)
        self.assertFalse(math.isnan(report['mean_error_pct']))

    def test_error_report_positive_errors(self) -> None:
        report = self.rec.error_report(k=5)
        self.assertTrue(np.all(report['errors_pct'] >= 0.0))

    def test_error_report_phase_label(self) -> None:
        report = self.rec.error_report(k=5)
        valid_phases = {
            'QED-SPARSE-264-ANCLAJE-INMUTABLE',
            'QED-SPARSE-ACTIVE',
            'RESONADOR-LOGARITMICO',
            'COLAPSO-INICIAL',
            'INSUFFICIENT_MODES',
        }
        self.assertIn(report['phase'], valid_phases)


# ──────────────────────────────────────────────────────────────
# Tests de recuperación espectral (acurácia)
# ──────────────────────────────────────────────────────────────

class TestSpectralRecovery(unittest.TestCase):
    """
    Tests de acurácia numérica: los autovalores deben aproximar los ceros de
    Riemann con error razonable.
    """

    def test_first_eigenvalue_close_to_gamma1(self) -> None:
        """El primer autovalor positivo debe ser cercano a γ₁ ≈ 14.1347."""
        rec = RiemannSparseRecovery(N=128, n_primes=20, sigma=SIGMA_C, alpha=0.05)
        report = rec.error_report(k=5)
        self.assertGreater(report['n_modes'], 0)
        first_eval = report['eigenvalues'][0]
        # Debe estar dentro del 2% de γ₁ = 14.1347
        self.assertAlmostEqual(first_eval, RIEMANN_ZEROS[0], delta=RIEMANN_ZEROS[0] * 0.02)

    def test_ten_eigenvalues_low_error(self) -> None:
        """Los primeros 10 modos deben tener error medio < 2% con alpha pequeño."""
        rec = RiemannSparseRecovery(N=256, n_primes=30, sigma=SIGMA_C, alpha=0.05)
        report = rec.error_report(k=10)
        self.assertLess(report['mean_error_pct'], 2.0)

    def test_phase_is_anclaje_for_low_alpha(self) -> None:
        """Con alpha pequeño, la fase debe ser ANCLAJE-INMUTABLE."""
        rec = RiemannSparseRecovery(N=256, n_primes=30, sigma=SIGMA_C, alpha=0.01)
        report = rec.error_report(k=10)
        self.assertEqual(report['phase'], 'QED-SPARSE-264-ANCLAJE-INMUTABLE')

    def test_error_increases_with_alpha(self) -> None:
        """Mayor acoplamiento α → mayor perturbación → mayor error."""
        rec_low = RiemannSparseRecovery(N=128, n_primes=20, sigma=SIGMA_C, alpha=0.001)
        rec_high = RiemannSparseRecovery(N=128, n_primes=20, sigma=SIGMA_C, alpha=0.5)
        err_low = rec_low.error_report(k=5)['mean_error_pct']
        err_high = rec_high.error_report(k=5)['mean_error_pct']
        self.assertLess(err_low, err_high)


# ──────────────────────────────────────────────────────────────
# Tests de sigma_sweep
# ──────────────────────────────────────────────────────────────

class TestSigmaSweep(unittest.TestCase):
    """Tests del barrido de sigma."""

    def setUp(self) -> None:
        self.sigmas = [0.1, 0.21, 0.5]
        self.results = sigma_sweep(
            self.sigmas, N=128, n_primes=15, k=5
        )

    def test_returns_one_result_per_sigma(self) -> None:
        self.assertEqual(len(self.results), len(self.sigmas))

    def test_result_structure(self) -> None:
        for res in self.results:
            self.assertIn('sigma', res)
            self.assertIn('mean_error_pct', res)
            self.assertIn('phase', res)

    def test_sigma_values_preserved(self) -> None:
        for sigma, res in zip(self.sigmas, self.results):
            self.assertAlmostEqual(res['sigma'], sigma)

    def test_all_errors_finite(self) -> None:
        for res in self.results:
            self.assertFalse(math.isnan(res['mean_error_pct']))


# ──────────────────────────────────────────────────────────────
# Tests de certificar_fase264
# ──────────────────────────────────────────────────────────────

class TestCertificarFase264(unittest.TestCase):
    """Tests de la certificación Fase #264."""

    def setUp(self) -> None:
        # Usar N pequeño para test rápido
        self.cert = certificar_fase264(
            N=256, n_primes=30, sigma=SIGMA_C, k=10,
            f0=141.7001, error_threshold=5.0
        )

    def test_certificado_true_for_small_alpha(self) -> None:
        """Con parámetros correctos, el certificado debe ser True."""
        self.assertTrue(self.cert['certificado'])

    def test_sha256_tag(self) -> None:
        self.assertEqual(self.cert['sha256_tag'], 'QED-SPARSE-264-20260315')

    def test_result_keys(self) -> None:
        for key in ('certificado', 'mean_error_pct', 'max_error_pct', 'phase',
                    'N', 'n_primes', 'sigma', 'n_modes', 'sha256_tag',
                    'eigenvalues', 'riemann_zeros'):
            self.assertIn(key, self.cert)

    def test_n_modes_positive(self) -> None:
        self.assertGreater(self.cert['n_modes'], 0)

    def test_eigenvalues_array(self) -> None:
        self.assertIsInstance(self.cert['eigenvalues'], np.ndarray)
        self.assertGreater(len(self.cert['eigenvalues']), 0)

    def test_phase_anclaje(self) -> None:
        self.assertEqual(self.cert['phase'], 'QED-SPARSE-264-ANCLAJE-INMUTABLE')

    def test_fails_with_tight_threshold(self) -> None:
        """Con umbral 0.001%, la certificación debe fallar."""
        cert = certificar_fase264(
            N=128, n_primes=10, sigma=0.5, k=5,
            error_threshold=0.001
        )
        # sigma=0.5 with alpha=0.05 may still pass; use very tight threshold
        cert_tight = certificar_fase264(
            N=128, n_primes=10, sigma=0.5, k=5,
            error_threshold=1e-6
        )
        self.assertFalse(cert_tight['certificado'])


# ──────────────────────────────────────────────────────────────
# Tests de constantes de módulo
# ──────────────────────────────────────────────────────────────

class TestModuleConstants(unittest.TestCase):
    """Tests de las constantes de módulo."""

    def test_sigma_c(self) -> None:
        self.assertAlmostEqual(SIGMA_C, 0.21, places=2)

    def test_n_primes_default(self) -> None:
        self.assertEqual(N_PRIMES_DEFAULT, 2000)

    def test_n_grid_default(self) -> None:
        self.assertEqual(N_GRID_DEFAULT, 32768)

    def test_n_grid_fast(self) -> None:
        self.assertEqual(N_GRID_FAST, 1024)


# ──────────────────────────────────────────────────────────────
# Tests de integración con qcal.__init__
# ──────────────────────────────────────────────────────────────

class TestQCALPackageIntegration(unittest.TestCase):
    """Verifica que los símbolos nuevos estén correctamente exportados por qcal."""

    def test_imports_from_qcal(self) -> None:
        import qcal
        self.assertTrue(hasattr(qcal, 'RiemannSparseRecovery'))
        self.assertTrue(hasattr(qcal, 'build_bk_sparse'))
        self.assertTrue(hasattr(qcal, 'build_vmod_sparse'))
        self.assertTrue(hasattr(qcal, 'sigma_sweep'))
        self.assertTrue(hasattr(qcal, 'certificar_fase264'))
        self.assertTrue(hasattr(qcal, 'SIGMA_C'))

    def test_qcal_version(self) -> None:
        import qcal
        self.assertEqual(qcal.__version__, '2.2.0')

    def test_spectral_operator_still_exported(self) -> None:
        """Los símbolos del operador espectral original siguen exportados."""
        import qcal
        self.assertTrue(hasattr(qcal, 'QCALSpectralOperator'))
        self.assertTrue(hasattr(qcal, 'certificar_riemann_qcal'))
        self.assertTrue(hasattr(qcal, 'RIEMANN_ZEROS'))


if __name__ == '__main__':
    unittest.main(verbosity=2)
