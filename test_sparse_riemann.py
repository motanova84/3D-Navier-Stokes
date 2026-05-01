#!/usr/bin/env python3
"""
Tests para qcal.sparse_riemann — Fase #264
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Verifica el Hamiltoniano QCAL-GUE sparse para recuperación del espectro Riemann.

Cobertura:
  - Construcción del Hamiltoniano (sparse, simétrico, forma correcta)
  - Extracción de autovalores (converge, real, ordenados)
  - Cálculo de error espectral (interfaz y tipos correctos)
  - Barrido de σ (retorna mejor sigma)
  - Informe de certificación (claves y tipos correctos)
  - Importación desde paquete qcal (public API)
  - Casos de error y validación de parámetros

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
License: MIT
"""

import math
import unittest
import numpy as np

try:
    from scipy import sparse
    _SCIPY_AVAILABLE = True
except ImportError:
    _SCIPY_AVAILABLE = False


# ──────────────────────────────────────────────────────────────
# Parámetros de test (N pequeño para velocidad)
# ──────────────────────────────────────────────────────────────

_N_SMALL = 128    # Malla pequeña para tests rápidos
_N_MEDIUM = 256   # Malla media para tests de convergencia
_K_EVALS = 12     # Autovalores a extraer en tests


@unittest.skipUnless(_SCIPY_AVAILABLE, "scipy no está disponible")
class TestFractalQCALGUE(unittest.TestCase):
    """Tests para la clase FractalQCAL_GUE."""

    def setUp(self) -> None:
        from qcal.sparse_riemann import FractalQCAL_GUE
        self.FractalQCAL_GUE = FractalQCAL_GUE
        # Instancia pequeña para reutilización
        self.qcal = FractalQCAL_GUE(N=_N_SMALL, num_primes=20, sigma=0.21)

    # ── Construcción del Hamiltoniano ────────────────────────────────────────

    def test_hamiltonian_shape(self):
        """El Hamiltoniano tiene forma (N, N)."""
        H = self.qcal.build_hamiltonian()
        self.assertEqual(H.shape, (_N_SMALL, _N_SMALL))

    def test_hamiltonian_is_sparse(self):
        """El Hamiltoniano es sparse (número de no-ceros << N²)."""
        H = self.qcal.build_hamiltonian()
        self.assertTrue(sparse.issparse(H))
        density = H.nnz / (_N_SMALL * _N_SMALL)
        self.assertLess(density, 0.1)  # Menos del 10% de entradas no-cero

    def test_hamiltonian_is_symmetric(self):
        """El Hamiltoniano es simétrico: H = Hᵀ."""
        H = self.qcal.build_hamiltonian()
        diff = H - H.T
        max_diff = abs(diff).max()
        self.assertLess(max_diff, 1e-10, "H no es simétrico")

    def test_hamiltonian_cache(self):
        """build_hamiltonian() devuelve el mismo objeto en llamadas sucesivas."""
        H1 = self.qcal.build_hamiltonian()
        H2 = self.qcal.build_hamiltonian()
        self.assertIs(H1, H2)

    def test_hamiltonian_invalidated_on_sigma_change(self):
        """Cambiar sigma e invocar reset() construye un Hamiltoniano diferente."""
        H1 = self.qcal.build_hamiltonian()
        self.qcal.sigma = 0.25
        self.qcal.reset()  # Public API para invalidar caché
        H2 = self.qcal.build_hamiltonian()
        self.assertIsNot(H1, H2)

    # ── Extracción de autovalores ────────────────────────────────────────────

    def test_eigenvalues_count(self):
        """compute_eigenvalues(k) devuelve exactamente k autovalores."""
        evals = self.qcal.compute_eigenvalues(k=_K_EVALS)
        self.assertEqual(len(evals), _K_EVALS)

    def test_eigenvalues_real(self):
        """Todos los autovalores son reales (no complejos)."""
        evals = self.qcal.compute_eigenvalues(k=_K_EVALS)
        self.assertTrue(np.all(np.isreal(evals)))

    def test_eigenvalues_sorted(self):
        """Los autovalores están ordenados en orden no-decreciente."""
        evals = self.qcal.compute_eigenvalues(k=_K_EVALS)
        self.assertTrue(np.all(np.diff(evals) >= -1e-10))

    def test_eigenvalues_finite(self):
        """Todos los autovalores son finitos (no NaN ni Inf)."""
        evals = self.qcal.compute_eigenvalues(k=_K_EVALS)
        self.assertTrue(np.all(np.isfinite(evals)))

    def test_eigenvalues_k_too_large_raises(self):
        """k >= N debe lanzar ValueError."""
        with self.assertRaises(ValueError):
            self.qcal.compute_eigenvalues(k=_N_SMALL)

    # ── Cálculo de error espectral ───────────────────────────────────────────

    def test_spectral_error_keys(self):
        """compute_spectral_error devuelve todas las claves esperadas."""
        evals = self.qcal.compute_eigenvalues(k=_K_EVALS)
        result = self.qcal.compute_spectral_error(evals, n_compare=5)
        expected_keys = {
            "pos_evals", "riemann_zeros", "abs_errors",
            "rel_errors_pct", "mean_error_pct", "n_compared",
        }
        self.assertEqual(set(result.keys()), expected_keys)

    def test_spectral_error_with_min_eval_zero(self):
        """Con min_eval=0 se comparan autovalores incluso para N pequeño."""
        from qcal.sparse_riemann import compute_riemann_spectral_error
        evals = self.qcal.compute_eigenvalues(k=_K_EVALS)
        result = compute_riemann_spectral_error(evals, n_compare=5, min_eval=0.0)
        # Con min_eval=0 deberíamos tener autovalores comparados
        self.assertGreater(result["n_compared"], 0)
        self.assertFalse(np.isnan(result["mean_error_pct"]))

    def test_spectral_error_empty_when_no_pos_evals(self):
        """Si no hay autovalores > min_eval, n_compared=0 y mean_error=nan."""
        from qcal.sparse_riemann import compute_riemann_spectral_error
        evals_all_zero = np.array([-1.0, -0.5, 0.0, 0.1, 0.2])
        result = compute_riemann_spectral_error(evals_all_zero, n_compare=5, min_eval=5.0)
        self.assertEqual(result["n_compared"], 0)
        self.assertTrue(np.isnan(result["mean_error_pct"]))

    def test_spectral_error_types(self):
        """Los campos del resultado tienen los tipos correctos."""
        from qcal.sparse_riemann import compute_riemann_spectral_error
        # Simular autovalores en el rango de Riemann
        fake_evals = np.array([14.0, 21.0, 25.0, 30.0, 33.0, 38.0])
        result = compute_riemann_spectral_error(fake_evals, n_compare=5, min_eval=0.0)
        self.assertIsInstance(result["pos_evals"], np.ndarray)
        self.assertIsInstance(result["riemann_zeros"], np.ndarray)
        self.assertIsInstance(result["abs_errors"], np.ndarray)
        self.assertIsInstance(result["rel_errors_pct"], np.ndarray)
        self.assertIsInstance(result["mean_error_pct"], float)
        self.assertIsInstance(result["n_compared"], int)

    def test_spectral_error_perfect_match(self):
        """Con autovalores exactos, el error es ~0%."""
        from qcal.sparse_riemann import compute_riemann_spectral_error, RIEMANN_ZEROS_20
        perfect_evals = np.array(RIEMANN_ZEROS_20[:5])
        result = compute_riemann_spectral_error(perfect_evals, n_compare=5, min_eval=0.0)
        self.assertLess(result["mean_error_pct"], 1e-6)
        self.assertEqual(result["n_compared"], 5)

    # ── Barrido de σ ─────────────────────────────────────────────────────────

    def test_sigma_sweep_returns_dict(self):
        """sigma_sweep retorna un diccionario con las claves esperadas."""
        qcal = self.FractalQCAL_GUE(N=_N_SMALL, num_primes=15, sigma=0.21)
        result = qcal.sigma_sweep(sigmas=[0.20, 0.21, 0.22], k=10)
        self.assertIn("best_sigma", result)
        self.assertIn("best_error_pct", result)
        self.assertIn("sweep_results", result)

    def test_sigma_sweep_best_in_list(self):
        """El sigma óptimo es uno de los sigma probados."""
        qcal = self.FractalQCAL_GUE(N=_N_SMALL, num_primes=15, sigma=0.21)
        sigmas_to_try = [0.20, 0.21, 0.22]
        result = qcal.sigma_sweep(sigmas=sigmas_to_try, k=10)
        self.assertIn(result["best_sigma"], sigmas_to_try)

    def test_sigma_sweep_results_count(self):
        """El número de resultados del barrido coincide con los sigmas probados."""
        qcal = self.FractalQCAL_GUE(N=_N_SMALL, num_primes=15, sigma=0.21)
        sigmas = [0.18, 0.21, 0.25]
        result = qcal.sigma_sweep(sigmas=sigmas, k=10)
        self.assertEqual(len(result["sweep_results"]), len(sigmas))

    # ── Informe de certificación ─────────────────────────────────────────────

    def test_certification_report_keys(self):
        """certification_report devuelve todas las claves esperadas."""
        report = self.qcal.certification_report()
        expected_keys = {
            "N", "num_primes", "sigma", "f0",
            "mean_error_pct", "n_compared", "estado",
            "eigenvalues_sample",
        }
        self.assertEqual(set(report.keys()), expected_keys)

    def test_certification_report_n_correct(self):
        """El campo N en el reporte coincide con el N del objeto."""
        report = self.qcal.certification_report()
        self.assertEqual(report["N"], _N_SMALL)

    def test_certification_report_estado_valid(self):
        """El campo 'estado' es uno de los valores esperados."""
        valid_states = {
            "ANCLAJE_INMUTABLE_FASE264",
            "CONVERGENCIA_GUE",
            "RESONADOR_LOGARITMICO",
            "COLAPSO_INICIAL",
            "INSUFICIENTE_AUTOVALORES",
        }
        report = self.qcal.certification_report()
        self.assertIn(report["estado"], valid_states)

    def test_certification_report_eigenvalues_sample_is_list(self):
        """eigenvalues_sample es una lista de floats."""
        report = self.qcal.certification_report()
        self.assertIsInstance(report["eigenvalues_sample"], list)
        for v in report["eigenvalues_sample"]:
            self.assertIsInstance(v, float)

    # ── Validación de parámetros ─────────────────────────────────────────────

    def test_invalid_n_raises(self):
        """N < 64 debe lanzar ValueError."""
        with self.assertRaises(ValueError):
            self.FractalQCAL_GUE(N=32, num_primes=10)

    def test_invalid_num_primes_raises(self):
        """num_primes < 1 debe lanzar ValueError."""
        with self.assertRaises(ValueError):
            self.FractalQCAL_GUE(N=128, num_primes=0)

    def test_custom_f0(self):
        """El factor f0 personalizado se usa en la construcción del Hamiltoniano."""
        custom_f0 = 7.5
        qcal = self.FractalQCAL_GUE(N=_N_SMALL, num_primes=10, f0=custom_f0)
        self.assertAlmostEqual(qcal.f0, custom_f0)
        H = qcal.build_hamiltonian()
        self.assertEqual(H.shape, (_N_SMALL, _N_SMALL))


@unittest.skipUnless(_SCIPY_AVAILABLE, "scipy no está disponible")
class TestBuildSparseHamiltonian(unittest.TestCase):
    """Tests para la función de fábrica build_sparse_hamiltonian."""

    def test_returns_tuple(self):
        """build_sparse_hamiltonian retorna (H, u)."""
        from qcal.sparse_riemann import build_sparse_hamiltonian
        H, u = build_sparse_hamiltonian(N=128, num_primes=10)
        self.assertIsNotNone(H)
        self.assertIsNotNone(u)

    def test_u_shape(self):
        """La malla u tiene longitud N."""
        from qcal.sparse_riemann import build_sparse_hamiltonian
        H, u = build_sparse_hamiltonian(N=128, num_primes=10)
        self.assertEqual(len(u), 128)

    def test_u_range(self):
        """La malla u cubre [0, u_max]."""
        from qcal.sparse_riemann import build_sparse_hamiltonian
        H, u = build_sparse_hamiltonian(N=128, num_primes=10, u_max=80.0)
        self.assertAlmostEqual(u[0], 0.0)
        self.assertAlmostEqual(u[-1], 80.0, places=5)

    def test_invalid_n_raises(self):
        """N < 64 debe lanzar ValueError."""
        from qcal.sparse_riemann import build_sparse_hamiltonian
        with self.assertRaises(ValueError):
            build_sparse_hamiltonian(N=10, num_primes=5)

    def test_invalid_num_primes_raises(self):
        """num_primes < 1 debe lanzar ValueError."""
        from qcal.sparse_riemann import build_sparse_hamiltonian
        with self.assertRaises(ValueError):
            build_sparse_hamiltonian(N=128, num_primes=0)

    def test_hamiltonian_is_real(self):
        """El Hamiltoniano es real (no complejo)."""
        from qcal.sparse_riemann import build_sparse_hamiltonian
        H, _ = build_sparse_hamiltonian(N=128, num_primes=10)
        self.assertEqual(H.dtype.kind, "f")  # float (real)

    def test_sigma_affects_hamiltonian(self):
        """Diferentes valores de sigma producen Hamiltonianos diferentes."""
        from qcal.sparse_riemann import build_sparse_hamiltonian
        H1, _ = build_sparse_hamiltonian(N=128, num_primes=10, sigma=0.20)
        H2, _ = build_sparse_hamiltonian(N=128, num_primes=10, sigma=0.28)
        diff = (H1 - H2)
        self.assertGreater(abs(diff).max(), 1e-12)


@unittest.skipUnless(_SCIPY_AVAILABLE, "scipy no está disponible")
class TestRiemannZeros20(unittest.TestCase):
    """Tests para la constante RIEMANN_ZEROS_20."""

    def test_length(self):
        """RIEMANN_ZEROS_20 tiene exactamente 20 entradas."""
        from qcal.sparse_riemann import RIEMANN_ZEROS_20
        self.assertEqual(len(RIEMANN_ZEROS_20), 20)

    def test_first_zero(self):
        """El primer cero de Riemann γ₁ ≈ 14.1347."""
        from qcal.sparse_riemann import RIEMANN_ZEROS_20
        self.assertAlmostEqual(RIEMANN_ZEROS_20[0], 14.134725142, places=5)

    def test_increasing(self):
        """Los ceros de Riemann están en orden creciente."""
        from qcal.sparse_riemann import RIEMANN_ZEROS_20
        for i in range(len(RIEMANN_ZEROS_20) - 1):
            self.assertLess(RIEMANN_ZEROS_20[i], RIEMANN_ZEROS_20[i + 1])

    def test_all_positive(self):
        """Todos los ceros son positivos."""
        from qcal.sparse_riemann import RIEMANN_ZEROS_20
        self.assertTrue(all(z > 0 for z in RIEMANN_ZEROS_20))


@unittest.skipUnless(_SCIPY_AVAILABLE, "scipy no está disponible")
class TestQCALPublicAPI(unittest.TestCase):
    """Tests de integración: exportaciones del paquete qcal."""

    def test_import_from_qcal(self):
        """FractalQCAL_GUE se puede importar desde qcal directamente."""
        from qcal import FractalQCAL_GUE
        self.assertIsNotNone(FractalQCAL_GUE)

    def test_import_build_sparse_hamiltonian(self):
        """build_sparse_hamiltonian se puede importar desde qcal."""
        from qcal import build_sparse_hamiltonian
        self.assertIsNotNone(build_sparse_hamiltonian)

    def test_import_compute_riemann_spectral_error(self):
        """compute_riemann_spectral_error se puede importar desde qcal."""
        from qcal import compute_riemann_spectral_error
        self.assertIsNotNone(compute_riemann_spectral_error)

    def test_import_riemann_zeros_20(self):
        """RIEMANN_ZEROS_20 se puede importar desde qcal."""
        from qcal import RIEMANN_ZEROS_20
        self.assertEqual(len(RIEMANN_ZEROS_20), 20)

    def test_qcal_version(self):
        """El paquete qcal tiene una versión semántica válida."""
        import qcal
        parts = qcal.__version__.split(".")
        self.assertEqual(len(parts), 3, "La versión debe tener formato major.minor.patch")
        self.assertTrue(all(p.isdigit() for p in parts), "Cada parte debe ser numérica")

    def test_existing_exports_still_work(self):
        """Las exportaciones existentes del paquete qcal siguen funcionando."""
        import qcal
        # Constantes base
        self.assertAlmostEqual(qcal.F0, 141.7001, places=3)
        self.assertAlmostEqual(qcal.PSI_MIN, 0.888, places=3)
        self.assertEqual(qcal.NODOS_LOGOS, 51)
        # Operador espectral existente
        self.assertIsNotNone(qcal.QCALSpectralOperator)
        # GACT flow
        self.assertIsNotNone(qcal.GACTUnifiedFlow)


@unittest.skipUnless(_SCIPY_AVAILABLE, "scipy no está disponible")
class TestSparseRiemannIntegration(unittest.TestCase):
    """Tests de integración end-to-end del pipeline sparse Riemann."""

    def test_full_pipeline_small_n(self):
        """Pipeline completo: construir → autovalores → error → reporte."""
        from qcal.sparse_riemann import FractalQCAL_GUE, compute_riemann_spectral_error

        qcal = FractalQCAL_GUE(N=_N_MEDIUM, num_primes=30, sigma=0.21)

        # 1. Construir Hamiltoniano
        H = qcal.build_hamiltonian()
        self.assertEqual(H.shape, (_N_MEDIUM, _N_MEDIUM))

        # 2. Extraer autovalores
        evals = qcal.compute_eigenvalues(k=15)
        self.assertEqual(len(evals), 15)
        self.assertTrue(np.all(np.isfinite(evals)))

        # 3. Error espectral (con min_eval=0 para N pequeño)
        result = compute_riemann_spectral_error(evals, n_compare=5, min_eval=0.0)
        self.assertGreater(result["n_compared"], 0)

        # 4. Reporte de certificación
        report = qcal.certification_report()
        self.assertIn("estado", report)
        self.assertIn("mean_error_pct", report)

    def test_different_sigma_produces_different_eigenvalues(self):
        """Diferentes sigma dan diferentes autovalores."""
        from qcal.sparse_riemann import FractalQCAL_GUE

        qcal1 = FractalQCAL_GUE(N=_N_SMALL, num_primes=20, sigma=0.18)
        qcal2 = FractalQCAL_GUE(N=_N_SMALL, num_primes=20, sigma=0.28)

        evals1 = qcal1.compute_eigenvalues(k=10)
        evals2 = qcal2.compute_eigenvalues(k=10)

        # Los autovalores deben diferir (el potencial cambia con sigma)
        max_diff = np.max(np.abs(evals1 - evals2))
        self.assertGreater(max_diff, 1e-10)

    def test_more_primes_changes_spectrum(self):
        """Más primos en el potencial fractal cambia el espectro."""
        from qcal.sparse_riemann import FractalQCAL_GUE

        qcal_few = FractalQCAL_GUE(N=_N_SMALL, num_primes=5, sigma=0.21)
        qcal_many = FractalQCAL_GUE(N=_N_SMALL, num_primes=50, sigma=0.21)

        evals_few = qcal_few.compute_eigenvalues(k=8)
        evals_many = qcal_many.compute_eigenvalues(k=8)

        max_diff = np.max(np.abs(evals_few - evals_many))
        self.assertGreater(max_diff, 1e-10)


if __name__ == "__main__":
    unittest.main(verbosity=2)
