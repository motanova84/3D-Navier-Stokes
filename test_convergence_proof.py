#!/usr/bin/env python3
"""
Tests para QCAL-Strings — Censura Taquiónica y Prueba de Convergencia
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Pruebas unitarias para qcal.convergence_proof:
- TachyonCensor: mapeo sigma y Ψ_censored
- RegularizedQCALHamiltonian: norma H¹ y autovalores
- compute_ns_hamiltonian: cálculo del Hamiltoniano NS
- epsilon_boundary_sweep: barrido de convergencia
- prove_convergence_limit: verificación ε → 0

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
License: MIT
"""

import unittest
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).parent))

from qcal.convergence_proof import (
    TachyonCensor,
    RegularizedQCALHamiltonian,
    compute_ns_hamiltonian,
    epsilon_boundary_sweep,
    prove_convergence_limit,
    H1_NS,
    EPSILON_CONVERGENCE,
    TOL_CONVERGENCE,
    SIGMA_CRITICAL_LINE,
    F0,
)


# ─────────────────────────────────────────────────────────────────────────────
# Tests: constantes
# ─────────────────────────────────────────────────────────────────────────────

class TestConstants(unittest.TestCase):

    def test_f0(self):
        self.assertAlmostEqual(F0, 141.7001, places=4)

    def test_h1_ns(self):
        self.assertAlmostEqual(H1_NS, 0.1363, places=4)

    def test_epsilon_convergence(self):
        self.assertAlmostEqual(EPSILON_CONVERGENCE, 1e-4, places=8)

    def test_tol_convergence(self):
        self.assertAlmostEqual(TOL_CONVERGENCE, 1e-3, places=6)

    def test_sigma_critical_line(self):
        self.assertAlmostEqual(SIGMA_CRITICAL_LINE, 0.5, places=4)


# ─────────────────────────────────────────────────────────────────────────────
# Tests: TachyonCensor
# ─────────────────────────────────────────────────────────────────────────────

class TestTachyonCensor(unittest.TestCase):

    def test_instantiation_default(self):
        censor = TachyonCensor()
        self.assertAlmostEqual(censor.epsilon, 0.01, places=6)
        self.assertAlmostEqual(censor.D_density, 1.0, places=6)

    def test_instantiation_custom(self):
        censor = TachyonCensor(epsilon=0.05, D_density=2.0)
        self.assertAlmostEqual(censor.epsilon, 0.05, places=6)
        self.assertAlmostEqual(censor.D_density, 2.0, places=6)

    def test_negative_epsilon_raises(self):
        with self.assertRaises(ValueError):
            TachyonCensor(epsilon=-0.1)

    def test_zero_epsilon_raises(self):
        with self.assertRaises(ValueError):
            TachyonCensor(epsilon=0.0)

    def test_map_sigma_on_critical(self):
        censor = TachyonCensor(epsilon=0.01)
        k = np.array([0.0])
        sigma = censor.map_sigma(k, k_max=1.0)
        self.assertAlmostEqual(float(sigma[0]), SIGMA_CRITICAL_LINE, places=6)

    def test_map_sigma_range(self):
        censor = TachyonCensor(epsilon=0.01)
        k = np.linspace(0, 1, 100)
        sigma = censor.map_sigma(k, k_max=1.0)
        self.assertTrue(np.all(sigma >= SIGMA_CRITICAL_LINE))
        self.assertTrue(np.all(sigma <= SIGMA_CRITICAL_LINE + censor.epsilon + 1e-10))

    def test_map_sigma_invalid_kmax(self):
        censor = TachyonCensor()
        with self.assertRaises(ValueError):
            censor.map_sigma(np.array([1.0]), k_max=0.0)

    def test_psi_censored_on_critical(self):
        # σ = 1/2 → Ψ = exp(0) = 1
        censor = TachyonCensor(epsilon=0.01)
        sigma = np.array([SIGMA_CRITICAL_LINE])
        psi = censor.psi_censored(sigma)
        self.assertAlmostEqual(float(psi[0]), 1.0, places=6)

    def test_psi_censored_off_critical(self):
        # σ > 1/2 → Ψ < 1
        censor = TachyonCensor(epsilon=0.01)
        sigma = np.array([0.6])  # desviación de 0.1
        psi = censor.psi_censored(sigma)
        self.assertLess(float(psi[0]), 1.0)
        self.assertGreater(float(psi[0]), 0.0)

    def test_psi_censored_exponential_decay(self):
        # Mayor desviación → Ψ más pequeño
        censor = TachyonCensor(epsilon=0.01)
        sigma_small = np.array([0.51])
        sigma_large = np.array([0.60])
        psi_small = float(censor.psi_censored(sigma_small)[0])
        psi_large = float(censor.psi_censored(sigma_large)[0])
        self.assertGreater(psi_small, psi_large)

    def test_apply_alias(self):
        censor = TachyonCensor(epsilon=0.01)
        sigma = np.array([SIGMA_CRITICAL_LINE, 0.6])
        np.testing.assert_array_equal(censor.apply(sigma), censor.psi_censored(sigma))

    def test_is_stable_true(self):
        censor = TachyonCensor(epsilon=0.1)
        sigma = np.array([0.5, 0.55, 0.45])  # todos dentro de ε=0.1
        self.assertTrue(censor.is_stable(sigma))

    def test_is_stable_false(self):
        censor = TachyonCensor(epsilon=0.01)
        sigma = np.array([0.5, 0.8])  # 0.8 está fuera
        self.assertFalse(censor.is_stable(sigma))

    def test_censor_spectrum_keys(self):
        censor = TachyonCensor(epsilon=0.01)
        k = np.linspace(0, 10, 50)
        result = censor.censor_spectrum(k, k_max=10.0)
        for key in ["sigma_mapped", "psi_censored", "n_stable", "n_penalized",
                    "fraccion_estable"]:
            self.assertIn(key, result)

    def test_censor_spectrum_counts(self):
        censor = TachyonCensor(epsilon=0.01)
        k = np.linspace(0, 10, 50)
        result = censor.censor_spectrum(k, k_max=10.0)
        total = result["n_stable"] + result["n_penalized"]
        self.assertEqual(total, 50)

    def test_censor_spectrum_fraction(self):
        censor = TachyonCensor(epsilon=0.01)
        k = np.linspace(0, 10, 100)
        result = censor.censor_spectrum(k, k_max=10.0)
        self.assertGreaterEqual(result["fraccion_estable"], 0.0)
        self.assertLessEqual(result["fraccion_estable"], 1.0)


# ─────────────────────────────────────────────────────────────────────────────
# Tests: RegularizedQCALHamiltonian
# ─────────────────────────────────────────────────────────────────────────────

class TestRegularizedQCALHamiltonian(unittest.TestCase):

    def test_instantiation(self):
        H = RegularizedQCALHamiltonian(N=50)
        self.assertEqual(H.N, 50)

    def test_invalid_N(self):
        with self.assertRaises(ValueError):
            RegularizedQCALHamiltonian(N=0)

    def test_invalid_epsilon(self):
        with self.assertRaises(ValueError):
            RegularizedQCALHamiltonian(epsilon=0.0)

    def test_hamiltonian_shape(self):
        H = RegularizedQCALHamiltonian(N=20)
        H_mat = H.compute_hamiltonian()
        self.assertEqual(H_mat.shape, (20, 20))

    def test_h1_norm_positive(self):
        H = RegularizedQCALHamiltonian(N=50)
        h1 = H.h1_norm()
        self.assertGreater(h1, 0.0)

    def test_h1_norm_finite(self):
        H = RegularizedQCALHamiltonian(N=50)
        h1 = H.h1_norm()
        self.assertTrue(np.isfinite(h1))

    def test_eigenvalues_count(self):
        H = RegularizedQCALHamiltonian(N=20)
        evals = H.eigenvalues()
        self.assertEqual(len(evals), 20)

    def test_eigenvalues_sorted(self):
        H = RegularizedQCALHamiltonian(N=20)
        evals = H.eigenvalues()
        self.assertTrue(np.all(np.diff(evals) >= 0))

    def test_h1_norm_finite_for_all_epsilon(self):
        # H1 norm should be finite and positive for any epsilon
        for eps in [0.1, 0.01, 1e-3, 1e-4]:
            H = RegularizedQCALHamiltonian(N=20, epsilon=eps)
            h1 = H.h1_norm()
            self.assertGreater(h1, 0.0)
            self.assertTrue(np.isfinite(h1))


# ─────────────────────────────────────────────────────────────────────────────
# Tests: compute_ns_hamiltonian
# ─────────────────────────────────────────────────────────────────────────────

class TestComputeNSHamiltonian(unittest.TestCase):

    def test_returns_dict(self):
        result = compute_ns_hamiltonian(N=20)
        self.assertIsInstance(result, dict)

    def test_keys(self):
        result = compute_ns_hamiltonian(N=20)
        for key in ["H", "h1_norm", "eigenvalues", "N", "epsilon", "f0"]:
            self.assertIn(key, result)

    def test_h_shape(self):
        N = 20
        result = compute_ns_hamiltonian(N=N)
        self.assertEqual(result["H"].shape, (N, N))

    def test_h1_positive(self):
        result = compute_ns_hamiltonian(N=20)
        self.assertGreater(result["h1_norm"], 0.0)

    def test_metadata(self):
        result = compute_ns_hamiltonian(N=20, epsilon=1e-3, f0=F0)
        self.assertEqual(result["N"], 20)
        self.assertAlmostEqual(result["epsilon"], 1e-3, places=8)
        self.assertAlmostEqual(result["f0"], F0, places=4)


# ─────────────────────────────────────────────────────────────────────────────
# Tests: epsilon_boundary_sweep
# ─────────────────────────────────────────────────────────────────────────────

class TestEpsilonBoundarySweep(unittest.TestCase):

    def test_returns_list(self):
        results = epsilon_boundary_sweep(N=20, epsilon_values=[1e-2, 1e-3])
        self.assertIsInstance(results, list)
        self.assertEqual(len(results), 2)

    def test_result_keys(self):
        results = epsilon_boundary_sweep(N=20, epsilon_values=[1e-3])
        r = results[0]
        for key in ["epsilon", "h1_norm", "convergido", "delta_h1"]:
            self.assertIn(key, r)

    def test_convergido_is_bool(self):
        results = epsilon_boundary_sweep(N=20, epsilon_values=[1e-4])
        self.assertIsInstance(results[0]["convergido"], bool)

    def test_delta_h1_positive(self):
        results = epsilon_boundary_sweep(N=20, epsilon_values=[1e-4])
        self.assertGreaterEqual(results[0]["delta_h1"], 0.0)

    def test_default_epsilon_values(self):
        results = epsilon_boundary_sweep(N=20)
        self.assertEqual(len(results), 5)

    def test_small_epsilon_boundary(self):
        # With ε = EPSILON_CONVERGENCE, delta_h1 should be finite and positive
        results = epsilon_boundary_sweep(N=100, epsilon_values=[EPSILON_CONVERGENCE],
                                          tol=TOL_CONVERGENCE)
        self.assertGreater(results[0]["delta_h1"], 0.0)
        self.assertTrue(np.isfinite(results[0]["delta_h1"]))


# ─────────────────────────────────────────────────────────────────────────────
# Tests: prove_convergence_limit
# ─────────────────────────────────────────────────────────────────────────────

class TestProveConvergenceLimit(unittest.TestCase):

    def test_returns_dict(self):
        result = prove_convergence_limit(N=50)
        self.assertIsInstance(result, dict)

    def test_keys(self):
        result = prove_convergence_limit(N=50)
        for key in ["convergido", "h1_norm", "delta_h1", "censura_activa",
                    "epsilon", "N", "tol", "mensaje"]:
            self.assertIn(key, result)

    def test_convergido_is_bool(self):
        result = prove_convergence_limit(N=50)
        self.assertIsInstance(result["convergido"], bool)

    def test_h1_positive(self):
        result = prove_convergence_limit(N=50)
        self.assertGreater(result["h1_norm"], 0.0)

    def test_censura_activa(self):
        result = prove_convergence_limit(N=50, epsilon=EPSILON_CONVERGENCE)
        self.assertTrue(result["censura_activa"])

    def test_prove_convergence_returns_info(self):
        # prove_convergence_limit should return a complete informational dict
        result = prove_convergence_limit(N=100, epsilon=EPSILON_CONVERGENCE,
                                          tol=TOL_CONVERGENCE)
        self.assertIsInstance(result["convergido"], bool)
        self.assertGreater(result["h1_norm"], 0.0)
        self.assertGreaterEqual(result["delta_h1"], 0.0)

    def test_mensaje_not_empty(self):
        result = prove_convergence_limit(N=50)
        self.assertGreater(len(result["mensaje"]), 0)


if __name__ == "__main__":
    unittest.main(verbosity=2)
