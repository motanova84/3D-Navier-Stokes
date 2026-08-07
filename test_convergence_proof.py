#!/usr/bin/env python3
"""
Tests for the QCAL Convergence Proof module.

Validates:
  - TachyonCensor (spectral Lorentzian filter, ε bandwidth, Dirac limit)
  - RegularizedQCALHamiltonian (Ĥ_QCAL(ε))
  - compute_ns_hamiltonian (classical NS limit)
  - epsilon_boundary_sweep (controlled blow-up experiment)
  - prove_convergence_limit (lim_{ε→0} Ĥ_QCAL(ε) = Ĥ_NS)
"""

import math
import unittest

import numpy as np

from qcal.convergence_proof import (
    TachyonCensor,
    RegularizedQCALHamiltonian,
    compute_ns_hamiltonian,
    epsilon_boundary_sweep,
    prove_convergence_limit,
    SIGMA_CRITICAL,
    EPSILON_DEFAULT,
    EPSILON_DIRAC_THRESHOLD,
    NU_GACT,
    H1_FINITE_BOUND,
)
from qcal.spectral_operator import F0, RIEMANN_ZEROS


class TestTachyonCensorInit(unittest.TestCase):
    """Initialization and basic properties of TachyonCensor."""

    def test_default_epsilon(self) -> None:
        """Default epsilon must equal EPSILON_DEFAULT."""
        tc = TachyonCensor()
        self.assertAlmostEqual(tc.epsilon, EPSILON_DEFAULT, places=10)

    def test_custom_epsilon(self) -> None:
        """Custom epsilon is stored correctly."""
        tc = TachyonCensor(epsilon=1e-3)
        self.assertAlmostEqual(tc.epsilon, 1e-3, places=15)

    def test_sigma_c_is_critical(self) -> None:
        """Censor is centered on the critical line σ = 0.5."""
        tc = TachyonCensor()
        self.assertAlmostEqual(tc.sigma_c, SIGMA_CRITICAL, places=10)
        self.assertAlmostEqual(tc.sigma_c, 0.5, places=10)

    def test_raises_on_zero_epsilon(self) -> None:
        """Zero bandwidth must raise ValueError."""
        with self.assertRaises(ValueError):
            TachyonCensor(epsilon=0.0)

    def test_raises_on_negative_epsilon(self) -> None:
        """Negative bandwidth must raise ValueError."""
        with self.assertRaises(ValueError):
            TachyonCensor(epsilon=-0.1)


class TestTachyonCensorFilter(unittest.TestCase):
    """Lorentzian filter behavior."""

    def setUp(self) -> None:
        self.tc = TachyonCensor(epsilon=0.1)

    def test_filter_at_critical_line(self) -> None:
        """Filter value at σ = 0.5 equals 1/(π·ε)."""
        expected = 1.0 / (math.pi * self.tc.epsilon)
        self.assertAlmostEqual(self.tc.filter(0.5), expected, places=10)

    def test_filter_nonnegative(self) -> None:
        """Filter is non-negative everywhere."""
        for sigma in [0.0, 0.25, 0.5, 0.75, 1.0]:
            self.assertGreaterEqual(self.tc.filter(sigma), 0.0)

    def test_filter_peak_at_critical_line(self) -> None:
        """Filter is maximised at σ = 0.5."""
        peak = self.tc.filter(0.5)
        for sigma in [0.0, 0.25, 0.75, 1.0]:
            self.assertLess(self.tc.filter(sigma), peak)

    def test_filter_array_shape(self) -> None:
        """filter_array returns an array with the same shape as input."""
        sigmas = np.linspace(0.0, 1.0, 100)
        result = self.tc.filter_array(sigmas)
        self.assertEqual(result.shape, sigmas.shape)

    def test_filter_array_matches_scalar(self) -> None:
        """filter_array values match scalar filter values."""
        sigmas = np.array([0.0, 0.25, 0.5, 0.75, 1.0])
        arr = self.tc.filter_array(sigmas)
        for i, s in enumerate(sigmas):
            self.assertAlmostEqual(float(arr[i]), self.tc.filter(float(s)), places=12)

    def test_filter_symmetric(self) -> None:
        """Lorentzian is symmetric around σ = 0.5."""
        self.assertAlmostEqual(
            self.tc.filter(0.4), self.tc.filter(0.6), places=12
        )
        self.assertAlmostEqual(
            self.tc.filter(0.3), self.tc.filter(0.7), places=12
        )

    def test_peak_increases_as_epsilon_decreases(self) -> None:
        """Smaller ε gives higher peak (Delta behavior)."""
        tc_small = TachyonCensor(epsilon=1e-4)
        tc_large = TachyonCensor(epsilon=1.0)
        self.assertGreater(tc_small.peak_value(), tc_large.peak_value())


class TestTachyonCensorProperties(unittest.TestCase):
    """Normalized weight, Dirac limit, and integral approximation."""

    def test_normalized_weight_constant(self) -> None:
        """Normalized weight ε·L(0.5;ε) = 1/π for all ε."""
        expected = 1.0 / math.pi
        for eps in [1e-1, 1e-2, 1e-3, 1e-4]:
            tc = TachyonCensor(epsilon=eps)
            self.assertAlmostEqual(tc.normalized_weight(), expected, places=10)

    def test_is_dirac_limit_false_large_epsilon(self) -> None:
        """Large ε (0.1) does not approximate the Dirac delta."""
        self.assertFalse(TachyonCensor(epsilon=0.1).is_dirac_limit())

    def test_is_dirac_limit_true_small_epsilon(self) -> None:
        """Small ε (< EPSILON_DIRAC_THRESHOLD) approximates the Dirac delta."""
        self.assertTrue(
            TachyonCensor(epsilon=EPSILON_DIRAC_THRESHOLD * 0.5).is_dirac_limit()
        )

    def test_is_dirac_limit_boundary(self) -> None:
        """ε exactly at threshold is not in the Dirac limit (strict inequality)."""
        self.assertFalse(TachyonCensor(epsilon=EPSILON_DIRAC_THRESHOLD).is_dirac_limit())

    def test_integral_approaches_one(self) -> None:
        """∫₀¹ L(σ;ε)dσ → 1 as ε → 0 (Dirac mass concentrates at σ=0.5)."""
        tc_large = TachyonCensor(epsilon=1.0)
        tc_small = TachyonCensor(epsilon=1e-4)
        integral_large = tc_large.integral_approximation()
        integral_small = tc_small.integral_approximation()
        self.assertLess(integral_large, integral_small)
        self.assertAlmostEqual(integral_small, 1.0, places=2)


class TestRegularizedQCALHamiltonian(unittest.TestCase):
    """Tests for Ĥ_QCAL(ε)."""

    def setUp(self) -> None:
        self.H = RegularizedQCALHamiltonian(epsilon=1e-2)

    def test_epsilon_stored(self) -> None:
        """Epsilon is stored correctly."""
        self.assertAlmostEqual(self.H.epsilon, 1e-2, places=15)

    def test_censor_is_tachyon_censor(self) -> None:
        """Operator has a TachyonCensor attribute."""
        self.assertIsInstance(self.H.censor, TachyonCensor)

    def test_h1_norm_positive(self) -> None:
        """H¹ norm is strictly positive."""
        self.assertGreater(self.H.h1_norm(), 0.0)

    def test_h1_norm_finite(self) -> None:
        """H¹ norm is finite for any ε > 0."""
        for eps in [1e-1, 1e-2, 1e-3, 1e-6]:
            H = RegularizedQCALHamiltonian(epsilon=eps)
            h1 = H.h1_norm()
            self.assertTrue(math.isfinite(h1), f"H¹ norm not finite at ε={eps}")

    def test_h1_norm_increases_as_epsilon_decreases(self) -> None:
        """‖u_ε‖_{H¹} increases monotonically as ε → 0."""
        epsilons = [1e-1, 1e-2, 1e-3, 1e-4, 1e-5]
        norms = [RegularizedQCALHamiltonian(epsilon=e).h1_norm() for e in epsilons]
        for i in range(len(norms) - 1):
            self.assertLess(
                norms[i], norms[i + 1],
                f"H¹ norm did not increase between ε={epsilons[i]} and ε={epsilons[i+1]}"
            )

    def test_h1_norm_bounded_by_ns_limit(self) -> None:
        """‖u_ε‖_{H¹} ≤ ‖u_NS‖_{H¹} for all ε > 0."""
        ns = compute_ns_hamiltonian()
        h1_ns = ns["h1_norm_ns"]
        for eps in [1e-1, 1e-2, 1e-3]:
            H = RegularizedQCALHamiltonian(epsilon=eps)
            self.assertLessEqual(H.h1_norm(), h1_ns + 1e-12)

    def test_spectral_energy_positive(self) -> None:
        """Spectral energy is positive for coherent state."""
        E = self.H.spectral_energy(psi=1.0, C=1.0)
        self.assertGreater(E, 0.0)

    def test_spectral_energy_raises_zero_C(self) -> None:
        """C = 0 must propagate ValueError from compute_v_mod."""
        with self.assertRaises(ValueError):
            self.H.spectral_energy(psi=1.0, C=0.0)

    def test_apply_keys(self) -> None:
        """apply() returns all required keys."""
        result = self.H.apply(psi=1.0, C=1.0)
        for key in ("epsilon", "psi", "energia_espectral", "h1_norm",
                    "peso_normalizado", "is_dirac_limit", "nu", "K"):
            self.assertIn(key, result)

    def test_apply_epsilon_matches(self) -> None:
        """apply() result epsilon matches operator epsilon."""
        result = self.H.apply(psi=1.0, C=1.0)
        self.assertAlmostEqual(result["epsilon"], 1e-2, places=15)

    def test_apply_normalized_weight_is_inv_pi(self) -> None:
        """Normalized weight in apply() is 1/π."""
        result = self.H.apply(psi=1.0, C=1.0)
        self.assertAlmostEqual(result["peso_normalizado"], 1.0 / math.pi, places=10)

    def test_custom_num_zeros(self) -> None:
        """Custom num_zeros changes spectral sum."""
        H10 = RegularizedQCALHamiltonian(epsilon=1e-2, num_zeros=10)
        H50 = RegularizedQCALHamiltonian(epsilon=1e-2, num_zeros=50)
        self.assertNotAlmostEqual(H10.h1_norm(), H50.h1_norm(), places=5)


class TestComputeNSHamiltonian(unittest.TestCase):
    """Tests for the Navier-Stokes limit (ε = 0)."""

    def setUp(self) -> None:
        self.ns = compute_ns_hamiltonian()

    def test_epsilon_is_zero(self) -> None:
        """NS limit corresponds to ε = 0."""
        self.assertEqual(self.ns["epsilon"], 0.0)

    def test_h1_ns_finite(self) -> None:
        """‖u_NS‖_{H¹} must be finite (Σ 1/γ_n² converges)."""
        h1 = self.ns["h1_norm_ns"]
        self.assertTrue(math.isfinite(h1))

    def test_h1_ns_positive(self) -> None:
        """‖u_NS‖_{H¹} is strictly positive."""
        self.assertGreater(self.ns["h1_norm_ns"], 0.0)

    def test_estado_h1_regular(self) -> None:
        """Estado must be 'H1_REGULAR' when sum converges."""
        self.assertEqual(self.ns["estado"], "H1_REGULAR")

    def test_convergencia_espectral(self) -> None:
        """convergencia_espectral must be True."""
        self.assertTrue(self.ns["convergencia_espectral"])

    def test_h1_ns_exceeds_regularized(self) -> None:
        """NS limit H¹ norm exceeds all ε > 0 regularized norms."""
        h1_ns = self.ns["h1_norm_ns"]
        for eps in [1e-1, 1e-2, 1e-3]:
            H = RegularizedQCALHamiltonian(epsilon=eps)
            self.assertGreater(h1_ns, H.h1_norm())

    def test_custom_num_zeros(self) -> None:
        """Custom num_zeros is reflected in the result."""
        ns10 = compute_ns_hamiltonian(num_zeros=10)
        self.assertEqual(ns10["num_zeros"], 10)
        self.assertGreater(self.ns["h1_norm_ns"], 0.0)

    def test_custom_nu_stored(self) -> None:
        """Custom nu value is returned in result dict."""
        ns = compute_ns_hamiltonian(nu=1e-3)
        self.assertAlmostEqual(ns["nu"], 1e-3, places=15)

    def test_custom_K_stored(self) -> None:
        """Custom K value is returned in result dict."""
        ns = compute_ns_hamiltonian(K=2.0)
        self.assertAlmostEqual(ns["K"], 2.0, places=10)


class TestEpsilonBoundarySweep(unittest.TestCase):
    """Tests for the controlled blow-up experiment."""

    def setUp(self) -> None:
        self.sweep = epsilon_boundary_sweep()

    def test_sweep_results_count(self) -> None:
        """Default sweep has 6 results."""
        self.assertEqual(len(self.sweep["sweep_results"]), 6)

    def test_all_h1_finite(self) -> None:
        """H¹ norm must be finite at every ε step."""
        self.assertTrue(self.sweep["h1_finite"])
        for r in self.sweep["sweep_results"]:
            self.assertTrue(r["is_finite"], f"H¹ not finite at ε={r['epsilon']}")

    def test_converges_to_ns(self) -> None:
        """The sweep must converge toward the NS limit."""
        self.assertTrue(self.sweep["converges"])

    def test_convergencia_verificada(self) -> None:
        """Overall convergence flag must be True."""
        self.assertTrue(self.sweep["convergencia_verificada"])

    def test_prediccion_riemann_regularizes(self) -> None:
        """Prediction must report natural Riemann regularization."""
        self.assertIn("GEOMETRÍA DE RIEMANN", self.sweep["prediccion"])

    def test_h1_ns_limit_positive(self) -> None:
        """NS limit norm is positive."""
        self.assertGreater(self.sweep["h1_ns_limit"], 0.0)

    def test_h1_norm_increases_with_decreasing_epsilon(self) -> None:
        """‖u_ε‖_{H¹} increases as ε decreases across sweep steps."""
        norms = [r["h1_norm"] for r in self.sweep["sweep_results"]]
        for i in range(len(norms) - 1):
            self.assertLess(norms[i], norms[i + 1])

    def test_delta_from_ns_decreases(self) -> None:
        """Distance to NS limit decreases as ε decreases."""
        deltas = [r["delta_from_ns"] for r in self.sweep["sweep_results"]]
        for i in range(len(deltas) - 1):
            self.assertGreater(deltas[i], deltas[i + 1])

    def test_dirac_limit_at_small_epsilon(self) -> None:
        """Steps with ε < EPSILON_DIRAC_THRESHOLD are flagged as Dirac limit."""
        for r in self.sweep["sweep_results"]:
            if r["epsilon"] < EPSILON_DIRAC_THRESHOLD:
                self.assertTrue(r["is_dirac_limit"])

    def test_custom_epsilons(self) -> None:
        """Custom epsilon sequence is respected."""
        custom = [1e-1, 1e-3, 1e-5]
        result = epsilon_boundary_sweep(epsilons=custom)
        self.assertEqual(len(result["sweep_results"]), 3)
        for r, e in zip(result["sweep_results"], custom):
            self.assertAlmostEqual(r["epsilon"], e, places=15)

    def test_no_blowup(self) -> None:
        """H¹ norm stays well below the finite bound throughout."""
        for r in self.sweep["sweep_results"]:
            self.assertLess(r["h1_norm"], H1_FINITE_BOUND)


class TestProveConvergenceLimit(unittest.TestCase):
    """Tests for the convergence limit proof."""

    def setUp(self) -> None:
        self.proof = prove_convergence_limit()

    def test_convergencia_demostrada(self) -> None:
        """Convergence must be demonstrated with default parameters."""
        self.assertTrue(self.proof["convergencia_demostrada"])

    def test_estado_probada(self) -> None:
        """Estado must indicate proven convergence."""
        self.assertIn("CONVERGENCIA_PROBADA", self.proof["estado"])

    def test_decrecimiento_monotono(self) -> None:
        """Error must decrease monotonically as ε → 0."""
        self.assertTrue(self.proof["decrecimiento_monotono"])

    def test_error_final_below_tolerance(self) -> None:
        """Final error must be below the default tolerance."""
        self.assertLess(self.proof["error_final"], self.proof["tolerancia"])

    def test_tabla_convergencia_keys(self) -> None:
        """Each row in tabla_convergencia has all required keys."""
        for row in self.proof["tabla_convergencia"]:
            for key in ("epsilon", "h1_qcal", "h1_ns", "error", "dentro_tolerancia"):
                self.assertIn(key, row)

    def test_h1_ns_positive(self) -> None:
        """h1_ns in proof is positive."""
        self.assertGreater(self.proof["h1_ns"], 0.0)

    def test_final_row_within_tolerance(self) -> None:
        """The last row (smallest ε) must be within tolerance."""
        last = self.proof["tabla_convergencia"][-1]
        self.assertTrue(last["dentro_tolerancia"])

    def test_errors_nonnegative(self) -> None:
        """All errors are non-negative."""
        for row in self.proof["tabla_convergencia"]:
            self.assertGreaterEqual(row["error"], 0.0)

    def test_reclasificacion_keys_present(self) -> None:
        """Reclassification dict must contain all three keys."""
        reclass = self.proof["reclasificacion"]
        for key in ("fisica_clasica", "materia", "consciencia"):
            self.assertIn(key, reclass)

    def test_reclasificacion_fisica_clasica(self) -> None:
        """Classical physics is described as QCAL with Ψ=1.0 and ε=0."""
        self.assertIn("ε=0", self.proof["reclasificacion"]["fisica_clasica"])

    def test_custom_tol(self) -> None:
        """Custom tolerance is stored and used."""
        proof = prove_convergence_limit(tol=1e-2)
        self.assertAlmostEqual(proof["tolerancia"], 1e-2, places=15)

    def test_custom_num_zeros(self) -> None:
        """Custom num_zeros changes h1_ns."""
        proof10 = prove_convergence_limit(num_zeros=10)
        proof50 = prove_convergence_limit(num_zeros=50)
        self.assertNotAlmostEqual(proof10["h1_ns"], proof50["h1_ns"], places=5)

    def test_h1_qcal_converges_to_h1_ns(self) -> None:
        """h1_qcal values approach h1_ns as ε decreases."""
        rows = self.proof["tabla_convergencia"]
        h1_ns = self.proof["h1_ns"]
        h1_vals = [r["h1_qcal"] for r in rows]
        # Each h1_qcal must be ≤ h1_ns (approaches from below)
        for v in h1_vals:
            self.assertLessEqual(v, h1_ns + 1e-12)
        # Values increase toward h1_ns
        for i in range(len(h1_vals) - 1):
            self.assertLessEqual(h1_vals[i], h1_vals[i + 1] + 1e-12)


class TestQCALPackageExports(unittest.TestCase):
    """Verify that new symbols are accessible via the qcal package."""

    def test_import_tachyon_censor(self) -> None:
        """TachyonCensor must be importable from qcal."""
        from qcal import TachyonCensor as TC
        self.assertIs(TC, TachyonCensor)

    def test_import_regularized_hamiltonian(self) -> None:
        """RegularizedQCALHamiltonian must be importable from qcal."""
        from qcal import RegularizedQCALHamiltonian as RH
        self.assertIs(RH, RegularizedQCALHamiltonian)

    def test_import_compute_ns_hamiltonian(self) -> None:
        """compute_ns_hamiltonian must be importable from qcal."""
        from qcal import compute_ns_hamiltonian as cns
        self.assertIs(cns, compute_ns_hamiltonian)

    def test_import_epsilon_boundary_sweep(self) -> None:
        """epsilon_boundary_sweep must be importable from qcal."""
        from qcal import epsilon_boundary_sweep as ebs
        self.assertIs(ebs, epsilon_boundary_sweep)

    def test_import_prove_convergence_limit(self) -> None:
        """prove_convergence_limit must be importable from qcal."""
        from qcal import prove_convergence_limit as pcl
        self.assertIs(pcl, prove_convergence_limit)

    def test_import_sigma_critical(self) -> None:
        """SIGMA_CRITICAL constant must be importable from qcal."""
        from qcal import SIGMA_CRITICAL as SC
        self.assertAlmostEqual(SC, 0.5, places=10)

    def test_import_nu_gact(self) -> None:
        """NU_GACT constant must be importable from qcal."""
        from qcal import NU_GACT as NG
        self.assertAlmostEqual(NG, 2.245e-4, places=10)


class TestConstants(unittest.TestCase):
    """Tests for module-level constants."""

    def test_sigma_critical(self) -> None:
        self.assertAlmostEqual(SIGMA_CRITICAL, 0.5, places=10)

    def test_epsilon_default(self) -> None:
        self.assertAlmostEqual(EPSILON_DEFAULT, 0.1, places=10)

    def test_epsilon_dirac_threshold(self) -> None:
        self.assertAlmostEqual(EPSILON_DIRAC_THRESHOLD, 1e-3, places=15)

    def test_nu_gact(self) -> None:
        self.assertAlmostEqual(NU_GACT, 2.245e-4, places=10)

    def test_h1_finite_bound_large(self) -> None:
        self.assertGreater(H1_FINITE_BOUND, 1.0)


if __name__ == "__main__":
    unittest.main(verbosity=2)
