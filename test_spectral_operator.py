#!/usr/bin/env python3
"""
Tests for QCALSpectralOperator
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Pruebas unitarias para qcal.spectral_operator.QCALSpectralOperator.

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
License: MIT
"""

import math
import unittest
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))

from qcal.spectral_operator import QCALSpectralOperator, F0, GAMMA_1, PSI_MIN


class TestQCALSpectralOperatorInit(unittest.TestCase):
    """Tests de inicialización del operador."""

    def test_default_init(self):
        op = QCALSpectralOperator()
        self.assertEqual(op.gamma, 1.0)
        self.assertEqual(op.C, 1.0)
        self.assertAlmostEqual(op.f0, F0)

    def test_custom_init(self):
        op = QCALSpectralOperator(gamma=2.0, consciousness_density=3.0)
        self.assertEqual(op.gamma, 2.0)
        self.assertEqual(op.C, 3.0)

    def test_invalid_gamma_raises(self):
        with self.assertRaises(ValueError):
            QCALSpectralOperator(gamma=0.0)
        with self.assertRaises(ValueError):
            QCALSpectralOperator(gamma=-1.0)

    def test_invalid_consciousness_density_raises(self):
        with self.assertRaises(ValueError):
            QCALSpectralOperator(consciousness_density=0.0)
        with self.assertRaises(ValueError):
            QCALSpectralOperator(consciousness_density=-0.5)


class TestModulationPotential(unittest.TestCase):
    """Tests del potencial de modulación V̂_mod = γ · ℏ / C."""

    def setUp(self):
        self.op = QCALSpectralOperator(gamma=1.0, consciousness_density=1.0)

    def test_modulation_potential_positive(self):
        v = self.op.modulation_potential()
        self.assertGreater(v, 0.0)

    def test_modulation_potential_formula(self):
        op = QCALSpectralOperator(gamma=2.0, consciousness_density=4.0)
        expected = 2.0 * op.hbar / 4.0
        self.assertAlmostEqual(op.modulation_potential(), expected)


class TestBerryKeatingEigenvalue(unittest.TestCase):
    """Tests del autovalor Berry-Keating."""

    def setUp(self):
        self.op = QCALSpectralOperator()

    def test_returns_gamma_n_unchanged(self):
        for gamma_n in [14.134725, 21.022040, 25.010858]:
            self.assertEqual(self.op.berry_keating_eigenvalue(gamma_n), gamma_n)


class TestComputeEigenvalue(unittest.TestCase):
    """Tests del autovalor resonante λ_n."""

    def setUp(self):
        self.op = QCALSpectralOperator()

    def test_first_riemann_zero_eigenvalue(self):
        lam = self.op.compute_eigenvalue(GAMMA_1)
        # λ₁ ≈ 14.1347 * 141.7001 + V̂_mod ≈ 2002.89 Hz
        self.assertAlmostEqual(lam, 2002.89, delta=1.0)

    def test_eigenvalue_exceeds_gamma_n_times_f0(self):
        gamma_n = 14.134725
        lam = self.op.compute_eigenvalue(gamma_n)
        base = gamma_n * self.op.f0
        # λ_n >= γ_n · f₀ (V̂_mod ≥ 0)
        self.assertGreaterEqual(lam, base)


class TestIsHermitian(unittest.TestCase):
    """Tests de hermiticidad."""

    def test_default_is_hermitian(self):
        op = QCALSpectralOperator()
        self.assertTrue(op.is_hermitian())

    def test_positive_params_hermitian(self):
        op = QCALSpectralOperator(gamma=0.5, consciousness_density=2.0)
        self.assertTrue(op.is_hermitian())


class TestCertifyCriticalLine(unittest.TestCase):
    """Tests de certificación de línea crítica."""

    def setUp(self):
        self.op = QCALSpectralOperator()

    def test_critical_line_sigma_half_certified(self):
        certified, psi = self.op.certify_critical_line(0.5)
        self.assertTrue(certified)
        self.assertAlmostEqual(psi, 1.0)

    def test_off_critical_sigma_1_not_certified(self):
        certified, psi = self.op.certify_critical_line(1.0)
        self.assertFalse(certified)
        self.assertLess(psi, PSI_MIN)

    def test_psi_monotone_decreasing_away_from_half(self):
        _, psi_05 = self.op.certify_critical_line(0.5)
        _, psi_06 = self.op.certify_critical_line(0.6)
        # psi_05 = 1.0, psi_06 < 1.0 (sharp decay due to large hbar denominator)
        self.assertGreater(psi_05, psi_06)

    def test_symmetric_around_half(self):
        _, psi_plus = self.op.certify_critical_line(0.5 + 0.1)
        _, psi_minus = self.op.certify_critical_line(0.5 - 0.1)
        self.assertAlmostEqual(psi_plus, psi_minus, places=12)


class TestVerifyOffCriticalZeros(unittest.TestCase):
    """Tests de verificación de ceros off-critical."""

    def setUp(self):
        self.op = QCALSpectralOperator()

    def test_no_off_critical_zeros_certified(self):
        verified, msg = self.op.verify_off_critical_zeros([0.5, 0.6, 1.0, 0.4])
        self.assertTrue(verified)
        self.assertIn("∅", msg)

    def test_only_critical_line_passes(self):
        verified, _ = self.op.verify_off_critical_zeros([0.5])
        # sigma=0.5 es on-critical, off_critical list is empty → verified
        self.assertTrue(verified)


class TestGetSpectralTable(unittest.TestCase):
    """Tests de la tabla espectral."""

    def setUp(self):
        self.op = QCALSpectralOperator()

    def test_spectral_table_keys(self):
        table = self.op.get_spectral_table()
        for key in ["lambda_0", "hermiticidad", "psi_critica", "psi_off_critical", "resonancia_aprox_hz"]:
            self.assertIn(key, table)

    def test_spectral_table_hermitian_true(self):
        table = self.op.get_spectral_table()
        self.assertTrue(table["hermiticidad"])

    def test_spectral_table_psi_critica_one(self):
        table = self.op.get_spectral_table()
        self.assertAlmostEqual(table["psi_critica"], 1.0)

    def test_spectral_table_resonancia_approx(self):
        table = self.op.get_spectral_table()
        # λ₁ ≈ 2003 Hz (rounded)
        self.assertAlmostEqual(table["resonancia_aprox_hz"], 2003, delta=2)


class TestEstadoQEDRiemann(unittest.TestCase):
    """Tests del estado de certificación global."""

    def test_estado_string(self):
        op = QCALSpectralOperator()
        self.assertEqual(op.estado_qed_riemann(), "QED-RIEMANN-VERIFIED")


class TestQCALPackageImport(unittest.TestCase):
    """Tests de importación del paquete qcal."""

    def test_import_qcal_spectral_operator(self):
        from qcal import QCALSpectralOperator as QSO
        op = QSO()
        self.assertIsNotNone(op)

    def test_import_qcal_constants(self):
        import qcal
        self.assertAlmostEqual(qcal.F0, 141.7001)
        self.assertEqual(qcal.PSI_MIN, 0.888)
        self.assertEqual(qcal.NODOS_LOGOS, 51)

    def test_import_sincronizar_bsd_adn(self):
        from qcal import sincronizar_bsd_adn
        self.assertTrue(callable(sincronizar_bsd_adn))


if __name__ == "__main__":
    unittest.main(verbosity=2)
