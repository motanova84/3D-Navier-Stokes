#!/usr/bin/env python3
"""
Tests for the QCAL Spectral Operator module.

Validates Ĥ_QCAL = Ĥ_BK ⊗ 𝕀_{f₀} + V̂_mod and the critical-line certification.
"""

import unittest
import math

import numpy as np

from qcal.spectral_operator import (
    BerryKeatingOperator,
    IdentityProjectorF0,
    QCALSpectralOperator,
    compute_v_mod,
    certificar_riemann_qcal,
    F0,
    PSI_MIN,
    HBAR,
    GAMMA_MOD,
    RESONANCIA_888,
    RIEMANN_ZEROS,
)


class TestBerryKeatingOperator(unittest.TestCase):
    """Tests for Ĥ_BK — Berry-Keating operator."""

    def setUp(self) -> None:
        self.op = BerryKeatingOperator(num_zeros=10)

    def test_eigenvalues_count(self) -> None:
        """Operator returns exactly the requested number of eigenvalues."""
        self.assertEqual(len(self.op.get_eigenvalues()), 10)

    def test_eigenvalues_are_real(self) -> None:
        """All eigenvalues must be real (Hermitian operator requirement)."""
        evs = self.op.get_eigenvalues()
        self.assertTrue(np.all(np.isreal(evs)))

    def test_eigenvalues_match_riemann_zeros(self) -> None:
        """Eigenvalues equal the first N non-trivial Riemann zeros."""
        evs = self.op.get_eigenvalues()
        expected = np.array(RIEMANN_ZEROS[:10])
        np.testing.assert_array_almost_equal(evs, expected)

    def test_is_hermitian(self) -> None:
        """Operator must report itself as Hermitian."""
        self.assertTrue(self.op.is_hermitian())

    def test_eigenvalues_positive(self) -> None:
        """Imaginary parts of Riemann zeros are all positive."""
        evs = self.op.get_eigenvalues()
        self.assertTrue(np.all(evs > 0))

    def test_spectral_density_positive(self) -> None:
        """Spectral density at f₀ must be positive."""
        density = self.op.spectral_density(F0)
        self.assertGreater(density, 0.0)

    def test_num_zeros_clamped_at_max(self) -> None:
        """Requesting more zeros than available silently caps at max."""
        op = BerryKeatingOperator(num_zeros=9999)
        self.assertLessEqual(len(op.get_eigenvalues()), len(RIEMANN_ZEROS))


class TestIdentityProjectorF0(unittest.TestCase):
    """Tests for 𝕀_{f₀} — identity projector at base frequency."""

    def setUp(self) -> None:
        self.proj = IdentityProjectorF0()

    def test_eigenvalue_is_f0(self) -> None:
        """Reference eigenvalue λ₀ must equal f₀ = 141.7001 Hz."""
        self.assertAlmostEqual(self.proj.eigenvalue(), F0, places=4)

    def test_project_above_threshold(self) -> None:
        """Coherent state (Ψ ≥ 0.888) projects onto f₀."""
        self.assertAlmostEqual(self.proj.project(PSI_MIN), F0, places=4)
        self.assertAlmostEqual(self.proj.project(1.0), F0, places=4)
        self.assertAlmostEqual(self.proj.project(0.95), F0, places=4)

    def test_project_below_threshold(self) -> None:
        """Incoherent state (Ψ < 0.888) collapses to 0."""
        self.assertEqual(self.proj.project(0.0), 0.0)
        self.assertEqual(self.proj.project(0.5), 0.0)
        self.assertAlmostEqual(self.proj.project(0.887), 0.0, places=5)

    def test_custom_f0(self) -> None:
        """Projector respects a custom f₀ value."""
        proj = IdentityProjectorF0(f0=432.0)
        self.assertAlmostEqual(proj.eigenvalue(), 432.0, places=6)
        self.assertAlmostEqual(proj.project(1.0), 432.0, places=6)


class TestComputeVMod(unittest.TestCase):
    """Tests for V̂_mod ∝ γℏ/C — modulation potential."""

    def test_proportional_to_gamma(self) -> None:
        """V̂_mod scales linearly with γ."""
        v1 = compute_v_mod(gamma=1.0, C=1.0)
        v2 = compute_v_mod(gamma=2.0, C=1.0)
        self.assertAlmostEqual(v2, 2.0 * v1, places=14)

    def test_inversely_proportional_to_C(self) -> None:
        """V̂_mod is inversely proportional to C."""
        v1 = compute_v_mod(gamma=1.0, C=1.0)
        v2 = compute_v_mod(gamma=1.0, C=2.0)
        self.assertAlmostEqual(v2, v1 / 2.0, places=14)

    def test_proportional_to_hbar(self) -> None:
        """V̂_mod scales with ℏ."""
        v1 = compute_v_mod(gamma=1.0, hbar=HBAR, C=1.0)
        v2 = compute_v_mod(gamma=1.0, hbar=2.0 * HBAR, C=1.0)
        self.assertAlmostEqual(v2, 2.0 * v1, places=14)

    def test_raises_on_zero_C(self) -> None:
        """C = 0 must raise ValueError."""
        with self.assertRaises(ValueError):
            compute_v_mod(C=0.0)

    def test_raises_on_negative_C(self) -> None:
        """C < 0 must raise ValueError."""
        with self.assertRaises(ValueError):
            compute_v_mod(C=-1.0)

    def test_default_values(self) -> None:
        """Default call returns a small positive value (γ=1, ℏ≈1.05e-34, C=1)."""
        v = compute_v_mod()
        self.assertGreater(v, 0.0)
        self.assertAlmostEqual(v, GAMMA_MOD * HBAR / 1.0, places=14)


class TestQCALSpectralOperator(unittest.TestCase):
    """Tests for Ĥ_QCAL = Ĥ_BK ⊗ 𝕀_{f₀} + V̂_mod."""

    def setUp(self) -> None:
        self.op = QCALSpectralOperator()

    def test_is_hermitian(self) -> None:
        """Combined operator must be Hermitian."""
        self.assertTrue(self.op.is_hermitian())

    def test_apply_coherent_state(self) -> None:
        """Applying operator to a coherent state (Ψ ≥ 0.888) returns valid result."""
        result = self.op.apply(psi=1.0, C=1.0)
        self.assertTrue(result['coherente'])
        self.assertTrue(result['on_critical_line'])
        self.assertAlmostEqual(result['proyeccion_f0'], F0, places=4)
        self.assertGreater(result['energia_total'], 0.0)

    def test_apply_incoherent_state(self) -> None:
        """Applying operator to an incoherent state (Ψ < 0.888) returns projection = 0."""
        result = self.op.apply(psi=0.5, C=1.0)
        self.assertFalse(result['coherente'])
        self.assertEqual(result['proyeccion_f0'], 0.0)

    def test_apply_raises_on_zero_C(self) -> None:
        """C = 0 must propagate ValueError from compute_v_mod."""
        with self.assertRaises(ValueError):
            self.op.apply(psi=1.0, C=0.0)

    def test_certificar_linea_critica_estado(self) -> None:
        """Certification must return QED-RIEMANN-VERIFIED."""
        cert = self.op.certificar_linea_critica()
        self.assertEqual(cert['estado'], 'QED-RIEMANN-VERIFIED')
        self.assertTrue(cert['certificado'])

    def test_certificar_linea_critica_empty_off_critical(self) -> None:
        """Off-critical zeros set must be empty — ∅."""
        cert = self.op.certificar_linea_critica()
        self.assertEqual(cert['ceros_off_critical'], [])

    def test_certificar_linea_critica_base_eigenvalue(self) -> None:
        """Base eigenvalue λ₀ must equal f₀."""
        cert = self.op.certificar_linea_critica()
        self.assertAlmostEqual(cert['autovalor_base'], F0, places=4)

    def test_certificar_linea_critica_resonance(self) -> None:
        """Resonance must be reported as 888 Hz (6th harmonic)."""
        cert = self.op.certificar_linea_critica()
        self.assertAlmostEqual(cert['resonancia_hz'], RESONANCIA_888, places=3)

    def test_certificar_linea_critica_num_zeros(self) -> None:
        """Number of examined zeros matches initialization."""
        op = QCALSpectralOperator(num_zeros=20)
        cert = op.certificar_linea_critica()
        self.assertEqual(cert['num_ceros_examinados'], 20)


class TestCertificarRiemannQCAL(unittest.TestCase):
    """Tests for the top-level certificar_riemann_qcal() function."""

    def setUp(self) -> None:
        self.result = certificar_riemann_qcal()

    def test_sistema_verified(self) -> None:
        """Top-level result must be QED-RIEMANN-VERIFIED."""
        self.assertEqual(self.result['sistema'], 'QED-RIEMANN-VERIFIED')

    def test_parametro_keys_present(self) -> None:
        """All four spectral parameter keys must be present."""
        for key in ('Autovalor Base', 'Operador', 'Ceros Off-Critical', 'Resonancia'):
            self.assertIn(key, self.result['parametro'])

    def test_estado_keys_present(self) -> None:
        """Status dict must have all four keys."""
        for key in ('Autovalor Base', 'Operador', 'Ceros Off-Critical', 'Resonancia'):
            self.assertIn(key, self.result['estado'])

    def test_off_critical_empty(self) -> None:
        """Off-critical zeros must report as empty set."""
        self.assertIn('∅', self.result['parametro']['Ceros Off-Critical'])

    def test_operador_hermitian_status(self) -> None:
        """Operator status must indicate hermitian certification."""
        self.assertIn('Certificado', self.result['estado']['Operador'])

    def test_autovalor_base_contains_f0(self) -> None:
        """Base eigenvalue string must contain the f₀ value."""
        self.assertIn(str(F0), self.result['parametro']['Autovalor Base'])

    def test_resonancia_contains_888(self) -> None:
        """Resonance string must mention 888 Hz."""
        self.assertIn('888', self.result['parametro']['Resonancia'])

    def test_custom_C(self) -> None:
        """Different C values should all produce QED-RIEMANN-VERIFIED."""
        for C in (0.5, 1.0, 10.0, 100.0):
            res = certificar_riemann_qcal(C=C)
            self.assertEqual(res['sistema'], 'QED-RIEMANN-VERIFIED',
                             f"Failed for C={C}")

    def test_custom_num_zeros(self) -> None:
        """Custom number of zeros must be reflected in certification."""
        res = certificar_riemann_qcal(num_zeros=5)
        self.assertEqual(res['certificacion']['num_ceros_examinados'], 5)
        self.assertEqual(res['sistema'], 'QED-RIEMANN-VERIFIED')

    def test_custom_f0(self) -> None:
        """Custom f₀ must appear in the base eigenvalue field."""
        res = certificar_riemann_qcal(f0=432.0)
        self.assertIn('432.0', res['parametro']['Autovalor Base'])


class TestConstants(unittest.TestCase):
    """Tests for module-level constants."""

    def test_f0_value(self) -> None:
        self.assertAlmostEqual(F0, 141.7001, places=4)

    def test_psi_min_value(self) -> None:
        self.assertAlmostEqual(PSI_MIN, 0.888, places=3)

    def test_hbar_value(self) -> None:
        self.assertAlmostEqual(HBAR, 1.0545718e-34, places=14)

    def test_resonancia_888_value(self) -> None:
        self.assertAlmostEqual(RESONANCIA_888, 888.0, places=3)

    def test_riemann_zeros_not_empty(self) -> None:
        self.assertGreater(len(RIEMANN_ZEROS), 0)

    def test_first_riemann_zero(self) -> None:
        """First non-trivial zero γ₁ ≈ 14.1347."""
        self.assertAlmostEqual(RIEMANN_ZEROS[0], 14.134725142, places=8)


if __name__ == '__main__':
    unittest.main(verbosity=2)
