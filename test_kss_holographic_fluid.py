#!/usr/bin/env python3
"""
Tests para KSS Holographic Fluid — Límite KSS del Citoplasma
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Pruebas unitarias para qcal.kss_holographic_fluid que implementa:
- Cálculo del límite KSS: ℏ/(4π k_B)
- Viscosidad desde decaimiento de rotores moleculares
- Densidad de entropía desde emisión de fotones ultra-débiles (UPE)
- Validación del Fluido Holográfico Perfecto (Ψ = 0.999999)
- Correspondencia Kaluza-Klein de microtúbulos

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
License: MIT
"""

import math
import sys
import unittest
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).parent))

from qcal.kss_holographic_fluid import (
    KSSHolographicFluid,
    KSSResult,
    compute_kss_bound,
    compute_viscosity_from_rotor_decay,
    compute_entropy_density_from_upe,
    HBAR,
    KB,
    KSS_BOUND,
    F_UPE_HZ,
    F0,
    T_CYTOPLASM_K,
    V_ROTOR_M3,
    PSI_HOLOGRAPHIC,
    KSS_PROXIMITY_FACTOR,
    SPEED_OF_LIGHT,
)


# ─────────────────────────────────────────────────────────────────────────────
# Tests: Physical constants
# ─────────────────────────────────────────────────────────────────────────────

class TestPhysicalConstants(unittest.TestCase):
    """Verify physical constants are correct."""

    def test_hbar_value(self):
        self.assertAlmostEqual(HBAR, 1.0545718e-34, places=15)

    def test_kb_value(self):
        self.assertAlmostEqual(KB, 1.380649e-23, places=29)

    def test_kss_bound_formula(self):
        """KSS_BOUND = ℏ/(4π k_B) ≈ 6.08e-13 s·K."""
        expected = HBAR / (4.0 * math.pi * KB)
        self.assertAlmostEqual(KSS_BOUND, expected, places=25)

    def test_kss_bound_order_of_magnitude(self):
        """KSS bound should be ~6e-13 s·K."""
        self.assertGreater(KSS_BOUND, 5e-13)
        self.assertLess(KSS_BOUND, 7e-13)

    def test_f_upe_hz(self):
        self.assertAlmostEqual(F_UPE_HZ, 2003.0)

    def test_f0(self):
        self.assertAlmostEqual(F0, 141.7001)

    def test_t_cytoplasm_k(self):
        """Physiological temperature 37 °C = 310.15 K."""
        self.assertAlmostEqual(T_CYTOPLASM_K, 310.15)

    def test_psi_holographic(self):
        self.assertAlmostEqual(PSI_HOLOGRAPHIC, 0.999999)


# ─────────────────────────────────────────────────────────────────────────────
# Tests: compute_kss_bound
# ─────────────────────────────────────────────────────────────────────────────

class TestComputeKSSBound(unittest.TestCase):
    """Test the standalone KSS bound function."""

    def test_returns_correct_value(self):
        result = compute_kss_bound()
        self.assertAlmostEqual(result, HBAR / (4.0 * math.pi * KB), places=25)

    def test_positive(self):
        self.assertGreater(compute_kss_bound(), 0.0)


# ─────────────────────────────────────────────────────────────────────────────
# Tests: compute_viscosity_from_rotor_decay
# ─────────────────────────────────────────────────────────────────────────────

class TestComputeViscosityFromRotorDecay(unittest.TestCase):
    """Test viscosity computation from molecular rotor fluorescence decay."""

    def test_basic_calculation(self):
        """η = k_B·T·τ / V_rotor."""
        tau = 1.0e-9  # 1 ns
        expected = KB * T_CYTOPLASM_K * tau / V_ROTOR_M3
        result = compute_viscosity_from_rotor_decay(tau)
        self.assertAlmostEqual(result, expected, places=5)

    def test_viscosity_scales_linearly_with_tau(self):
        """Doubling τ should double η."""
        tau1, tau2 = 1.0e-9, 2.0e-9
        eta1 = compute_viscosity_from_rotor_decay(tau1)
        eta2 = compute_viscosity_from_rotor_decay(tau2)
        self.assertAlmostEqual(eta2 / eta1, 2.0, places=10)

    def test_viscosity_scales_linearly_with_temperature(self):
        """Doubling T should double η."""
        tau = 1.0e-9
        eta1 = compute_viscosity_from_rotor_decay(tau, temperature_K=300.0)
        eta2 = compute_viscosity_from_rotor_decay(tau, temperature_K=600.0)
        self.assertAlmostEqual(eta2 / eta1, 2.0, places=10)

    def test_invalid_tau_raises(self):
        with self.assertRaises(ValueError):
            compute_viscosity_from_rotor_decay(-1.0e-9)

    def test_zero_tau_raises(self):
        with self.assertRaises(ValueError):
            compute_viscosity_from_rotor_decay(0.0)

    def test_invalid_temperature_raises(self):
        with self.assertRaises(ValueError):
            compute_viscosity_from_rotor_decay(1.0e-9, temperature_K=0.0)

    def test_invalid_volume_raises(self):
        with self.assertRaises(ValueError):
            compute_viscosity_from_rotor_decay(1.0e-9, v_rotor_m3=0.0)

    def test_returns_positive(self):
        eta = compute_viscosity_from_rotor_decay(1.0e-9)
        self.assertGreater(eta, 0.0)


# ─────────────────────────────────────────────────────────────────────────────
# Tests: compute_entropy_density_from_upe
# ─────────────────────────────────────────────────────────────────────────────

class TestComputeEntropyDensityFromUPE(unittest.TestCase):
    """Test entropy density derivation from UPE flux."""

    def test_basic_calculation(self):
        """s = ℏ·ω_UPE·Φ / (k_B·T·c²)."""
        phi = 1.0e3
        omega = 2.0 * math.pi * F_UPE_HZ
        expected = HBAR * omega * phi / (KB * T_CYTOPLASM_K * SPEED_OF_LIGHT ** 2)
        result = compute_entropy_density_from_upe(phi)
        self.assertAlmostEqual(result, expected, places=10)

    def test_scales_linearly_with_flux(self):
        """Doubling Φ_UPE should double s."""
        s1 = compute_entropy_density_from_upe(1.0e3)
        s2 = compute_entropy_density_from_upe(2.0e3)
        self.assertAlmostEqual(s2 / s1, 2.0, places=10)

    def test_scales_linearly_with_frequency(self):
        """Doubling f_UPE should double s."""
        s1 = compute_entropy_density_from_upe(1.0e3, f_upe_hz=1000.0)
        s2 = compute_entropy_density_from_upe(1.0e3, f_upe_hz=2000.0)
        self.assertAlmostEqual(s2 / s1, 2.0, places=10)

    def test_invalid_phi_raises(self):
        with self.assertRaises(ValueError):
            compute_entropy_density_from_upe(0.0)

    def test_negative_phi_raises(self):
        with self.assertRaises(ValueError):
            compute_entropy_density_from_upe(-100.0)

    def test_invalid_frequency_raises(self):
        with self.assertRaises(ValueError):
            compute_entropy_density_from_upe(1.0e3, f_upe_hz=0.0)

    def test_invalid_temperature_raises(self):
        with self.assertRaises(ValueError):
            compute_entropy_density_from_upe(1.0e3, temperature_K=0.0)

    def test_returns_positive(self):
        s = compute_entropy_density_from_upe(1.0e3)
        self.assertGreater(s, 0.0)


# ─────────────────────────────────────────────────────────────────────────────
# Tests: KSSHolographicFluid
# ─────────────────────────────────────────────────────────────────────────────

class TestKSSHolographicFluidInit(unittest.TestCase):
    """Test KSSHolographicFluid initialisation."""

    def test_default_init(self):
        fluid = KSSHolographicFluid()
        self.assertAlmostEqual(fluid.f0, F0)
        self.assertAlmostEqual(fluid.temperature_K, T_CYTOPLASM_K)
        self.assertAlmostEqual(fluid.f_upe_hz, F_UPE_HZ)
        self.assertAlmostEqual(fluid.kss_bound, KSS_BOUND)

    def test_custom_init(self):
        fluid = KSSHolographicFluid(f0=200.0, temperature_K=300.0, f_upe_hz=1500.0)
        self.assertAlmostEqual(fluid.f0, 200.0)
        self.assertAlmostEqual(fluid.temperature_K, 300.0)
        self.assertAlmostEqual(fluid.f_upe_hz, 1500.0)

    def test_invalid_f0_raises(self):
        with self.assertRaises(ValueError):
            KSSHolographicFluid(f0=0.0)

    def test_invalid_temperature_raises(self):
        with self.assertRaises(ValueError):
            KSSHolographicFluid(temperature_K=-1.0)

    def test_invalid_f_upe_raises(self):
        with self.assertRaises(ValueError):
            KSSHolographicFluid(f_upe_hz=0.0)


class TestKSSHolographicFluidValidate(unittest.TestCase):
    """Test the validate() method."""

    def setUp(self):
        self.fluid = KSSHolographicFluid()

    def test_returns_kss_result(self):
        result = self.fluid.validate(tau_rot_s=1.0e-9, phi_upe=1.0e3, psi=0.999999)
        self.assertIsInstance(result, KSSResult)

    def test_kss_result_fields(self):
        result = self.fluid.validate(tau_rot_s=1.0e-9, phi_upe=1.0e3, psi=0.5)
        self.assertGreater(result.eta, 0.0)
        self.assertGreater(result.s, 0.0)
        self.assertGreater(result.eta_over_s, 0.0)
        self.assertAlmostEqual(result.kss_bound, KSS_BOUND)
        self.assertGreater(result.ratio_to_bound, 0.0)
        self.assertEqual(result.psi, 0.5)

    def test_eta_over_s_consistency(self):
        result = self.fluid.validate(tau_rot_s=1.0e-9, phi_upe=1.0e3, psi=0.5)
        self.assertAlmostEqual(result.eta_over_s, result.eta / result.s, places=20)

    def test_ratio_to_bound_consistency(self):
        result = self.fluid.validate(tau_rot_s=1.0e-9, phi_upe=1.0e3, psi=0.5)
        self.assertAlmostEqual(
            result.ratio_to_bound, result.eta_over_s / result.kss_bound, places=10
        )

    def test_invalid_psi_raises(self):
        with self.assertRaises(ValueError):
            self.fluid.validate(tau_rot_s=1.0e-9, phi_upe=1.0e3, psi=1.5)

    def test_negative_psi_raises(self):
        with self.assertRaises(ValueError):
            self.fluid.validate(tau_rot_s=1.0e-9, phi_upe=1.0e3, psi=-0.1)

    def test_holographic_state_at_max_coherence(self):
        """At Ψ=0.999999 with small τ/large Φ, system can be holographic."""
        # With tau=1e-12 (very small viscosity) and large UPE flux
        result = self.fluid.validate(
            tau_rot_s=1.0e-12, phi_upe=1.0e10, psi=PSI_HOLOGRAPHIC
        )
        self.assertIn(result.state, [
            "FLUIDO_HOLOGRAFICO_PERFECTO",
            "BORDE_HOLOGRAFICO",
            "COHERENCIA_MAXIMA",
        ])

    def test_classical_fluid_at_low_coherence(self):
        result = self.fluid.validate(tau_rot_s=1.0e-6, phi_upe=1.0, psi=0.1)
        self.assertEqual(result.state, "FLUIDO_CLASICO")

    def test_to_dict_keys(self):
        result = self.fluid.validate(tau_rot_s=1.0e-9, phi_upe=1.0e3, psi=0.5)
        d = result.to_dict()
        for key in ('eta_Pa_s', 's_J_K_m3', 'eta_over_s', 'kss_bound',
                    'ratio_to_kss_bound', 'psi', 'is_holographic', 'state'):
            self.assertIn(key, d)


class TestKSSClassifyState(unittest.TestCase):
    """Test the state classification logic."""

    def setUp(self):
        self.fluid = KSSHolographicFluid()

    def test_fluido_holografico_perfecto(self):
        state = self.fluid._classify_state(psi=0.999999, ratio_to_bound=0.5)
        self.assertEqual(state, "FLUIDO_HOLOGRAFICO_PERFECTO")

    def test_borde_holografico(self):
        state = self.fluid._classify_state(psi=0.999999, ratio_to_bound=5.0)
        self.assertEqual(state, "BORDE_HOLOGRAFICO")

    def test_coherencia_maxima(self):
        state = self.fluid._classify_state(psi=0.9995, ratio_to_bound=100.0)
        self.assertEqual(state, "COHERENCIA_MAXIMA")

    def test_coherencia_biologica(self):
        state = self.fluid._classify_state(psi=0.9, ratio_to_bound=100.0)
        self.assertEqual(state, "COHERENCIA_BIOLOGICA")

    def test_fluido_clasico(self):
        state = self.fluid._classify_state(psi=0.1, ratio_to_bound=1000.0)
        self.assertEqual(state, "FLUIDO_CLASICO")


class TestKSSSweepCoherence(unittest.TestCase):
    """Test the sweep_coherence() method."""

    def setUp(self):
        self.fluid = KSSHolographicFluid()

    def test_returns_dict_with_correct_keys(self):
        result = self.fluid.sweep_coherence(tau_rot_s=1.0e-9, phi_upe=1.0e3)
        for key in ('psi', 'eta_over_s', 'ratio_to_bound', 'is_holographic'):
            self.assertIn(key, result)

    def test_array_lengths_match_n_points(self):
        n = 30
        result = self.fluid.sweep_coherence(tau_rot_s=1.0e-9, phi_upe=1.0e3, n_points=n)
        self.assertEqual(len(result['psi']), n)
        self.assertEqual(len(result['eta_over_s']), n)
        self.assertEqual(len(result['ratio_to_bound']), n)
        self.assertEqual(len(result['is_holographic']), n)

    def test_psi_range(self):
        result = self.fluid.sweep_coherence(tau_rot_s=1.0e-9, phi_upe=1.0e3, n_points=10)
        self.assertAlmostEqual(result['psi'][0], 0.0)
        self.assertAlmostEqual(result['psi'][-1], 1.0)

    def test_eta_over_s_positive(self):
        result = self.fluid.sweep_coherence(tau_rot_s=1.0e-9, phi_upe=1.0e3)
        self.assertTrue(np.all(result['eta_over_s'] > 0.0))

    def test_ratio_decreases_with_coherence(self):
        """Higher Ψ → higher s_eff → lower ratio_to_bound."""
        result = self.fluid.sweep_coherence(tau_rot_s=1.0e-9, phi_upe=1.0e3, n_points=20)
        ratios = result['ratio_to_bound']
        # The ratio should be monotonically non-increasing (s grows with psi)
        self.assertTrue(np.all(np.diff(ratios) <= 1e-10))


class TestKSSKaluzaKleinCorrespondence(unittest.TestCase):
    """Test the Kaluza-Klein cavity correspondence."""

    def setUp(self):
        self.fluid = KSSHolographicFluid()

    def test_kk_cavity_at_psi_holographic(self):
        is_kk, desc = self.fluid.kaluza_klein_correspondence(psi=PSI_HOLOGRAPHIC)
        self.assertTrue(is_kk)
        self.assertIn("Kaluza-Klein", desc)

    def test_no_kk_below_threshold(self):
        is_kk, desc = self.fluid.kaluza_klein_correspondence(psi=0.99)
        self.assertFalse(is_kk)

    def test_kk_at_exactly_threshold(self):
        is_kk, _ = self.fluid.kaluza_klein_correspondence(psi=0.999999)
        self.assertTrue(is_kk)

    def test_description_is_string(self):
        _, desc = self.fluid.kaluza_klein_correspondence(psi=0.5)
        self.assertIsInstance(desc, str)
        self.assertGreater(len(desc), 0)


# ─────────────────────────────────────────────────────────────────────────────
# Tests: Package-level import
# ─────────────────────────────────────────────────────────────────────────────

class TestPackageImport(unittest.TestCase):
    """Verify that KSS symbols are accessible from the top-level qcal package."""

    def test_import_from_package(self):
        from qcal import (
            KSSHolographicFluid,
            KSSResult,
            compute_kss_bound,
            compute_viscosity_from_rotor_decay,
            compute_entropy_density_from_upe,
            KSS_BOUND,
            F_UPE_HZ,
        )
        self.assertIsNotNone(KSSHolographicFluid)
        self.assertIsNotNone(compute_kss_bound)

    def test_kss_bound_from_package(self):
        from qcal import KSS_BOUND as bound
        self.assertAlmostEqual(bound, HBAR / (4.0 * math.pi * KB), places=25)


# ─────────────────────────────────────────────────────────────────────────────

if __name__ == '__main__':
    unittest.main(verbosity=2)
