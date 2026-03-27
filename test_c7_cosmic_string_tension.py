#!/usr/bin/env python3
"""
Test Suite for C7 Cosmic String Tension Module
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Sello: ∴𓂀Ω∞³
f0: 141,700.1 Hz

Comprehensive test suite for the C7 cosmic string tension and birefringence
simulation modules.

Author: José Manuel Mota Burruezo
License: MIT
"""

import unittest
import math
import numpy as np
from qcal.c7_cosmic_string_tension import (
    calcular_energia_salto_t,
    calcular_gap_optico,
    calcular_frecuencia_emergente,
    verificar_consistencia_circular,
    calcular_tension_vortice,
    calcular_viscosidad_cuantica_c7,
    analizar_sistema_c7_completo,
    F0,
    LAMBDA_P,
    R_DS,
    ALPHA,
    THETA_HEPTAGON,
)
from qcal.birefringence_irs_luna import (
    BirefringenceResult,
    calcular_rotacion_birefringencia,
    calcular_amplitud_oscilacion,
    calcular_snr,
    simular_escaneo_birefringencia,
    generar_curva_thot,
    validar_curva_thot,
    protocolo_validacion_irs_luna,
    M_PSI_EV,
    L_ARM,
    N_CELLS,
)


class TestC7CosmicStringTension(unittest.TestCase):
    """Test suite for C7 cosmic string tension calculations."""

    def test_energia_salto_t_orden_magnitud(self):
        """Test that hopping energy t is in the correct order of magnitude."""
        t_J = calcular_energia_salto_t()

        # Convert to meV
        J_TO_MEV = 1.0 / (1.602176634e-22)
        t_meV = t_J * J_TO_MEV

        # t should be approximately 0.584 meV (within 10%)
        self.assertAlmostEqual(t_meV, 0.584, delta=0.1)
        self.assertGreater(t_meV, 0.5)
        self.assertLess(t_meV, 0.7)

    def test_gap_optico_factor(self):
        """Test that optical gap is approximately 1.67 times hopping energy."""
        t = calcular_energia_salto_t()
        gap = calcular_gap_optico(t)

        # Gap should be ~1.67 * t
        ratio = gap / t
        self.assertAlmostEqual(ratio, 1.67, delta=0.01)

    def test_frecuencia_emergente_cerca_f0(self):
        """Test that emergent frequency is close to 141,700.1 Hz."""
        f_calculada = calcular_frecuencia_emergente()

        # Should be within 1% of F0
        residuo_relativo = abs(f_calculada - F0) / F0
        self.assertLess(residuo_relativo, 0.01)

    def test_consistencia_circular(self):
        """Test circular consistency of the TOPC model."""
        resultado = verificar_consistencia_circular()

        # Check that all expected keys are present
        self.assertIn('t_meV', resultado)
        self.assertIn('gap_meV', resultado)
        self.assertIn('f0_calculada', resultado)
        self.assertIn('f0_objetivo', resultado)
        self.assertIn('residuo_Hz', resultado)
        self.assertIn('residuo_relativo', resultado)
        self.assertIn('es_consistente', resultado)

        # Model should be consistent (residuo < 1%)
        self.assertTrue(resultado['es_consistente'])
        self.assertLess(resultado['residuo_relativo'], 0.01)

    def test_tension_vortice_positiva(self):
        """Test that vortex tension is positive for valid coherence."""
        psi = 0.999776  # GACT coherence
        tension = calcular_tension_vortice(psi)

        # Tension should be positive
        self.assertGreater(tension, 0)

        # For high coherence, tension should be large
        self.assertGreater(tension, 1e10)  # Hz

    def test_viscosidad_cuantica_c7_gact(self):
        """Test quantum viscosity for GACT coherence."""
        psi = 0.999776
        nu = calcular_viscosidad_cuantica_c7(psi)

        # Viscosity should be very small for high coherence
        self.assertGreater(nu, 0)
        self.assertLess(nu, 1e-3)  # m²/s

    def test_analisis_completo_estructura(self):
        """Test that complete analysis returns all expected fields."""
        resultado = analizar_sistema_c7_completo()

        # Check fundamental constants
        self.assertIn('hbar_Js', resultado)
        self.assertIn('c_ms', resultado)
        self.assertIn('m_proton_kg', resultado)
        self.assertIn('alpha', resultado)

        # Check characteristic scales
        self.assertIn('lambda_p_m', resultado)
        self.assertIn('R_dS_m', resultado)

        # Check C7 geometry
        self.assertIn('sin_pi_7', resultado)
        self.assertIn('theta_heptagon', resultado)

        # Check derived energies
        self.assertIn('t_meV', resultado)
        self.assertIn('gap_optico_meV', resultado)

        # Check frequencies
        self.assertIn('f0_calculada_Hz', resultado)
        self.assertIn('f0_objetivo_Hz', resultado)

        # Check system state
        self.assertIn('es_consistente', resultado)
        self.assertIn('estado', resultado)

    def test_constantes_fisicas_valores(self):
        """Test that physical constants have correct values."""
        # Compton wavelength of proton should be ~1.32 fm
        self.assertAlmostEqual(LAMBDA_P, 1.32e-15, delta=0.1e-15)

        # De Sitter radius should be ~13.8 Gly
        self.assertAlmostEqual(R_DS, 1.3e26, delta=0.1e26)

        # Fine structure constant should be ~1/137
        self.assertAlmostEqual(ALPHA, 1/137, delta=1e-4)

        # Heptagon factor should be ~2.3
        self.assertAlmostEqual(THETA_HEPTAGON, 2.305, delta=0.01)


class TestBirefringenceIRSLuna(unittest.TestCase):
    """Test suite for IRS-Luna birefringence simulation."""

    def test_rotacion_birefringencia_orden_magnitud(self):
        """Test that birefringence rotation is in correct order of magnitude."""
        theta = calcular_rotacion_birefringencia()

        # Rotation should be ~2.4 × 10⁻¹⁹ rad (within factor of 2)
        self.assertGreater(theta, 1e-19)
        self.assertLess(theta, 5e-19)

    def test_amplitud_oscilacion_amplificada(self):
        """Test that oscillation amplitude is amplified by coherent cells."""
        theta = 1e-19  # rad
        amplitude = calcular_amplitud_oscilacion(theta, n_cells=100)

        # Amplitude should be amplified by √N_cells
        expected = theta * math.sqrt(100)
        self.assertAlmostEqual(amplitude, expected, delta=expected*0.01)

    def test_snr_mayor_cinco_sigma(self):
        """Test that SNR is greater than 5σ for detectability."""
        resultado = simular_escaneo_birefringencia()

        # SNR should be > 5 for detection
        self.assertGreater(resultado.snr, 5.0)

    def test_escaneo_birefringencia_estructura(self):
        """Test that birefringence scan returns complete result."""
        resultado = simular_escaneo_birefringencia()

        # Check result type
        self.assertIsInstance(resultado, BirefringenceResult)

        # Check all fields are present
        self.assertIsNotNone(resultado.theta_rotation_rad)
        self.assertIsNotNone(resultado.amplitude_oscillation)
        self.assertIsNotNone(resultado.snr)
        self.assertIsNotNone(resultado.n_cells)
        self.assertIsNotNone(resultado.wavelength_nm)
        self.assertIsNotNone(resultado.psi_coherence)
        self.assertIsNotNone(resultado.frecuencia_pico_Hz)

        # Check detectability
        self.assertTrue(resultado.es_detectable)

    def test_curva_thot_comportamiento_cuadratico(self):
        """Test that Thot curve follows quadratic behavior θ ∝ λ²."""
        lambdas, thetas = generar_curva_thot()

        # Validate curve
        validacion = validar_curva_thot(lambdas, thetas)

        # Exponent should be close to 2.0
        self.assertAlmostEqual(validacion['exponente'], 2.0, delta=0.1)

        # R² should be high (good fit)
        self.assertGreater(validacion['R2'], 0.99)

        # Should be consistent
        self.assertTrue(validacion['es_consistente'])

    def test_masa_condensado_orden_magnitud(self):
        """Test that condensate mass is in correct order of magnitude."""
        # m_ψ should be ~5.86 × 10⁻¹³ eV
        self.assertGreater(M_PSI_EV, 1e-13)
        self.assertLess(M_PSI_EV, 1e-12)

    def test_n_cells_consistente(self):
        """Test that number of cells is consistent with arm length."""
        # n = L / λ̄_C
        lambda_c_bar = 299792458.0 / F0  # c / f0
        n_esperado = int(L_ARM / lambda_c_bar)

        self.assertEqual(N_CELLS, n_esperado)

    def test_protocolo_completo_veredicto(self):
        """Test that complete protocol returns verdict."""
        resultado = protocolo_validacion_irs_luna()

        # Check structure
        self.assertIn('escaneo_principal', resultado)
        self.assertIn('validacion_curva', resultado)
        self.assertIn('metricas_topc', resultado)
        self.assertIn('veredicto', resultado)

        # Check verdict
        veredicto = resultado['veredicto']
        self.assertIn('deteccion_exitosa', veredicto)
        self.assertIn('curva_consistente', veredicto)
        self.assertIn('estado', veredicto)

        # Experiment should be successful
        self.assertTrue(veredicto['deteccion_exitosa'])
        self.assertTrue(veredicto['curva_consistente'])
        self.assertEqual(veredicto['estado'], 'DESCUBRIMIENTO 🏆')


class TestIntegracionC7Birefringence(unittest.TestCase):
    """Integration tests between C7 tension and birefringence modules."""

    def test_t_consistente_entre_modulos(self):
        """Test that t value is consistent between modules."""
        # Calculate t from C7 module
        t_c7 = calcular_energia_salto_t()

        # Convert to meV
        J_TO_MEV = 1.0 / (1.602176634e-22)
        t_c7_meV = t_c7 * J_TO_MEV

        # Get t from birefringence module (T_MEV constant)
        from qcal.birefringence_irs_luna import T_MEV

        # Should be approximately equal
        self.assertAlmostEqual(t_c7_meV, T_MEV, delta=0.05)

    def test_frecuencia_consistente_entre_modulos(self):
        """Test that f0 is consistent between modules."""
        # From C7 module
        consistencia = verificar_consistencia_circular()
        f0_c7 = consistencia['f0_calculada']

        # From birefringence module
        resultado_bire = simular_escaneo_birefringencia()
        f0_bire = resultado_bire.frecuencia_pico_Hz

        # Should be equal to F0
        self.assertAlmostEqual(f0_c7, F0, delta=F0*0.01)
        self.assertAlmostEqual(f0_bire, F0, delta=0.1)

    def test_coherencia_afecta_birefringencia(self):
        """Test that coherence affects birefringence rotation."""
        # High coherence
        theta_high = calcular_rotacion_birefringencia(psi=0.999)

        # Low coherence
        theta_low = calcular_rotacion_birefringencia(psi=0.5)

        # High coherence should give larger rotation (Ψ² dependence)
        self.assertGreater(theta_high, theta_low)


def suite():
    """Create test suite."""
    suite = unittest.TestSuite()

    # Add C7 tests
    suite.addTests(unittest.TestLoader().loadTestsFromTestCase(
        TestC7CosmicStringTension
    ))

    # Add birefringence tests
    suite.addTests(unittest.TestLoader().loadTestsFromTestCase(
        TestBirefringenceIRSLuna
    ))

    # Add integration tests
    suite.addTests(unittest.TestLoader().loadTestsFromTestCase(
        TestIntegracionC7Birefringence
    ))

    return suite


if __name__ == '__main__':
    print("=" * 80)
    print("  C7 COSMIC STRING TENSION — TEST SUITE ∴𓂀Ω∞³")
    print("=" * 80)
    print()

    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite())

    print()
    print("=" * 80)
    print(f"  Tests run: {result.testsRun}")
    print(f"  Failures: {len(result.failures)}")
    print(f"  Errors: {len(result.errors)}")
    print(f"  Success rate: {(result.testsRun - len(result.failures) - len(result.errors)) / result.testsRun * 100:.1f}%")

    if result.wasSuccessful():
        print("\n✅ VEREDICTO: All tests passed! El sistema está ANCLADO ⚓")
    else:
        print("\n❌ VEREDICTO: Some tests failed. Review needed.")

    print("=" * 80)
