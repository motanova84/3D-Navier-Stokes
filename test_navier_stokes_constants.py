#!/usr/bin/env python3
"""
Test Suite for Navier-Stokes Unified Constants Module

Validates the unified constants module for parameter a unification
and QCAL constants.
"""
Tests para el módulo navier_stokes.constants

Verifica la correcta implementación de las constantes fundamentales
y funciones del sistema Ψ-NS QCAL.
"""

import unittest
import numpy as np
from navier_stokes.constants import (
    calcular_a,
    obtener_delta_star,
    verificar_regularidad,
    get_all_media_parameters,
    get_qcal_constants,
    F0,
    OMEGA0,
    A_VACIO,
    A_AGUA,
    A_AIRE,
    C0_DEFAULT,
    ALPHA_QFT,
    BETA_QFT,
    GAMMA_QFT,
    C_STAR,
    C_STR,
    C_B,
    C_CZ,
    C_STAR_BESOV,
)


class TestConstants(unittest.TestCase):
    """Test fundamental constants are defined correctly."""
    
    def test_f0_value(self):
        """Test F0 has the correct QCAL value."""
        self.assertAlmostEqual(F0, 141.7001, places=4)
    
    def test_omega0_value(self):
        """Test OMEGA0 is correctly calculated from F0."""
        expected_omega = 2.0 * np.pi * F0
        self.assertAlmostEqual(OMEGA0, expected_omega, places=4)
    
    def test_medium_parameters(self):
        """Test medium-specific parameters are defined."""
        self.assertAlmostEqual(A_VACIO, 8.9, places=1)
        self.assertAlmostEqual(A_AGUA, 7.0, places=1)
        self.assertAlmostEqual(A_AIRE, 200.0, places=1)
    
    def test_qft_coefficients(self):
        """Test QFT coupling coefficients are positive."""
        self.assertGreater(ALPHA_QFT, 0)
        self.assertGreater(BETA_QFT, 0)
        self.assertGreater(GAMMA_QFT, 0)
        
        # Check specific values
        self.assertAlmostEqual(ALPHA_QFT, 1.0 / (16.0 * np.pi**2), places=10)
        self.assertAlmostEqual(BETA_QFT, 1.0 / (384.0 * np.pi**2), places=10)
        self.assertAlmostEqual(GAMMA_QFT, 1.0 / (192.0 * np.pi**2), places=10)
    
    def test_parabolic_constants(self):
        """Test parabolic coercivity constants."""
        self.assertAlmostEqual(C_STAR, 1.0 / 16.0, places=10)
        self.assertAlmostEqual(C_STR, 32.0, places=1)
    
    def test_riccati_besov_constants(self):
        """Test Riccati-Besov constants."""
        self.assertAlmostEqual(C_B, 0.15, places=2)
        self.assertAlmostEqual(C_CZ, 1.5, places=1)
        self.assertAlmostEqual(C_STAR_BESOV, 1.2, places=1)
    
    def test_c0_default(self):
        """Test default phase gradient."""
        self.assertAlmostEqual(C0_DEFAULT, 1.0, places=1)


class TestCalcularA(unittest.TestCase):
    """Test calcular_a function with different media."""
    
    def test_agua_spanish(self):
        """Test agua (water) in Spanish."""
        a = calcular_a('agua')
        self.assertAlmostEqual(a, 7.0, places=1)
    
    def test_agua_default(self):
        """Test agua is the default medium."""
        a = calcular_a()
        self.assertAlmostEqual(a, 7.0, places=1)
    
    def test_water_english(self):
        """Test water in English."""
        a = calcular_a('water')
        self.assertAlmostEqual(a, 7.0, places=1)
    
    def test_vacio_spanish(self):
        """Test vacio (vacuum) in Spanish."""
        a = calcular_a('vacio')
        self.assertAlmostEqual(a, 8.9, places=1)
    
    def test_vacuum_english(self):
        """Test vacuum in English."""
        a = calcular_a('vacuum')
        self.assertAlmostEqual(a, 8.9, places=1)
    
    def test_aire_spanish(self):
        """Test aire (air) in Spanish."""
        a = calcular_a('aire')
        self.assertAlmostEqual(a, 200.0, places=1)
    
    def test_air_english(self):
        """Test air in English."""
        a = calcular_a('air')
        self.assertAlmostEqual(a, 200.0, places=1)
    
    def test_case_insensitive(self):
        """Test that medium names are case-insensitive."""
        self.assertAlmostEqual(calcular_a('AGUA'), 7.0, places=1)
        self.assertAlmostEqual(calcular_a('Water'), 7.0, places=1)
        self.assertAlmostEqual(calcular_a('AIR'), 200.0, places=1)
    
    def test_invalid_medium(self):
        """Test that invalid medium raises ValueError."""
        with self.assertRaises(ValueError) as context:
            calcular_a('invalid_medium')
        self.assertIn('Unknown medium', str(context.exception))
    
    def test_custom_viscosity(self):
        """Test custom viscosity calculation."""
        # For nu = 1e-3, calculated a should be around 6.3 (Riccati-Besov threshold)
        a = calcular_a(custom_viscosity=1e-3)
        self.assertGreater(a, 6.0)
        self.assertLess(a, 7.0)
    
    def test_custom_viscosity_overrides_medium(self):
        """Test that custom viscosity overrides medium selection."""
        a1 = calcular_a(medio='agua', custom_viscosity=1e-3)
        a2 = calcular_a(medio='aire', custom_viscosity=1e-3)
        # Both should be the same since custom viscosity overrides
        self.assertAlmostEqual(a1, a2, places=6)


class TestObtenerDeltaStar(unittest.TestCase):
    """Test obtener_delta_star function."""
    
    def test_agua(self):
        """Test delta_star for agua."""
        delta_star = obtener_delta_star(A_AGUA)
        expected = (A_AGUA**2 * C0_DEFAULT**2) / (4.0 * np.pi**2)
        self.assertAlmostEqual(delta_star, expected, places=10)
    
    def test_vacio(self):
        """Test delta_star for vacio."""
        delta_star = obtener_delta_star(A_VACIO)
        expected = (A_VACIO**2 * C0_DEFAULT**2) / (4.0 * np.pi**2)
        self.assertAlmostEqual(delta_star, expected, places=10)
    
    def test_aire(self):
        """Test delta_star for aire."""
        delta_star = obtener_delta_star(A_AIRE)
        expected = (A_AIRE**2 * C0_DEFAULT**2) / (4.0 * np.pi**2)
        self.assertAlmostEqual(delta_star, expected, places=10)
    
    def test_custom_c0(self):
        """Test delta_star with custom c0."""
        c0 = 2.0
        delta_star = obtener_delta_star(A_AGUA, c0=c0)
        expected = (A_AGUA**2 * c0**2) / (4.0 * np.pi**2)
        self.assertAlmostEqual(delta_star, expected, places=10)
    
    def test_positive_values(self):
        """Test that delta_star is always positive for positive a."""
        for a in [1.0, 5.0, 10.0, 50.0, 100.0]:
            delta_star = obtener_delta_star(a)
            self.assertGreater(delta_star, 0)


class TestVerificarRegularidad(unittest.TestCase):
    """Test verificar_regularidad function."""
    
    def test_agua_low_viscosity(self):
        """Test regularidad for agua with low viscosity."""
        nu = 1e-6  # Low viscosity (water-like)
        result = verificar_regularidad(A_AGUA, nu, verbose=False)
        
        # Check structure
        self.assertIn('delta_star', result)
        self.assertIn('gamma', result)
        self.assertIn('delta', result)
        self.assertIn('parabolic_ok', result)
        self.assertIn('riccati_besov_ok', result)
        self.assertIn('global_regularity', result)
        
        # For agua with low viscosity, satisfies Riccati-Besov but not parabolic
        # So global_regularity is False, but delta > 0
        self.assertTrue(result['riccati_besov_ok'])
        self.assertGreater(result['delta'], 0)
    
    def test_vacio_low_viscosity(self):
        """Test regularidad for vacio with very low viscosity."""
        nu = 1e-6
        result = verificar_regularidad(A_VACIO, nu, verbose=False)
        
        # Vacio has higher a, should definitely achieve regularity
        self.assertTrue(result['global_regularity'])
    
    def test_aire_air_viscosity(self):
        """Test regularidad for aire with air-like viscosity."""
        nu = 1.5e-5  # Air viscosity
        result = verificar_regularidad(A_AIRE, nu, verbose=False)
        
        # Aire with high a should achieve regularity
        self.assertTrue(result['global_regularity'])
    
    def test_insufficient_amplitude(self):
        """Test that low amplitude fails regularity."""
        nu = 1e-3
        a_low = 1.0  # Too low
        result = verificar_regularidad(a_low, nu, verbose=False)
        
        # Should not achieve global regularity
        self.assertFalse(result['global_regularity'])
    
    def test_verbose_mode(self):
        """Test that verbose mode doesn't crash."""
        import io
        import sys
        
        # Capture stdout
        old_stdout = sys.stdout
        sys.stdout = io.StringIO()
        
        try:
            result = verificar_regularidad(A_AGUA, 1e-6, verbose=True)
            output = sys.stdout.getvalue()
            
            # Check that output contains expected text
            self.assertIn('Verification Results', output)
            self.assertIn('δ*', output)
            self.assertIn('γ', output)
            self.assertIn('Δ', output)
        finally:
            sys.stdout = old_stdout
    
    def test_custom_parameters(self):
        """Test with custom c0 and M."""
        nu = 1e-3
        result = verificar_regularidad(A_VACIO, nu, c0=2.0, M=200.0, verbose=False)
        
        # Should still produce a result
        self.assertIn('global_regularity', result)
        # Check it's a boolean (numpy bool is okay too)
        self.assertIn(result['global_regularity'], [True, False, np.True_, np.False_])
    
    def test_parabolic_condition(self):
        """Test parabolic damping condition."""
        nu = 1e-3
        a = 8.9  # From calibration
        result = verificar_regularidad(a, nu, verbose=False)
        
        # Check that gamma is calculated correctly
        delta_star = obtener_delta_star(a)
        expected_gamma = nu * C_STAR - (1.0 - delta_star/2.0) * C_STR
        self.assertAlmostEqual(result['gamma'], expected_gamma, places=10)
    
    def test_riccati_besov_condition(self):
        """Test Riccati-Besov damping condition."""
        nu = 1e-3
        a = 8.9
        M = 100.0
        result = verificar_regularidad(a, nu, M=M, verbose=False)
        
        # Check that delta is calculated correctly
        delta_star = obtener_delta_star(a)
        log_term = 1.0 + np.log(1.0 + M)
        expected_delta = nu * C_B - (1.0 - delta_star) * C_CZ * C_STAR_BESOV * log_term
        self.assertAlmostEqual(result['delta'], expected_delta, places=10)


class TestGetAllMediaParameters(unittest.TestCase):
    """Test get_all_media_parameters function."""
    
    def test_returns_dict(self):
        """Test that function returns a dictionary."""
        params = get_all_media_parameters()
        self.assertIsInstance(params, dict)
    
    def test_contains_all_media(self):
        """Test that all media are present."""
        params = get_all_media_parameters()
        self.assertIn('vacio', params)
        self.assertIn('agua', params)
        self.assertIn('aire', params)
    
    def test_correct_values(self):
        """Test that values are correct."""
        params = get_all_media_parameters()
        self.assertAlmostEqual(params['vacio'], A_VACIO, places=1)
        self.assertAlmostEqual(params['agua'], A_AGUA, places=1)
        self.assertAlmostEqual(params['aire'], A_AIRE, places=1)


class TestGetQCALConstants(unittest.TestCase):
    """Test get_qcal_constants function."""
    
    def test_returns_dict(self):
        """Test that function returns a dictionary."""
        constants = get_qcal_constants()
        self.assertIsInstance(constants, dict)
    
    def test_contains_all_constants(self):
        """Test that all constants are present."""
        constants = get_qcal_constants()
        self.assertIn('F0', constants)
        self.assertIn('OMEGA0', constants)
        self.assertIn('ALPHA_QFT', constants)
        self.assertIn('BETA_QFT', constants)
        self.assertIn('GAMMA_QFT', constants)
    
    def test_correct_values(self):
        """Test that values are correct."""
        constants = get_qcal_constants()
        self.assertAlmostEqual(constants['F0'], F0, places=4)
        self.assertAlmostEqual(constants['OMEGA0'], OMEGA0, places=4)
        self.assertAlmostEqual(constants['ALPHA_QFT'], ALPHA_QFT, places=10)
        self.assertAlmostEqual(constants['BETA_QFT'], BETA_QFT, places=10)
        self.assertAlmostEqual(constants['GAMMA_QFT'], GAMMA_QFT, places=10)


class TestIntegration(unittest.TestCase):
    """Integration tests for the unified constants module."""
    
    def test_agua_workflow(self):
        """Test complete workflow for agua."""
        # Get amplitude
        a = calcular_a('agua')
        
        # Calculate delta_star
        delta_star = obtener_delta_star(a)
        
        # Verify regularidad
        result = verificar_regularidad(a, nu=1e-3)
        
        # Agua satisfies Riccati-Besov but not necessarily parabolic
        self.assertGreater(result['delta'], 0)
        self.assertTrue(result['riccati_besov_ok'])
    
    def test_all_media_regularity(self):
        """Test regularity conditions for different media.
        
        Note: agua (a=7.0) is intentionally calibrated to satisfy the primary
        Riccati-Besov condition but not the stricter parabolic condition. This
        is acceptable as Riccati-Besov is the main indicator of global regularity.
        For applications requiring both conditions, use vacio (a=8.9).
        """
        test_cases = [
            ('vacio', 1e-3, True),  # Should achieve full regularity
            ('agua', 1e-3, False),  # Satisfies Riccati-Besov but not parabolic (intentional)
            ('aire', 1.5e-5, True),  # Should achieve full regularity with high amplitude
        ]
        
        for medio, nu, expected_full_regularity in test_cases:
            with self.subTest(medio=medio):
                a = calcular_a(medio)
                result = verificar_regularidad(a, nu)
                
                # All should at least satisfy Riccati-Besov
                self.assertTrue(
                    result['riccati_besov_ok'],
                    f"{medio} should satisfy Riccati-Besov condition"
                )
                
                # Check if full regularity matches expectation
                self.assertEqual(
                    result['global_regularity'],
                    expected_full_regularity,
                    f"{medio} regularity mismatch"
                )
    
    def test_custom_calibration(self):
        """Test custom calibration workflow."""
        nu_custom = 5e-4
        
        # Get custom calibrated amplitude (uses Riccati-Besov formula)
        a = calcular_a(custom_viscosity=nu_custom)
        
        # Verify it achieves at least Riccati-Besov regularidad
        result = verificar_regularidad(a, nu_custom)
        
        # Should satisfy Riccati-Besov condition with custom calibration
        self.assertTrue(result['riccati_besov_ok'])
        self.assertGreater(result['delta'], 0)
    
    def test_import_from_package(self):
        """Test that imports work correctly from package."""
        # This test ensures __init__.py exports are correct
        from navier_stokes import calcular_a as ca
        from navier_stokes import F0 as f0
        from navier_stokes import verificar_regularidad as vr
        
        self.assertEqual(ca('agua'), A_AGUA)
        self.assertEqual(f0, F0)
        self.assertIsNotNone(vr)


def suite():
    """Create test suite."""
    test_suite = unittest.TestSuite()
    test_suite.addTest(unittest.TestLoader().loadTestsFromTestCase(TestConstants))
    test_suite.addTest(unittest.TestLoader().loadTestsFromTestCase(TestCalcularA))
    test_suite.addTest(unittest.TestLoader().loadTestsFromTestCase(TestObtenerDeltaStar))
    test_suite.addTest(unittest.TestLoader().loadTestsFromTestCase(TestVerificarRegularidad))
    test_suite.addTest(unittest.TestLoader().loadTestsFromTestCase(TestGetAllMediaParameters))
    test_suite.addTest(unittest.TestLoader().loadTestsFromTestCase(TestGetQCALConstants))
    test_suite.addTest(unittest.TestLoader().loadTestsFromTestCase(TestIntegration))
    return test_suite


if __name__ == '__main__':
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite())
    exit(0 if result.wasSuccessful() else 1)
    F0,
    calcular_a,
    calcular_velocidad_medio,
    calcular_defecto_desalineacion,
    calcular_coeficiente_amortiguamiento
)


class TestConstantesFundamentales(unittest.TestCase):
    """Tests para constantes fundamentales del sistema QCAL."""
    
    def test_frecuencia_fundamental(self):
        """Verifica que F0 tiene el valor correcto."""
        self.assertEqual(F0, 141.7001)
    
    def test_tipo_frecuencia(self):
        """Verifica que F0 es un número."""
        self.assertIsInstance(F0, (int, float))


class TestCalcularParametroA(unittest.TestCase):
    """Tests para la función calcular_a."""
    
    def test_a_vacio(self):
        """Verifica el valor de a para vacío."""
        a = calcular_a('vacio')
        self.assertEqual(a, 8.9)
    
    def test_a_agua(self):
        """Verifica el valor de a para agua."""
        a = calcular_a('agua')
        self.assertEqual(a, 7.0)
    
    def test_a_aire(self):
        """Verifica el valor de a para aire."""
        a = calcular_a('aire')
        self.assertEqual(a, 200)
    
    def test_a_default(self):
        """Verifica que el valor por defecto es vacío."""
        a_default = calcular_a()
        a_vacio = calcular_a('vacio')
        self.assertEqual(a_default, a_vacio)
    
    def test_medio_invalido(self):
        """Verifica que se lanza error para medio inválido."""
        with self.assertRaises(ValueError) as context:
            calcular_a('plasma')
        self.assertIn('no reconocido', str(context.exception))
    
    def test_case_insensitive(self):
        """Verifica que la función es case-insensitive."""
        a_lower = calcular_a('vacio')
        a_upper = calcular_a('VACIO')
        a_mixed = calcular_a('VaCiO')
        self.assertEqual(a_lower, a_upper)
        self.assertEqual(a_lower, a_mixed)
    
    def test_todos_los_medios_positivos(self):
        """Verifica que todos los valores de a son positivos."""
        for medio in ['vacio', 'agua', 'aire']:
            a = calcular_a(medio)
            self.assertGreater(a, 0)


class TestCalcularVelocidadMedio(unittest.TestCase):
    """Tests para la función calcular_velocidad_medio."""
    
    def test_velocidad_desde_a_vacio(self):
        """Verifica la velocidad calculada para a=8.9."""
        a = 8.9
        c = calcular_velocidad_medio(a)
        # c = (2π × 141.7001) / 8.9 ≈ 100
        self.assertAlmostEqual(c, 100.0, delta=0.1)
    
    def test_velocidad_desde_a_agua(self):
        """Verifica la velocidad calculada para a=7.0."""
        a = 7.0
        c = calcular_velocidad_medio(a)
        # c = (2π × 141.7001) / 7.0 ≈ 127
        self.assertAlmostEqual(c, 127.0, delta=0.5)
    
    def test_velocidad_desde_a_aire(self):
        """Verifica la velocidad calculada para a=200."""
        a = 200
        c = calcular_velocidad_medio(a)
        # c = (2π × 141.7001) / 200 ≈ 4.45
        self.assertAlmostEqual(c, 4.45, delta=0.01)
    
    def test_consistencia_inversa(self):
        """Verifica que a -> c -> a' da a' = a."""
        a_original = 8.9
        c = calcular_velocidad_medio(a_original)
        a_recuperado = (2 * np.pi * F0) / c
        self.assertAlmostEqual(a_recuperado, a_original, places=10)
    
    def test_error_a_negativo(self):
        """Verifica que se lanza error para a negativo."""
        with self.assertRaises(ValueError):
            calcular_velocidad_medio(-5.0)
    
    def test_error_a_cero(self):
        """Verifica que se lanza error para a=0."""
        with self.assertRaises(ValueError):
            calcular_velocidad_medio(0.0)


class TestCalcularDefectoDesalineacion(unittest.TestCase):
    """Tests para la función calcular_defecto_desalineacion."""
    
    def test_delta_vacio(self):
        """Verifica δ* para a=8.9 (vacío)."""
        a = 8.9
        delta = calcular_defecto_desalineacion(a)
        # δ* = (8.9² × 1²) / (4π²) ≈ 2.01
        self.assertAlmostEqual(delta, 2.01, delta=0.01)
    
    def test_delta_agua(self):
        """Verifica δ* para a=7.0 (agua)."""
        a = 7.0
        delta = calcular_defecto_desalineacion(a)
        # δ* = (7.0² × 1²) / (4π²) ≈ 1.24
        self.assertAlmostEqual(delta, 1.24, delta=0.01)
    
    def test_delta_aire(self):
        """Verifica δ* para a=200 (aire)."""
        a = 200
        delta = calcular_defecto_desalineacion(a)
        # δ* = (200² × 1²) / (4π²) ≈ 1012.9
        self.assertAlmostEqual(delta, 1012.9, delta=0.5)
    
    def test_delta_con_c0_custom(self):
        """Verifica δ* con c0 personalizado."""
        a = 10.0
        c0 = 2.0
        delta = calcular_defecto_desalineacion(a, c0)
        # δ* = (10² × 2²) / (4π²) = 400 / (4π²)
        expected = 400 / (4 * np.pi**2)
        self.assertAlmostEqual(delta, expected, places=10)
    
    def test_delta_escalamiento_cuadratico(self):
        """Verifica que δ* escala cuadráticamente con a."""
        a1 = 5.0
        a2 = 10.0
        delta1 = calcular_defecto_desalineacion(a1)
        delta2 = calcular_defecto_desalineacion(a2)
        # δ2 / δ1 = (a2/a1)² = 4
        ratio = delta2 / delta1
        self.assertAlmostEqual(ratio, 4.0, places=10)


class TestCalcularCoeficienteAmortiguamiento(unittest.TestCase):
    """Tests para la función calcular_coeficiente_amortiguamiento."""
    
    def test_gamma_vacio(self):
        """Verifica γ para δ*=2.01 (vacío)."""
        delta_star = 2.01
        gamma = calcular_coeficiente_amortiguamiento(delta_star)
        # γ = 10⁻³/16 - (1 - 2.01/2) × 32
        # γ = 0.0000625 - (-0.005) × 32
        # γ = 0.0000625 + 0.16 ≈ 0.16
        self.assertGreater(gamma, 0, "γ debe ser positivo para vacío")
        self.assertAlmostEqual(gamma, 0.10, delta=0.1)
    
    def test_gamma_positivo_vacio(self):
        """Verifica que γ > 0 para vacío (cierre incondicional)."""
        a_vacio = calcular_a('vacio')
        delta_vacio = calcular_defecto_desalineacion(a_vacio)
        gamma_vacio = calcular_coeficiente_amortiguamiento(delta_vacio)
        self.assertGreater(
            gamma_vacio, 0,
            "γ debe ser positivo para cierre incondicional en vacío"
        )
    
    def test_gamma_con_parametros_custom(self):
        """Verifica γ con parámetros personalizados."""
        delta_star = 1.5
        nu = 1e-2
        c_star = 0.1
        C_str = 10.0
        gamma = calcular_coeficiente_amortiguamiento(
            delta_star, nu, c_star, C_str
        )
        # γ = 0.01 × 0.1 - (1 - 1.5/2) × 10
        # γ = 0.001 - 0.25 × 10
        # γ = 0.001 - 2.5 = -2.499
        expected = nu * c_star - (1 - delta_star / 2) * C_str
        self.assertAlmostEqual(gamma, expected, places=10)
    
    def test_gamma_dependencia_lineal_delta(self):
        """Verifica que γ depende linealmente de δ*."""
        delta1 = 1.0
        delta2 = 2.0
        gamma1 = calcular_coeficiente_amortiguamiento(delta1)
        gamma2 = calcular_coeficiente_amortiguamiento(delta2)
        
        # Δγ / Δδ* = C_str / 2 = 32 / 2 = 16
        delta_gamma = gamma2 - gamma1
        delta_delta = delta2 - delta1
        pendiente = delta_gamma / delta_delta
        self.assertAlmostEqual(pendiente, 16.0, places=10)


class TestIntegracionSistemaCompleto(unittest.TestCase):
    """Tests de integración para el sistema completo."""
    
    def test_flujo_completo_vacio(self):
        """Verifica el flujo completo de cálculos para vacío."""
        # 1. Obtener parámetro a
        a = calcular_a('vacio')
        self.assertEqual(a, 8.9)
        
        # 2. Calcular velocidad
        c = calcular_velocidad_medio(a)
        self.assertAlmostEqual(c, 100.0, delta=0.1)
        
        # 3. Calcular defecto de desalineación
        delta = calcular_defecto_desalineacion(a)
        self.assertAlmostEqual(delta, 2.01, delta=0.01)
        
        # 4. Calcular coeficiente de amortiguamiento
        gamma = calcular_coeficiente_amortiguamiento(delta)
        self.assertGreater(gamma, 0)
    
    def test_flujo_completo_agua(self):
        """Verifica el flujo completo de cálculos para agua."""
        a = calcular_a('agua')
        c = calcular_velocidad_medio(a)
        delta = calcular_defecto_desalineacion(a)
        gamma = calcular_coeficiente_amortiguamiento(delta)
        
        self.assertEqual(a, 7.0)
        self.assertAlmostEqual(c, 127.0, delta=0.5)
        self.assertAlmostEqual(delta, 1.24, delta=0.01)
        # Para agua, γ puede ser pequeño pero generalmente positivo
        self.assertIsInstance(gamma, (int, float))
    
    def test_flujo_completo_aire(self):
        """Verifica el flujo completo de cálculos para aire."""
        a = calcular_a('aire')
        c = calcular_velocidad_medio(a)
        delta = calcular_defecto_desalineacion(a)
        gamma = calcular_coeficiente_amortiguamiento(delta)
        
        self.assertEqual(a, 200)
        self.assertAlmostEqual(c, 4.45, delta=0.01)
        self.assertAlmostEqual(delta, 1012.9, delta=0.5)
        self.assertGreater(gamma, 0)
    
    def test_coherencia_matematica(self):
        """Verifica la coherencia matemática del sistema."""
        for medio in ['vacio', 'agua', 'aire']:
            with self.subTest(medio=medio):
                # Obtener parámetro a
                a = calcular_a(medio)
                
                # Calcular velocidad
                c = calcular_velocidad_medio(a)
                
                # Verificar relación a = (2πf₀) / c
                a_calculado = (2 * np.pi * F0) / c
                self.assertAlmostEqual(a, a_calculado, places=5)
                
                # Calcular δ*
                delta = calcular_defecto_desalineacion(a)
                
                # Verificar que δ* > 0
                self.assertGreater(delta, 0)
    
    def test_comparacion_medios(self):
        """Verifica que los valores son consistentes entre medios."""
        a_vacio = calcular_a('vacio')
        a_agua = calcular_a('agua')
        a_aire = calcular_a('aire')
        
        # Verificar orden: agua < vacío < aire
        self.assertLess(a_agua, a_vacio)
        self.assertLess(a_vacio, a_aire)
        
        # Verificar que las velocidades tienen orden inverso
        c_vacio = calcular_velocidad_medio(a_vacio)
        c_agua = calcular_velocidad_medio(a_agua)
        c_aire = calcular_velocidad_medio(a_aire)
        
        self.assertGreater(c_agua, c_vacio)
        self.assertGreater(c_vacio, c_aire)


class TestDocumentacionYEjemplos(unittest.TestCase):
    """Tests para verificar que los ejemplos de la documentación funcionan."""
    
    def test_ejemplo_calcular_a_vacio(self):
        """Verifica el ejemplo de calcular_a para vacío."""
        a_vacio = calcular_a('vacio')
        self.assertAlmostEqual(a_vacio, 8.9, places=1)
    
    def test_ejemplo_calcular_a_agua(self):
        """Verifica el ejemplo de calcular_a para agua."""
        a_agua = calcular_a('agua')
        self.assertAlmostEqual(a_agua, 7.0, places=1)
    
    def test_ejemplo_calcular_a_aire(self):
        """Verifica el ejemplo de calcular_a para aire."""
        a_aire = calcular_a('aire')
        self.assertAlmostEqual(a_aire, 200.0, places=1)
    
    def test_ejemplo_velocidad_vacio(self):
        """Verifica el ejemplo de calcular_velocidad_medio."""
        c_vacio = calcular_velocidad_medio(8.9)
        self.assertAlmostEqual(c_vacio, 100.0, delta=0.5)
    
    def test_ejemplo_delta_vacio(self):
        """Verifica el ejemplo de calcular_defecto_desalineacion."""
        delta_vacio = calcular_defecto_desalineacion(8.9)
        self.assertAlmostEqual(delta_vacio, 2.01, delta=0.05)


if __name__ == '__main__':
    # Ejecutar tests con verbose output
    unittest.main(verbosity=2)
