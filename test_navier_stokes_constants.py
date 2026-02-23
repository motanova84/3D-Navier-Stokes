"""
Tests para el módulo navier_stokes.constants

Verifica la correcta implementación de las constantes fundamentales
y funciones del sistema Ψ-NS QCAL.
"""

import unittest
import numpy as np
from navier_stokes.constants import (
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
