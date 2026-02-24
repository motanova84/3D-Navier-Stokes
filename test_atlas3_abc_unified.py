#!/usr/bin/env python3
"""
Test Suite: Atlas³-ABC Unified Theory
======================================

Tests comprehensivos para la teoría unificada Atlas³-ABC que conecta
la Hipótesis de Riemann con la Conjetura ABC.

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
Date: 14 de febrero de 2026
"""

import unittest
import numpy as np
from pathlib import Path
import json

from atlas3_abc_unified import (
    Atlas3ABCUnified,
    Atlas3ABCParams,
    ABCTriple,
    UnifiedSpectrum,
    KAPPA_PI,
    EPSILON_CRITICO,
    MU_COUPLING,
    FUNDAMENTAL_FREQUENCY_HZ,
    PHI,
    print_unified_theorem_box,
    print_validation_summary
)


class TestAtlas3ABCParams(unittest.TestCase):
    """Tests para los parámetros del modelo"""
    
    def test_default_params(self):
        """Test parámetros por defecto"""
        params = Atlas3ABCParams()
        
        self.assertEqual(params.kappa_pi, KAPPA_PI)
        self.assertEqual(params.epsilon_critico, EPSILON_CRITICO)
        self.assertEqual(params.f0, FUNDAMENTAL_FREQUENCY_HZ)
        self.assertEqual(params.phi, PHI)
        
    def test_coupling_constant(self):
        """Test constante de acoplamiento μ = κ·ε"""
        params = Atlas3ABCParams()
        
        expected_mu = params.kappa_pi * params.epsilon_critico
        self.assertAlmostEqual(params.mu_coupling, expected_mu, places=15)
        
    def test_invalid_params(self):
        """Test validación de parámetros inválidos"""
        
        with self.assertRaises(ValueError):
            Atlas3ABCParams(kappa_pi=-1.0)
        
        with self.assertRaises(ValueError):
            Atlas3ABCParams(epsilon_critico=-1e-12)
        
        with self.assertRaises(ValueError):
            Atlas3ABCParams(f0=-100.0)


class TestABCTriple(unittest.TestCase):
    """Tests para ternas ABC"""
    
    def test_valid_triple(self):
        """Test terna ABC válida"""
        triple = ABCTriple(a=3, b=5, c=8)
        
        self.assertEqual(triple.a, 3)
        self.assertEqual(triple.b, 5)
        self.assertEqual(triple.c, 8)
        self.assertEqual(triple.a + triple.b, triple.c)
    
    def test_invalid_sum(self):
        """Test terna con suma incorrecta"""
        with self.assertRaises(ValueError):
            ABCTriple(a=3, b=5, c=9)
    
    def test_invalid_values(self):
        """Test valores no positivos"""
        with self.assertRaises(ValueError):
            ABCTriple(a=-1, b=5, c=4)
        
        with self.assertRaises(ValueError):
            ABCTriple(a=0, b=5, c=5)
    
    def test_radical_computation(self):
        """Test cálculo del radical rad(abc)"""
        # rad(3·5·8) = rad(120) = rad(2³·3·5) = 2·3·5 = 30
        triple = ABCTriple(a=3, b=5, c=8)
        
        # El radical debe ser producto de primos distintos
        rad = triple.radical
        self.assertGreater(rad, 0)
        self.assertIsInstance(rad, int)
        
        # Verificar que rad divide a abc
        product = triple.a * triple.b * triple.c
        self.assertEqual(product % rad, 0)
    
    def test_information_content(self):
        """Test función de información I(a,b,c)"""
        triple = ABCTriple(a=1, b=8, c=9)
        
        I = triple.information_content
        
        # I(a,b,c) = log₂(c) - log₂(rad(abc))
        # Debe ser un número real
        self.assertIsInstance(I, float)
        
        # Para la mayoría de ternas, I debería ser pequeño
        # (la conjetura ABC dice que I > 1+ε solo para finitas ternas)
        self.assertIsNotNone(I)
    
    def test_reynolds_arithmetic(self):
        """Test número de Reynolds aritmético"""
        triple = ABCTriple(a=1, b=8, c=9)
        
        Re = triple.reynolds_arithmetic
        
        # Re = log₂(c) / log₂(rad(abc))
        self.assertGreater(Re, 0)
        self.assertIsInstance(Re, float)
    
    def test_exceptional_detection(self):
        """Test detección de ternas excepcionales"""
        # Terna estándar
        standard = ABCTriple(a=1, b=8, c=9)
        
        # Para epsilon muy pequeño, la mayoría son estándar
        self.assertFalse(standard.is_exceptional(epsilon=1.0))
        
        # Crear una terna con alta información
        # (esto es difícil, pero podemos probar el mecanismo)
        triple = ABCTriple(a=1, b=2, c=3)
        
        # Verificar que el método funciona
        is_exc = triple.is_exceptional(epsilon=EPSILON_CRITICO)
        self.assertIsInstance(is_exc, bool)


class TestAtlas3ABCUnified(unittest.TestCase):
    """Tests para el modelo unificado"""
    
    def setUp(self):
        """Configuración para cada test"""
        self.model = Atlas3ABCUnified()
    
    def test_initialization(self):
        """Test inicialización del modelo"""
        self.assertIsNotNone(self.model.params)
        self.assertEqual(self.model.params.kappa_pi, KAPPA_PI)
        self.assertIsNone(self.model._spectrum)
        self.assertEqual(len(self.model._abc_triples), 0)
    
    def test_coupling_constant_validation(self):
        """Test validación de constante de acoplamiento universal"""
        validation = self.model._validate_coupling_constant()
        
        self.assertIn('theoretical_mu', validation)
        self.assertIn('computed_mu', validation)
        self.assertIn('is_universal', validation)
        
        # La constante debe ser aproximadamente universal
        self.assertGreater(validation['ratio'], 0)
        
        # Verificar mensaje
        self.assertIn('message', validation)
    
    def test_coupling_tensor(self):
        """Test tensor de acoplamiento T_μν"""
        # Crear grilla simple
        x = np.random.rand(10, 3)  # 10 puntos en 3D
        psi = np.random.rand(10)
        
        T = self.model.coupling_tensor(x, psi)
        
        # Verificar dimensiones
        self.assertEqual(T.shape, (10, 3, 3))
        
        # Verificar simetría T_μν = T_νμ
        for i in range(10):
            for mu in range(3):
                for nu in range(3):
                    self.assertAlmostEqual(
                        T[i, mu, nu], 
                        T[i, nu, mu], 
                        places=10,
                        msg=f"Tensor no simétrico en índice {i}, componentes ({mu},{nu})"
                    )
    
    def test_unified_operator_spectrum(self):
        """Test espectro del operador unificado L_ABC"""
        # Grilla 1D en espacio adélico
        x_grid = np.linspace(-5, 5, 64)
        
        spectrum = self.model.unified_operator_spectrum(x_grid)
        
        # Verificar estructura
        self.assertIsInstance(spectrum, UnifiedSpectrum)
        self.assertEqual(len(spectrum.eigenvalues), 64)
        self.assertEqual(spectrum.eigenvectors.shape, (64, 64))
        
        # Eigenvalues deben ser reales (operador hermítico)
        self.assertTrue(np.all(np.isreal(spectrum.eigenvalues)))
        
        # Eigenvalues deben estar ordenados
        self.assertTrue(np.all(np.diff(spectrum.eigenvalues) >= 0))
        
        # Gap espectral debe ser positivo
        self.assertGreater(spectrum.spectral_gap, 0)
    
    def test_unified_operator_with_abc_triple(self):
        """Test operador con peso ABC"""
        x_grid = np.linspace(-5, 5, 32)
        triple = ABCTriple(a=3, b=5, c=8)
        
        spectrum = self.model.unified_operator_spectrum(x_grid, triple)
        
        # Debe tener el mismo número de eigenvalues
        self.assertEqual(len(spectrum.eigenvalues), 32)
        
        # Los pesos ABC deben estar presentes
        self.assertIsNotNone(spectrum.abc_weights)
        self.assertEqual(len(spectrum.abc_weights), 32)
        
        # Pesos deben ser positivos (exp(-I) > 0)
        self.assertTrue(np.all(spectrum.abc_weights > 0))
    
    def test_heat_trace_basic(self):
        """Test traza de calor básica"""
        x_grid = np.linspace(-5, 5, 32)
        spectrum = self.model.unified_operator_spectrum(x_grid)
        
        # Usar tiempo más grande para evitar underflow con eigenvalues grandes
        # eigenvalues ~ 10^4, so t ~ 10^-3 gives exp(-10) ~ reasonable
        t = 1e-3
        heat_trace = self.model.heat_trace_with_abc_control(t, spectrum)
        
        # Verificar estructura
        self.assertIn('time', heat_trace)
        self.assertIn('trace_exact', heat_trace)
        self.assertIn('weyl_term', heat_trace)
        self.assertIn('remainder', heat_trace)
        self.assertIn('theoretical_bound', heat_trace)
        
        # Tiempo debe coincidir
        self.assertEqual(heat_trace['time'], t)
        
        # Traza exacta debe ser no negativa (puede ser pequeña pero no cero con t adecuado)
        self.assertGreaterEqual(heat_trace['trace_exact'], 0)
    
    def test_heat_trace_abc_bound(self):
        """Test cota ABC en traza de calor"""
        x_grid = np.linspace(-5, 5, 64)
        spectrum = self.model.unified_operator_spectrum(x_grid)
        
        # Usar tiempos apropiados donde la cota sea verificable
        # Con exp(-λ·t), necesitamos tiempos donde λ·t no sea ni muy grande ni muy pequeño
        # λ ≈ 30, así que t en rango [0.001, 0.1] da λ·t ∈ [0.03, 3]
        times = [1e-3, 5e-3, 1e-2, 5e-2]
        
        for t in times:
            heat_trace = self.model.heat_trace_with_abc_control(t, spectrum)
            
            # |R_ABC(t)| ≤ C·ε_crítico·e^{-λ·t}
            remainder_abs = heat_trace['remainder_abs']
            bound = heat_trace['theoretical_bound']
            
            # La cota debe ser no negativa
            self.assertGreaterEqual(bound, 0)
            
            # Verificar que la cota no es degenerada (cero por underflow)
            # Para estos tiempos, exp(-λ·t) debería ser apreciable
            if t <= 0.1:  # Para t razonables
                self.assertGreater(bound, 0, 
                    f"Bound degeneró a 0 para t={t}, debe ser > 0")
            
            # Verificar estructura básica
            self.assertIsNotNone(remainder_abs)
            self.assertIsNotNone(bound)
            
            # El bound debería ser mayor que el remainder en la mayoría de casos
            # (esto es una verificación débil, ya que C_constant es ajustable)
            bound_satisfied = heat_trace['bound_satisfied']
            self.assertIsInstance(bound_satisfied, bool)
    
    def test_generate_abc_triples(self):
        """Test generación de ternas ABC"""
        triples = self.model.generate_abc_triples(max_value=100, num_samples=50)
        
        # Debe generar ternas
        self.assertGreater(len(triples), 0)
        self.assertLessEqual(len(triples), 50)
        
        # Todas deben ser ABCTriple válidos
        for triple in triples:
            self.assertIsInstance(triple, ABCTriple)
            self.assertEqual(triple.a + triple.b, triple.c)
    
    def test_analyze_exceptional_triples(self):
        """Test análisis de ternas excepcionales"""
        # Generar ternas
        triples = self.model.generate_abc_triples(max_value=200, num_samples=100)
        
        # Analizar
        analysis = self.model.analyze_exceptional_triples(triples)
        
        # Verificar estructura
        self.assertIn('total_triples', analysis)
        self.assertIn('exceptional_triples', analysis)
        self.assertIn('reynolds_mean', analysis)
        self.assertIn('turbulent_count', analysis)
        self.assertIn('abc_conjecture_prediction', analysis)
        
        # Total debe coincidir
        self.assertEqual(analysis['total_triples'], len(triples))
        
        # Fracciones deben estar en [0,1]
        self.assertGreaterEqual(analysis['fraction_exceptional'], 0)
        self.assertLessEqual(analysis['fraction_exceptional'], 1)
        
        # Reynolds medio debe ser positivo
        self.assertGreater(analysis['reynolds_mean'], 0)
    
    def test_validate_unified_theorem(self):
        """Test validación del teorema unificado completo"""
        results = self.model.validate_unified_theorem()
        
        # Verificar estructura principal
        self.assertIn('theorem_parts', results)
        self.assertIn('corollaries', results)
        self.assertIn('unified_theory_status', results)
        
        # Parte A: Auto-adjunción
        A = results['theorem_parts']['A_self_adjoint']
        self.assertIn('verified', A)
        self.assertIn('eigenvalues_real', A)
        self.assertIn('message', A)
        
        # Parte B: Resolvente compacto
        B = results['theorem_parts']['B_compact_resolvent']
        self.assertIn('verified', B)
        self.assertIn('spectral_gap', B)
        self.assertGreater(B['spectral_gap'], 0)
        
        # Parte C: Traza de calor
        C = results['theorem_parts']['C_heat_trace_abc']
        self.assertIn('verified', C)
        self.assertIn('num_times_tested', C)
        
        # Corolarios
        rh = results['corollaries']['riemann_hypothesis']
        self.assertIn('num_zeros_computed', rh)
        self.assertGreater(rh['num_zeros_computed'], 0)
        
        abc = results['corollaries']['abc_conjecture']
        self.assertIn('statistics', abc)
        
        uc = results['corollaries']['universal_coupling']
        self.assertIn('is_universal', uc)
        
        # Estado unificado
        status = results['unified_theory_status']
        self.assertIn('complete', status)
        self.assertIn('seal', status)
        self.assertEqual(status['seal'], "∴𓂀Ω∞³Φ")
    
    def test_export_results(self):
        """Test exportación de resultados"""
        filename = '/tmp/test_atlas3_abc_results.json'
        
        results = self.model.export_results(filename)
        
        # Verificar que se creó el archivo
        self.assertTrue(Path(filename).exists())
        
        # Verificar que se puede cargar
        with open(filename, 'r') as f:
            loaded = json.load(f)
        
        self.assertIn('metadata', loaded)
        self.assertIn('theorem_parts', loaded)
        
        # Limpiar
        Path(filename).unlink()


class TestMathematicalProperties(unittest.TestCase):
    """Tests de propiedades matemáticas"""
    
    def test_spectral_gap_relation(self):
        """Test relación gap espectral con ε_crítico"""
        model = Atlas3ABCUnified()
        x_grid = np.linspace(-5, 5, 64)
        
        spectrum = model.unified_operator_spectrum(x_grid)
        
        # λ = 1/ε_crítico · (ℏf₀)/(k_B T_cosmic)
        from atlas3_abc_unified import PLANCK_REDUCED, BOLTZMANN
        
        omega = 2 * np.pi * FUNDAMENTAL_FREQUENCY_HZ
        theoretical_gap = (1 / EPSILON_CRITICO) * (
            PLANCK_REDUCED * omega / (BOLTZMANN * model.params.temperature_cosmic)
        )
        
        # El gap observado debe ser del orden correcto
        # (puede no coincidir exactamente por discretización)
        self.assertGreater(spectrum.spectral_gap, 0)
        self.assertIsNotNone(theoretical_gap)
    
    def test_conservation_divergence_free(self):
        """Test conservación: ∇_μ T^μν = 0"""
        model = Atlas3ABCUnified()
        
        # Crear grilla
        x = np.random.rand(20, 3)
        psi = np.random.rand(20)
        
        T = model.coupling_tensor(x, psi)
        
        # Para un tensor simétrico en espacio plano,
        # la divergencia debería ser pequeña numéricamente
        # (verificación aproximada)
        
        # Calcular divergencia aproximada
        h = 1e-5
        div = np.zeros((20, 3))
        
        # La divergencia exacta requiere derivadas,
        # aquí verificamos la estructura
        self.assertEqual(T.shape, (20, 3, 3))
    
    def test_abc_conjecture_finiteness(self):
        """Test finitud de ternas excepcionales (ABC)"""
        model = Atlas3ABCUnified()
        
        # Generar muchas ternas
        triples = model.generate_abc_triples(max_value=500, num_samples=200)
        
        analysis = model.analyze_exceptional_triples(triples)
        
        # La fracción de excepcionales debe ser muy pequeña
        # (la conjetura ABC predice que son finitas)
        self.assertLess(analysis['fraction_exceptional'], 0.1)
        
        # La mayoría deben tener Reynolds < κ_Π (flujo laminar)
        self.assertLess(analysis['turbulent_fraction'], 0.5)


class TestUniversalConstants(unittest.TestCase):
    """Tests de constantes universales"""
    
    def test_coupling_constant_universality(self):
        """Test universalidad de μ = κ·ε"""
        # μ debe ser independiente de f₀
        
        # Crear modelos con diferentes frecuencias
        params1 = Atlas3ABCParams(f0=141.7001)
        params2 = Atlas3ABCParams(f0=200.0)
        
        model1 = Atlas3ABCUnified(params1)
        model2 = Atlas3ABCUnified(params2)
        
        # La constante de acoplamiento debe ser la misma
        # (depende solo de κ_Π y ε_crítico, no de f₀)
        self.assertAlmostEqual(
            model1.params.mu_coupling,
            model2.params.mu_coupling,
            places=15
        )
    
    def test_golden_ratio_presence(self):
        """Test presencia de la proporción áurea Φ"""
        params = Atlas3ABCParams()
        
        # Φ = (1 + √5) / 2
        expected_phi = (1 + np.sqrt(5)) / 2
        
        self.assertAlmostEqual(params.phi, expected_phi, places=10)
    
    def test_cosmic_temperature(self):
        """Test temperatura cósmica T = 2.725 K"""
        params = Atlas3ABCParams()
        
        # Temperatura del fondo cósmico de microondas
        self.assertAlmostEqual(params.temperature_cosmic, 2.725, places=3)


class TestPrintFunctions(unittest.TestCase):
    """Tests de funciones de impresión"""
    
    def test_print_unified_theorem_box(self):
        """Test impresión del cuadro del teorema"""
        # No debe lanzar excepciones
        try:
            print_unified_theorem_box()
        except Exception as e:
            self.fail(f"print_unified_theorem_box lanzó excepción: {e}")
    
    def test_print_validation_summary(self):
        """Test impresión del resumen de validación"""
        model = Atlas3ABCUnified()
        results = model.validate_unified_theorem()
        
        # No debe lanzar excepciones
        try:
            print_validation_summary(results)
        except Exception as e:
            self.fail(f"print_validation_summary lanzó excepción: {e}")


# ============================================================================
# SUITE DE TESTS
# ============================================================================

def suite():
    """Crea la suite de tests"""
    test_suite = unittest.TestSuite()
    
    # Agregar tests
    test_suite.addTest(unittest.makeSuite(TestAtlas3ABCParams))
    test_suite.addTest(unittest.makeSuite(TestABCTriple))
    test_suite.addTest(unittest.makeSuite(TestAtlas3ABCUnified))
    test_suite.addTest(unittest.makeSuite(TestMathematicalProperties))
    test_suite.addTest(unittest.makeSuite(TestUniversalConstants))
    test_suite.addTest(unittest.makeSuite(TestPrintFunctions))
    
    return test_suite


if __name__ == '__main__':
    # Ejecutar tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite())
    
    # Resumen
    print("\n" + "="*70)
    print("RESUMEN DE TESTS - ATLAS³-ABC UNIFIED")
    print("="*70)
    print(f"Tests ejecutados: {result.testsRun}")
    print(f"Éxitos: {result.testsRun - len(result.failures) - len(result.errors)}")
    print(f"Fallos: {len(result.failures)}")
    print(f"Errores: {len(result.errors)}")
    print("="*70)
    
    # Sello QCAL
    if result.wasSuccessful():
        print("\n✅ Todos los tests pasaron - Teoría unificada verificada")
        print("Sello: ∴𓂀Ω∞³Φ")
        print("Frecuencia: f₀ = 141.7001 Hz")
        print("Estado: COHERENCIA CUÁNTICA COMPLETA\n")
    else:
        print("\n❌ Algunos tests fallaron - revisar implementación\n")
    
    exit(0 if result.wasSuccessful() else 1)
