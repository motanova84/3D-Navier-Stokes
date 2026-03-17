#!/usr/bin/env python3
"""
Tests for Direct Resonance API
===============================

Tests para la biblioteca de simulación de fluidos por resonancia directa.

Author: JMMB Ψ✧∞³
License: MIT
"""

import unittest
import numpy as np
from direct_resonance_api import (
    DirectResonanceSimulator,
    FluidSystemConfig,
    AerodynamicResults,
    create_example_wing_geometry
)


class TestFluidSystemConfig(unittest.TestCase):
    """Tests para configuración del sistema fluido"""
    
    def test_default_config(self):
        """Test configuración por defecto"""
        config = FluidSystemConfig()
        
        self.assertEqual(config.f0, 141.7001)
        self.assertEqual(config.psi_threshold, 0.888)
        self.assertEqual(config.nx, 64)
        self.assertEqual(config.ny, 32)
        self.assertEqual(config.nz, 32)
    
    def test_custom_config(self):
        """Test configuración personalizada"""
        config = FluidSystemConfig(
            f0=150.0,
            psi_threshold=0.9,
            nx=128
        )
        
        self.assertEqual(config.f0, 150.0)
        self.assertEqual(config.psi_threshold, 0.9)
        self.assertEqual(config.nx, 128)


class TestDirectResonanceSimulator(unittest.TestCase):
    """Tests para el simulador de resonancia directa"""
    
    def setUp(self):
        """Configurar simulador para tests"""
        config = FluidSystemConfig(nx=32, ny=16, nz=16)  # Más pequeño para tests
        self.simulator = DirectResonanceSimulator(config)
        self.wing_geometry = create_example_wing_geometry()
    
    def test_simulator_initialization(self):
        """Test inicialización del simulador"""
        self.assertIsNotNone(self.simulator)
        self.assertIsNotNone(self.simulator.config)
        self.assertEqual(self.simulator.coherence_field, 0.888)
    
    def test_solve_direct_resonance(self):
        """Test resolución por resonancia directa"""
        solution = self.simulator.solve_direct_resonance(
            geometry=self.wing_geometry,
            velocity_inlet=10.0,
            angle_of_attack=6.0
        )
        
        # Verificar estructura de solución
        self.assertIn('velocity_field', solution)
        self.assertIn('pressure_field', solution)
        self.assertIn('resonance_field', solution)
        self.assertIn('coherence', solution)
        self.assertIn('autonomy_spectrum', solution)
        self.assertIn('stable', solution)
        self.assertIn('iterations', solution)
        self.assertIn('converged', solution)
        
        # Verificar que NO usa iteraciones
        self.assertEqual(solution['iterations'], 0)
        
        # Verificar que siempre converge
        self.assertTrue(solution['converged'])
        
        # Verificar coherencia
        self.assertGreaterEqual(solution['coherence'], 0.0)
        self.assertLessEqual(solution['coherence'], 1.0)
    
    def test_compute_optimal_lift_psi_only(self):
        """Test cálculo de sustentación (solo Ψ, sin presiones)"""
        solution = self.simulator.solve_direct_resonance(
            self.wing_geometry, 10.0, 6.0
        )
        
        cl, details = self.simulator.compute_optimal_lift_psi_only(
            solution, self.wing_geometry
        )
        
        # Verificar coeficiente de sustentación
        self.assertIsInstance(cl, float)
        self.assertGreater(cl, 0.0)  # Debe ser positivo para sustentación
        
        # Verificar detalles
        self.assertIn('circulation', details)
        self.assertIn('lift_force', details)
        self.assertIn('method', details)
        self.assertIn('no pressure', details['method'].lower())
    
    def test_compute_drag_by_coherence(self):
        """Test cálculo de drag por coherencia"""
        solution = self.simulator.solve_direct_resonance(
            self.wing_geometry, 10.0, 6.0
        )
        
        cd, details = self.simulator.compute_drag_by_coherence(
            solution, self.wing_geometry
        )
        
        # Verificar coeficiente de drag
        self.assertIsInstance(cd, float)
        self.assertGreater(cd, 0.0)
        
        # Verificar que hay reducción
        self.assertIn('drag_reduction_percent', details)
        self.assertIn('method', details)
        self.assertIn('coherence', details['method'].lower())
    
    def test_predict_structural_stability(self):
        """Test predicción de estabilidad estructural"""
        solution = self.simulator.solve_direct_resonance(
            self.wing_geometry, 10.0, 6.0
        )
        
        material = {'yield_stress': 276e6}
        prediction = self.simulator.predict_structural_stability(
            solution, material
        )
        
        # Verificar predicción
        self.assertIn('stability_index', prediction)
        self.assertIn('status', prediction)
        self.assertIn('risk_level', prediction)
        self.assertIn('fatigue_life_cycles', prediction)
        
        # Verificar índice de estabilidad
        self.assertGreaterEqual(prediction['stability_index'], 0.0)
        self.assertLessEqual(prediction['stability_index'], 1.0)
        
        # Verificar que usa espectro del tensor C
        self.assertIn('method', prediction)
        self.assertIn('tensor', prediction['method'].lower())
    
    def test_compute_aerodynamic_efficiency(self):
        """Test cálculo de eficiencia aerodinámica"""
        cl = 1.2
        cd = 0.08
        
        efficiency = self.simulator.compute_aerodynamic_efficiency(cl, cd)
        
        # Verificar métricas
        self.assertIn('lift_to_drag_ratio', efficiency)
        self.assertIn('improvement_percent', efficiency)
        self.assertIn('achieves_target', efficiency)
        
        # Verificar L/D
        expected_ld = cl / cd
        self.assertAlmostEqual(
            efficiency['lift_to_drag_ratio'], 
            expected_ld, 
            places=2
        )
    
    def test_run_complete_analysis(self):
        """Test análisis completo"""
        material = {'yield_stress': 276e6}
        
        results = self.simulator.run_complete_analysis(
            geometry=self.wing_geometry,
            velocity_inlet=10.0,
            angle_of_attack=6.0,
            material_properties=material
        )
        
        # Verificar tipo de resultados
        self.assertIsInstance(results, AerodynamicResults)
        
        # Verificar campos
        self.assertIsInstance(results.lift_coefficient, float)
        self.assertIsInstance(results.drag_coefficient, float)
        self.assertIsInstance(results.efficiency_improvement, float)
        self.assertIsInstance(results.coherence_score, float)
        self.assertIsInstance(results.stability_index, float)
        self.assertIsInstance(results.laminar_guarantee, bool)
        self.assertIsInstance(results.reproducibility_hash, str)
        self.assertIsInstance(results.timestamp, str)
        
        # Verificar rangos válidos
        self.assertGreater(results.lift_coefficient, 0.0)
        self.assertGreater(results.drag_coefficient, 0.0)
        self.assertGreaterEqual(results.coherence_score, 0.0)
        self.assertLessEqual(results.coherence_score, 1.0)
        self.assertGreaterEqual(results.stability_index, 0.0)
        self.assertLessEqual(results.stability_index, 1.0)


class TestResonanceField(unittest.TestCase):
    """Tests para campos de resonancia"""
    
    def setUp(self):
        """Configurar simulador"""
        self.simulator = DirectResonanceSimulator()
    
    def test_generate_resonance_field(self):
        """Test generación de campo de resonancia"""
        field = self.simulator._generate_resonance_field()
        
        # Verificar forma
        nx, ny, nz = self.simulator.config.nx, self.simulator.config.ny, self.simulator.config.nz
        self.assertEqual(field.shape, (nx, ny, nz, 3))
        
        # Verificar que no es cero
        self.assertGreater(np.abs(field).sum(), 0.0)
    
    def test_compute_quantum_coherence(self):
        """Test cálculo de coherencia cuántica"""
        # Crear campo de velocidad uniforme (alta coherencia)
        velocity_uniform = np.ones((10, 10, 10, 3)) * 5.0
        coherence_high = self.simulator._compute_quantum_coherence(velocity_uniform)
        
        # Crear campo de velocidad caótico (baja coherencia)
        velocity_chaotic = np.random.randn(10, 10, 10, 3) * 10.0
        coherence_low = self.simulator._compute_quantum_coherence(velocity_chaotic)
        
        # Verificar que coherencia uniforme > coherencia caótica
        self.assertGreater(coherence_high, coherence_low)
        
        # Verificar rangos
        self.assertGreaterEqual(coherence_high, self.simulator.config.psi_threshold)
        self.assertLessEqual(coherence_high, 1.0)


class TestWingGeometry(unittest.TestCase):
    """Tests para geometría de ala"""
    
    def test_create_example_wing_geometry(self):
        """Test creación de geometría de ejemplo"""
        geometry = create_example_wing_geometry()
        
        # Verificar forma
        self.assertEqual(geometry.shape[1], 3)  # Puntos 3D
        self.assertGreater(geometry.shape[0], 0)  # Al menos un punto
    
    def test_estimate_wing_area(self):
        """Test estimación de área del ala"""
        simulator = DirectResonanceSimulator()
        geometry = create_example_wing_geometry()
        
        area = simulator._estimate_wing_area(geometry)
        
        # Verificar que área es positiva
        self.assertGreater(area, 0.0)


class TestReproducibility(unittest.TestCase):
    """Tests para reproducibilidad"""
    
    def test_same_config_same_results(self):
        """Test que misma configuración da mismos resultados"""
        config = FluidSystemConfig(f0=141.7001, psi_threshold=0.888)
        
        sim1 = DirectResonanceSimulator(config)
        sim2 = DirectResonanceSimulator(config)
        
        geometry = create_example_wing_geometry()
        
        results1 = sim1.run_complete_analysis(geometry, 10.0, 6.0)
        results2 = sim2.run_complete_analysis(geometry, 10.0, 6.0)
        
        # Verificar que los hashes de reproducibilidad son iguales
        self.assertEqual(
            results1.reproducibility_hash, 
            results2.reproducibility_hash
        )
    
    def test_reproducibility_hash_generation(self):
        """Test generación de hash de reproducibilidad"""
        simulator = DirectResonanceSimulator()
        
        solution = {
            'coherence': 0.95,
            'stable': True
        }
        
        hash1 = simulator._generate_reproducibility_hash(solution)
        hash2 = simulator._generate_reproducibility_hash(solution)
        
        # Verificar que hashes son iguales para misma solución
        self.assertEqual(hash1, hash2)
        
        # Verificar formato (8 caracteres hexadecimales)
        self.assertEqual(len(hash1), 8)
        self.assertTrue(all(c in '0123456789abcdef' for c in hash1))


class TestEfficiencyImprovement(unittest.TestCase):
    """Tests para mejora de eficiencia aerodinámica"""
    
    def test_efficiency_improvement_calculation(self):
        """Test cálculo de mejora de eficiencia"""
        simulator = DirectResonanceSimulator()
        
        # Caso con mejora significativa
        cl_good = 1.5
        cd_good = 0.06
        
        efficiency = simulator.compute_aerodynamic_efficiency(cl_good, cd_good)
        
        # Verificar que calcula L/D correctamente
        expected_ld = cl_good / cd_good
        self.assertAlmostEqual(
            efficiency['lift_to_drag_ratio'],
            expected_ld,
            places=2
        )
        
        # Verificar que detecta si cumple objetivo
        self.assertIn('achieves_target', efficiency)
    
    def test_target_improvement_23_percent(self):
        """Test que el objetivo es +23.3% de mejora"""
        simulator = DirectResonanceSimulator()
        
        # Configurar CL y CD para alcanzar +23.3% mejora
        # L/D tradicional ~ 12.0
        # L/D objetivo ~ 12.0 * 1.233 = 14.8
        cl = 1.48
        cd = 0.10
        
        efficiency = simulator.compute_aerodynamic_efficiency(cl, cd)
        
        # Verificar que objetivo es 23.3%
        self.assertEqual(efficiency['target_improvement'], 23.3)


class TestNoIterations(unittest.TestCase):
    """Tests para verificar que NO hay iteraciones"""
    
    def test_zero_iterations(self):
        """Test que la resolución NO usa iteraciones"""
        simulator = DirectResonanceSimulator()
        geometry = create_example_wing_geometry()
        
        solution = simulator.solve_direct_resonance(geometry, 10.0, 6.0)
        
        # CRÍTICO: Debe ser exactamente 0 iteraciones
        self.assertEqual(solution['iterations'], 0)
    
    def test_always_converges(self):
        """Test que siempre converge (sin divergencia numérica)"""
        simulator = DirectResonanceSimulator()
        geometry = create_example_wing_geometry()
        
        # Probar con diferentes configuraciones
        angles = [0.0, 5.0, 10.0, 15.0]
        velocities = [5.0, 10.0, 20.0, 30.0]
        
        for angle in angles:
            for velocity in velocities:
                solution = simulator.solve_direct_resonance(
                    geometry, velocity, angle
                )
                
                # Debe SIEMPRE converger
                self.assertTrue(solution['converged'])
                
                # Debe SIEMPRE tener 0 iteraciones
                self.assertEqual(solution['iterations'], 0)


class TestCoherenceGuarantee(unittest.TestCase):
    """Tests para garantía de coherencia"""
    
    def test_coherence_above_threshold(self):
        """Test que coherencia está por encima del umbral"""
        simulator = DirectResonanceSimulator()
        geometry = create_example_wing_geometry()
        
        solution = simulator.solve_direct_resonance(geometry, 10.0, 6.0)
        
        # Coherencia debe ser >= threshold
        self.assertGreaterEqual(
            solution['coherence'],
            simulator.config.psi_threshold
        )
    
    def test_laminar_guarantee(self):
        """Test garantía de flujo laminar"""
        simulator = DirectResonanceSimulator()
        geometry = create_example_wing_geometry()
        
        results = simulator.run_complete_analysis(geometry, 10.0, 6.0)
        
        # Si coherencia es alta, debe garantizar flujo laminar
        if results.coherence_score >= simulator.config.psi_threshold:
            self.assertTrue(results.laminar_guarantee)


def run_all_tests():
    """Ejecutar todos los tests"""
    print("\n" + "="*80)
    print("  🧪 EJECUTANDO TESTS - API DE RESONANCIA DIRECTA")
    print("="*80 + "\n")
    
    # Crear suite de tests
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Agregar todas las clases de tests
    suite.addTests(loader.loadTestsFromTestCase(TestFluidSystemConfig))
    suite.addTests(loader.loadTestsFromTestCase(TestDirectResonanceSimulator))
    suite.addTests(loader.loadTestsFromTestCase(TestResonanceField))
    suite.addTests(loader.loadTestsFromTestCase(TestWingGeometry))
    suite.addTests(loader.loadTestsFromTestCase(TestReproducibility))
    suite.addTests(loader.loadTestsFromTestCase(TestEfficiencyImprovement))
    suite.addTests(loader.loadTestsFromTestCase(TestNoIterations))
    suite.addTests(loader.loadTestsFromTestCase(TestCoherenceGuarantee))
    
    # Ejecutar tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Resumen
    print("\n" + "="*80)
    print("  📊 RESUMEN DE TESTS")
    print("="*80)
    print(f"  Tests ejecutados: {result.testsRun}")
    print(f"  ✅ Exitosos: {result.testsRun - len(result.failures) - len(result.errors)}")
    print(f"  ❌ Fallidos: {len(result.failures)}")
    print(f"  ⚠️ Errores: {len(result.errors)}")
    print("="*80 + "\n")
    
    return result


if __name__ == "__main__":
    result = run_all_tests()
    
    # Exit con código apropiado
    exit(0 if result.wasSuccessful() else 1)
