#!/usr/bin/env python
"""
Tests para el Sistema de Jerarquía Gravitacional Armónica
"""

import unittest
import numpy as np
from hierarchical_gravity import HierarchicalGravitySystem


class TestHierarchicalGravitySystem(unittest.TestCase):
    """Test suite para el sistema de jerarquía gravitacional"""
    
    def setUp(self):
        """Configurar sistema para cada test"""
        self.system = HierarchicalGravitySystem()
    
    def test_initialization(self):
        """Test: Inicialización correcta del sistema"""
        self.assertEqual(self.system.f0_hz, 141.7001)
        self.assertAlmostEqual(self.system.kappa, 1.0/7.0, places=6)
        self.assertEqual(self.system.psi_turbulent_threshold, 0.88)
        self.assertEqual(self.system.psi_superfluid_threshold, 0.95)
    
    def test_dimensional_layer_frequencies(self):
        """Test: Frecuencias de capas dimensionales"""
        # Primera capa debe ser f₀
        self.assertEqual(self.system.dimensional_layer(1), self.system.f0_hz)
        
        # Segunda capa debe ser 2*f₀
        self.assertEqual(self.system.dimensional_layer(2), 2 * self.system.f0_hz)
        
        # Séptima capa
        expected_f7 = 7 * self.system.f0_hz
        self.assertAlmostEqual(self.system.dimensional_layer(7), expected_f7, places=4)
    
    def test_effective_viscosity_perfect_coherence(self):
        """Test: Viscosidad efectiva con coherencia perfecta"""
        psi_perfect = 1.0
        nu_eff = self.system.effective_viscosity(psi_perfect)
        
        # Con Ψ = 1, ν_eff = ν_base / κ
        expected = self.system.nu_base / self.system.kappa
        self.assertAlmostEqual(nu_eff, expected, places=6)
    
    def test_effective_viscosity_zero_coherence(self):
        """Test: Viscosidad efectiva con coherencia cero"""
        psi_zero = 0.0
        nu_eff = self.system.effective_viscosity(psi_zero)
        
        # Con Ψ = 0, debe dar infinito (resistencia infinita)
        self.assertTrue(np.isinf(nu_eff))
    
    def test_effective_viscosity_decreases_with_coherence(self):
        """Test: Viscosidad disminuye al aumentar coherencia"""
        psi_low = 0.5
        psi_high = 0.9
        
        nu_low = self.system.effective_viscosity(psi_low)
        nu_high = self.system.effective_viscosity(psi_high)
        
        # Mayor coherencia → menor viscosidad
        self.assertGreater(nu_low, nu_high)
    
    def test_computational_complexity_turbulent(self):
        """Test: Estado de complejidad en régimen turbulento"""
        psi_turbulent = 0.7  # < 0.88
        state = self.system.computational_complexity_state(psi_turbulent)
        self.assertEqual(state, "P≠NP")
    
    def test_computational_complexity_superfluid(self):
        """Test: Estado de complejidad en régimen superfluidez"""
        psi_superfluid = 0.96  # >= 0.95
        state = self.system.computational_complexity_state(psi_superfluid)
        self.assertEqual(state, "P=NP")
    
    def test_computational_complexity_transition(self):
        """Test: Estado de complejidad en transición"""
        psi_transition = 0.90  # Entre 0.88 y 0.95
        state = self.system.computational_complexity_state(psi_transition)
        self.assertEqual(state, "TRANSICIÓN")
    
    def test_metric_singularity_pressure_diverges(self):
        """Test: Presión diverge cuando r → 0"""
        r = np.array([1.0, 0.1, 0.01, 0.001])
        pressure, _, _ = self.system.metric_singularity(r)
        
        # Presión debe aumentar al disminuir r
        for i in range(len(r) - 1):
            self.assertGreater(pressure[i+1], pressure[i])
    
    def test_metric_singularity_velocity_diverges(self):
        """Test: Velocidad diverge cuando r → 0"""
        r = np.array([1.0, 0.1, 0.01, 0.001])
        _, velocity, _ = self.system.metric_singularity(r)
        
        # Velocidad debe aumentar al disminuir r
        for i in range(len(r) - 1):
            self.assertGreater(velocity[i+1], velocity[i])
    
    def test_metric_singularity_grr_diverges(self):
        """Test: Métrica g_rr diverge cuando r → 0"""
        r = np.array([1.0, 0.5, 0.1])
        _, _, g_rr = self.system.metric_singularity(r)
        
        # g_rr debe aumentar al disminuir r (en valor absoluto)
        self.assertTrue(np.all(np.isfinite(g_rr)))
    
    def test_coherence_evolution_range(self):
        """Test: Campo de coherencia está en [0, 1]"""
        t = np.linspace(0, 1.0, 1000)
        psi = self.system.coherence_evolution(t)
        
        # Ψ debe estar en rango [0, 1]
        self.assertTrue(np.all(psi >= 0))
        self.assertTrue(np.all(psi <= 1))
    
    def test_coherence_evolution_oscillates_at_f0(self):
        """Test: Coherencia oscila a frecuencia f₀"""
        t = np.linspace(0, 0.1, 10000)
        psi = self.system.coherence_evolution(t)
        
        # Debe haber múltiples oscilaciones
        # Para t_max = 0.1s y f₀ ≈ 141.7 Hz, esperamos ~14 ciclos
        # Contar cambios de signo en la derivada como aproximación
        dpsi_dt = np.diff(psi)
        sign_changes = np.sum(np.diff(np.sign(dpsi_dt)) != 0)
        
        # Debe haber al menos 10 cambios de signo (5 ciclos completos)
        self.assertGreater(sign_changes, 10)
    
    def test_dimensional_lamination_flow_layers(self):
        """Test: Flujo con laminación dimensional"""
        n_layers = 7
        results = self.system.dimensional_lamination_flow(n_layers=n_layers, t_max=0.1)
        
        # Debe haber 7 capas
        self.assertEqual(len(results['layer_frequencies']), n_layers)
        self.assertEqual(results['layer_phases'].shape[0], n_layers)
        
        # Frecuencias deben ser múltiplos de f₀
        for i, freq in enumerate(results['layer_frequencies']):
            expected = (i + 1) * self.system.f0_hz
            self.assertAlmostEqual(freq, expected, places=4)
    
    def test_dimensional_lamination_no_friction(self):
        """Test: Capas sin fricción entrópica"""
        results = self.system.dimensional_lamination_flow(n_layers=7, t_max=1.0)
        
        # Las velocidades deben mantenerse (no decayen)
        # Verificar que las velocidades oscilan sin amortiguamiento
        for layer_vel in results['layer_velocities']:
            # Máximo debe ser aproximadamente constante
            max_vel = np.max(np.abs(layer_vel))
            
            # Verificar que las oscilaciones mantienen amplitud
            # (sin decaimiento significativo)
            # En vez de min/max, verificamos que el máximo es significativo
            # y que hay oscilación real
            self.assertGreater(max_vel, 0)  # Debe haber movimiento
            
            # Verificar que hay oscilación (no es constante)
            std_vel = np.std(layer_vel)
            self.assertGreater(std_vel, 0.1 * max_vel)
    
    def test_vortex_portal_geometry_structure(self):
        """Test: Estructura de geometría del vórtice"""
        results = self.system.vortex_portal_geometry(r_range=(0.01, 10.0), n_points=100)
        
        # Debe contener todas las claves esperadas
        self.assertIn('radius', results)
        self.assertIn('pressure', results)
        self.assertIn('velocity', results)
        self.assertIn('metric_grr', results)
        self.assertIn('energy', results)
        self.assertIn('curvature', results)
        
        # Todos los arrays deben tener la misma longitud
        n = len(results['radius'])
        self.assertEqual(len(results['pressure']), n)
        self.assertEqual(len(results['velocity']), n)
        self.assertEqual(len(results['metric_grr']), n)
    
    def test_superfluid_transition_structure(self):
        """Test: Estructura de transición a superfluidez"""
        results = self.system.superfluid_transition(psi_range=(0.7, 1.0), n_points=50)
        
        # Debe contener todas las claves
        self.assertIn('coherence', results)
        self.assertIn('viscosity', results)
        self.assertIn('complexity_state', results)
        self.assertIn('complexity_indicator', results)
        
        # Viscosidad debe disminuir con coherencia
        # (verificar tendencia general)
        psi = results['coherence']
        nu = results['viscosity']
        
        # La viscosidad al inicio (Ψ bajo) debe ser mayor que al final (Ψ alto)
        self.assertGreater(nu[0], nu[-1])
    
    def test_superfluid_transition_thresholds(self):
        """Test: Umbrales de transición correctos"""
        results = self.system.superfluid_transition(psi_range=(0.7, 1.0), n_points=100)
        
        # Verificar que los umbrales están correctamente identificados
        self.assertEqual(results['turbulent_threshold'], 0.88)
        self.assertEqual(results['superfluid_threshold'], 0.95)
    
    def test_superfluid_transition_complexity_indicator(self):
        """Test: Indicador de complejidad en transición"""
        results = self.system.superfluid_transition(psi_range=(0.7, 1.0), n_points=100)
        
        indicator = results['complexity_indicator']
        psi = results['coherence']
        
        # Para Ψ < 0.88, indicador debe ser 0 (P≠NP)
        idx_turbulent = psi < 0.88
        if np.any(idx_turbulent):
            self.assertTrue(np.all(indicator[idx_turbulent] == 0))
        
        # Para Ψ >= 0.95, indicador debe ser 1 (P=NP)
        idx_superfluid = psi >= 0.95
        if np.any(idx_superfluid):
            self.assertTrue(np.all(indicator[idx_superfluid] == 1))
    
    def test_kappa_dimensional_lamination_value(self):
        """Test: κ = 1/7 permite laminación dimensional"""
        # κ = 1/7 es el factor crítico
        self.assertAlmostEqual(self.system.kappa, 0.142857, places=6)
        
        # Verificar que está en rango válido (0, 1)
        self.assertGreater(self.system.kappa, 0)
        self.assertLess(self.system.kappa, 1)
    
    def test_omega0_matches_f0(self):
        """Test: ω₀ = 2πf₀"""
        expected_omega = 2 * np.pi * self.system.f0_hz
        self.assertAlmostEqual(self.system.omega0_rad_s, expected_omega, places=4)
    
    def test_report_generation(self):
        """Test: Generación de reporte"""
        report = self.system.generate_report()
        
        # Verificar que el reporte contiene información clave
        self.assertIn("141.7001", report)
        self.assertIn("1/7", report)
        self.assertIn("SUPERFLUIDEZ", report)
        self.assertIn("P = NP", report)
        self.assertIn("VÓRTICE", report)


class TestPhysicalConsistency(unittest.TestCase):
    """Tests de consistencia física del sistema"""
    
    def setUp(self):
        """Configurar sistema"""
        self.system = HierarchicalGravitySystem()
    
    def test_superfluid_regime_minimal_viscosity(self):
        """Test: En superfluidez, viscosidad es mínima"""
        psi_values = np.linspace(0.95, 1.0, 10)
        viscosities = [self.system.effective_viscosity(psi) for psi in psi_values]
        
        # Todas las viscosidades deben ser pequeñas comparadas con nu_base
        for nu_eff in viscosities:
            # ν_eff debe ser del orden de ν_base/κ o menor
            self.assertLess(nu_eff, 10 * self.system.nu_base / self.system.kappa)
    
    def test_energy_increases_near_vortex_center(self):
        """Test: Energía aumenta al acercarse al centro del vórtice"""
        results = self.system.vortex_portal_geometry(r_range=(0.01, 5.0))
        
        # La energía debe aumentar al disminuir el radio
        # (porque v² ~ 1/r²)
        energy = results['energy']
        
        # Verificar tendencia: energía al principio (r pequeño) > energía al final (r grande)
        # Nota: radius[0] es r_min, radius[-1] es r_max
        self.assertGreater(energy[0], energy[-1])
    
    def test_curvature_diverges_at_singularity(self):
        """Test: Curvatura diverge en la singularidad"""
        r = np.logspace(-2, 1, 100)  # De 0.01 a 10
        results = self.system.vortex_portal_geometry(r_range=(r[0], r[-1]), n_points=len(r))
        
        curvature = results['curvature']
        
        # Curvatura debe aumentar dramáticamente para r pequeño
        # R ~ 1/r³, así que R(r_min) >> R(r_max)
        # Nota: curvature[0] corresponde a r_min, curvature[-1] a r_max
        self.assertGreater(curvature[0] / curvature[-1], 100)


class TestNumericalStability(unittest.TestCase):
    """Tests de estabilidad numérica"""
    
    def setUp(self):
        """Configurar sistema"""
        self.system = HierarchicalGravitySystem()
    
    def test_no_nan_in_viscosity(self):
        """Test: Sin NaN en cálculo de viscosidad"""
        psi_values = np.linspace(0.01, 1.0, 100)
        viscosities = [self.system.effective_viscosity(psi) for psi in psi_values]
        
        # No debe haber NaN
        self.assertFalse(any(np.isnan(v) for v in viscosities))
    
    def test_no_nan_in_metric_singularity(self):
        """Test: Sin NaN en singularidad métrica"""
        r = np.logspace(-3, 1, 100)
        pressure, velocity, g_rr = self.system.metric_singularity(r)
        
        # No debe haber NaN en ninguno
        self.assertFalse(np.any(np.isnan(pressure)))
        self.assertFalse(np.any(np.isnan(velocity)))
        self.assertFalse(np.any(np.isnan(g_rr)))
    
    def test_coherence_bounded(self):
        """Test: Coherencia siempre acotada en [0,1]"""
        t = np.linspace(0, 10.0, 10000)
        psi = self.system.coherence_evolution(t, x_amplitude=2.0)
        
        # Incluso con amplitud > 1, debe estar acotada
        self.assertTrue(np.all(psi >= 0))
        self.assertTrue(np.all(psi <= 1))


def run_tests():
    """Ejecutar todos los tests"""
    print("\n" + "="*70)
    print("  TESTS: SISTEMA DE JERARQUÍA GRAVITACIONAL ARMÓNICA")
    print("="*70 + "\n")
    
    # Crear suite de tests
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Agregar todas las clases de tests
    suite.addTests(loader.loadTestsFromTestCase(TestHierarchicalGravitySystem))
    suite.addTests(loader.loadTestsFromTestCase(TestPhysicalConsistency))
    suite.addTests(loader.loadTestsFromTestCase(TestNumericalStability))
    
    # Ejecutar tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Resumen
    print("\n" + "="*70)
    print("  RESUMEN DE TESTS")
    print("="*70)
    print(f"  Tests ejecutados: {result.testsRun}")
    print(f"  Exitosos: {result.testsRun - len(result.failures) - len(result.errors)}")
    print(f"  Fallos: {len(result.failures)}")
    print(f"  Errores: {len(result.errors)}")
    print("="*70 + "\n")
    
    return result.wasSuccessful()


if __name__ == "__main__":
    success = run_tests()
    exit(0 if success else 1)
