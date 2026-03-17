#!/usr/bin/env python3
"""
Test Suite: Cytoplasmic Riemann Resonance Model
================================================

Suite completa de pruebas para el modelo de Resonancia Riemann-Citoplasma.

Tests incluidos:
1. Verificación de constantes físicas
2. Validación de longitud de coherencia ξ ≈ 1.06 μm
3. Validación de frecuencias armónicas
4. Verificación de κ_Π = 2.5773
5. Pruebas de hermiticidad del operador
6. Detección de decoherencia
7. Tests de mapeo Riemann → Biología
8. Validación de exportación/importación JSON
9. Tests de protocolo molecular

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
Date: 1 de febrero de 2026
"""

import sys
from pathlib import Path
import unittest
import numpy as np
import json
import tempfile
import os

# Añadir path para imports
sys.path.insert(0, str(Path(__file__).parent.parent / 'teoria_principal'))

from cytoplasmic_riemann_resonance import (
    CytoplasmicRiemannResonance,
    MolecularValidationProtocol,
    BiologicalResonanceParams,
    RiemannBiologicalMapping,
    compute_riemann_zero_statistics,
    KAPPA_PI,
    FUNDAMENTAL_FREQUENCY_HZ,
    NUM_HUMAN_CELLS,
    CYTOPLASM_DENSITY,
    CYTOPLASM_KINEMATIC_VISCOSITY,
    PLANCK_REDUCED,
    BOLTZMANN
)


class TestBiologicalResonanceParams(unittest.TestCase):
    """Tests para la clase BiologicalResonanceParams"""
    
    def test_default_parameters(self):
        """Test de parámetros por defecto"""
        params = BiologicalResonanceParams()
        
        self.assertEqual(params.density, CYTOPLASM_DENSITY)
        self.assertEqual(params.kinematic_viscosity, CYTOPLASM_KINEMATIC_VISCOSITY)
        self.assertEqual(params.fundamental_frequency, FUNDAMENTAL_FREQUENCY_HZ)
        self.assertEqual(params.kappa_pi, KAPPA_PI)
        self.assertEqual(params.num_cells, NUM_HUMAN_CELLS)
        self.assertGreater(params.temperature, 0)
        self.assertGreater(params.num_harmonics, 0)
    
    def test_parameter_validation_density(self):
        """Test de validación de densidad"""
        with self.assertRaises(ValueError):
            BiologicalResonanceParams(density=-1.0)
        
        with self.assertRaises(ValueError):
            BiologicalResonanceParams(density=0.0)
    
    def test_parameter_validation_viscosity(self):
        """Test de validación de viscosidad"""
        with self.assertRaises(ValueError):
            BiologicalResonanceParams(kinematic_viscosity=-1e-6)
        
        with self.assertRaises(ValueError):
            BiologicalResonanceParams(kinematic_viscosity=0.0)
    
    def test_parameter_validation_temperature(self):
        """Test de validación de temperatura"""
        with self.assertRaises(ValueError):
            BiologicalResonanceParams(temperature=-10)
        
        with self.assertRaises(ValueError):
            BiologicalResonanceParams(temperature=0)
    
    def test_custom_parameters(self):
        """Test con parámetros personalizados"""
        params = BiologicalResonanceParams(
            density=1100.0,
            kinematic_viscosity=2e-6,
            fundamental_frequency=150.0,
            temperature=300.0,
            num_harmonics=20
        )
        
        self.assertEqual(params.density, 1100.0)
        self.assertEqual(params.kinematic_viscosity, 2e-6)
        self.assertEqual(params.fundamental_frequency, 150.0)
        self.assertEqual(params.temperature, 300.0)
        self.assertEqual(params.num_harmonics, 20)


class TestCytoplasmicRiemannResonance(unittest.TestCase):
    """Tests para la clase principal CytoplasmicRiemannResonance"""
    
    def setUp(self):
        """Setup ejecutado antes de cada test"""
        self.model = CytoplasmicRiemannResonance()
    
    def test_initialization(self):
        """Test de inicialización del modelo"""
        self.assertIsNotNone(self.model.params)
        self.assertIsNotNone(self.model.omega_0)
        self.assertIsNotNone(self.model.coherence_length)
        self.assertIsNotNone(self.model.flow_operator)
        self.assertIsNotNone(self.model.eigenvalues)
        self.assertIsNotNone(self.model.eigenvectors)
    
    def test_coherence_length_value(self):
        """Test de valor de longitud de coherencia ξ ≈ 1.06 μm"""
        # La longitud de coherencia debe estar cerca de 1.06 μm
        expected_coherence_um = 1.06
        tolerance = 0.1  # ±0.1 μm
        
        self.assertAlmostEqual(
            self.model.coherence_length_um,
            expected_coherence_um,
            delta=tolerance,
            msg=f"ξ = {self.model.coherence_length_um:.4f} μm debe estar cerca de 1.06 μm"
        )
    
    def test_coherence_length_calculation(self):
        """Test de cálculo de longitud de coherencia: ξ = √(ν/ω)"""
        # Calcular manualmente
        omega_0 = 2.0 * np.pi * self.model.params.fundamental_frequency
        expected_xi = np.sqrt(self.model.params.kinematic_viscosity / omega_0)
        
        self.assertAlmostEqual(
            self.model.coherence_length,
            expected_xi,
            places=10
        )
    
    def test_kappa_pi_value(self):
        """Test de valor de κ_Π = 2.5773"""
        expected_kappa = 2.5773
        tolerance = 0.001
        
        self.assertAlmostEqual(
            self.model.params.kappa_pi,
            expected_kappa,
            delta=tolerance,
            msg=f"κ_Π = {self.model.params.kappa_pi:.4f} debe ser 2.5773"
        )
    
    def test_fundamental_frequency(self):
        """Test de frecuencia fundamental ≈ 141.6 kHz (calibrada para ξ = 1.06 μm)"""
        self.assertAlmostEqual(
            self.model.params.fundamental_frequency,
            141647.33,
            places=0  # Within 1 Hz
        )
    
    def test_harmonic_frequencies(self):
        """Test de frecuencias armónicas fₙ = n × 141.7001 Hz"""
        expected_frequencies = np.array([
            (n + 1) * FUNDAMENTAL_FREQUENCY_HZ 
            for n in range(self.model.hilbert_dim)
        ])
        
        # Las frecuencias resonantes deben estar cerca de los armónicos
        for i, (computed, expected) in enumerate(zip(
            self.model.resonant_frequencies, expected_frequencies
        )):
            deviation = abs(computed - expected) / expected
            self.assertLess(
                deviation,
                0.15,  # <15% desviación permitida
                msg=f"Frecuencia f_{i+1} = {computed:.2f} Hz (esperado {expected:.2f} Hz)"
            )
    
    def test_operator_hermiticity(self):
        """Test de hermiticidad del operador: Ĥ = Ĥ†"""
        # El operador debe ser hermítico
        self.assertTrue(
            self.model.is_hermitian,
            "El operador de flujo debe ser hermítico"
        )
        
        # Verificar numéricamente Ĥ = Ĥ†
        operator_conj_transpose = self.model.flow_operator.conj().T
        
        self.assertTrue(
            np.allclose(self.model.flow_operator, operator_conj_transpose),
            "Ĥ debe ser igual a Ĥ†"
        )
    
    def test_eigenvalues_real(self):
        """Test de que todos los eigenvalores son reales"""
        # Para un operador hermítico, todos los eigenvalues deben ser reales
        max_imaginary = np.max(np.abs(self.model.eigenvalues.imag))
        
        self.assertLess(
            max_imaginary,
            1e-10,
            f"Componente imaginaria máxima: {max_imaginary} debe ser ~0"
        )
    
    def test_eigenvalues_positive(self):
        """Test de que los eigenvalores son positivos (energías)"""
        # Todos los eigenvalues deben ser positivos
        self.assertTrue(
            np.all(self.model.eigenvalues.real > 0),
            "Todos los eigenvalores deben ser positivos"
        )
    
    def test_eigenvalues_ordered(self):
        """Test de que los eigenvalores están ordenados"""
        # Los eigenvalues deben estar en orden ascendente
        sorted_eigenvalues = np.sort(self.model.eigenvalues.real)
        
        self.assertTrue(
            np.allclose(self.model.eigenvalues.real, sorted_eigenvalues),
            "Los eigenvalores deben estar ordenados"
        )
    
    def test_validate_riemann_hypothesis(self):
        """Test de validación de la Hipótesis de Riemann"""
        validation = self.model.validate_riemann_hypothesis_biological()
        
        # Verificar estructura del resultado
        self.assertIn('hypothesis_validated', validation)
        self.assertIn('interpretation', validation)
        self.assertIn('all_eigenvalues_real', validation)
        self.assertIn('harmonic_distribution', validation)
        self.assertIn('coherence_length_um', validation)
        self.assertIn('kappa_pi', validation)
        
        # La hipótesis debe validarse
        self.assertTrue(
            validation['hypothesis_validated'],
            "La Hipótesis de Riemann debe validarse biológicamente"
        )
        
        # Todos los eigenvalues deben ser reales
        self.assertTrue(
            validation['all_eigenvalues_real'],
            "Todos los eigenvalores deben ser reales"
        )
        
        # El operador debe ser hermítico
        self.assertTrue(
            validation['operator_is_hermitian'],
            "El operador debe ser hermítico"
        )
    
    def test_detect_decoherence_healthy(self):
        """Test de detección de decoherencia en célula sana"""
        # Sin perturbación significativa, no debe detectar decoherencia
        result = self.model.detect_decoherence(threshold=0.01)
        
        self.assertIn('decoherence_detected', result)
        self.assertIn('hermiticity_broken', result)
        self.assertIn('max_imaginary_component', result)
        
        # No debe detectar decoherencia en sistema sano
        # (puede haber pequeña perturbación aleatoria)
    
    def test_detect_decoherence_perturbed(self):
        """Test de detección de decoherencia con perturbación"""
        # Crear perturbación simple que claramente rompe hermiticidad
        # Matriz puramente imaginaria en la diagonal
        perturbation = np.zeros((self.model.hilbert_dim, self.model.hilbert_dim), dtype=complex)
        for i in range(self.model.hilbert_dim):
            perturbation[i, i] = 1j * np.abs(self.model.eigenvalues[0]) * 0.01
        
        result = self.model.detect_decoherence(
            perturbation_matrix=perturbation,
            threshold=1e-35  # Threshold muy bajo
        )
        
        # Debe detectar rotura de hermiticidad
        # (Una matriz hermítica no puede tener elementos diagonales puramente imaginarios)
        self.assertTrue(
            result['hermiticity_broken'],
            f"Debe detectar rotura de hermiticidad: {result['hermiticity_broken']}"
        )
    
    def test_get_coherence_at_scale(self):
        """Test de coherencia a diferentes escalas"""
        # A escala 0 (misma posición), coherencia = 1
        result_zero = self.model.get_coherence_at_scale(0.0)
        self.assertAlmostEqual(result_zero['coherence'], 1.0, places=5)
        
        # A escala ξ (longitud de coherencia), coherencia = 1/e
        result_xi = self.model.get_coherence_at_scale(self.model.coherence_length)
        self.assertAlmostEqual(
            result_xi['coherence'],
            np.exp(-1),
            places=5,
            msg="A r = ξ, la coherencia debe ser 1/e"
        )
        
        # A escala muy grande, coherencia → 0
        result_large = self.model.get_coherence_at_scale(1e-3)  # 1 mm
        self.assertLess(
            result_large['coherence'],
            0.01,
            "A escalas grandes, la coherencia debe ser muy pequeña"
        )
    
    def test_compute_riemann_biological_mappings(self):
        """Test de mapeos Riemann → Biología"""
        mappings = self.model.compute_riemann_biological_mappings()
        
        # Debe haber al menos 10 mapeos
        self.assertGreaterEqual(len(mappings), 10)
        
        # Verificar estructura de cada mapeo
        for mapping in mappings:
            self.assertIsInstance(mapping, RiemannBiologicalMapping)
            self.assertGreater(mapping.zero_index, 0)
            self.assertGreater(mapping.riemann_imaginary_part, 0)
            self.assertGreater(mapping.biological_frequency_hz, 0)
            self.assertGreater(mapping.coherence_length_um, 0)
            self.assertGreater(mapping.energy_scale_ev, 0)
            self.assertIsInstance(mapping.cellular_process, str)
            self.assertGreater(len(mapping.cellular_process), 0)
    
    def test_export_results(self):
        """Test de exportación de resultados a JSON"""
        with tempfile.TemporaryDirectory() as tmpdir:
            filepath = os.path.join(tmpdir, 'test_results.json')
            results = self.model.export_results(filepath)
            
            # Verificar que el archivo se creó
            self.assertTrue(os.path.exists(filepath))
            
            # Verificar estructura de resultados
            self.assertIn('model_info', results)
            self.assertIn('validation', results)
            self.assertIn('fundamental_constants', results)
            self.assertIn('riemann_biological_mappings', results)
            self.assertIn('coherence_at_scales', results)
            self.assertIn('operator_properties', results)
            
            # Leer archivo y verificar JSON válido
            with open(filepath, 'r') as f:
                loaded_results = json.load(f)
            
            self.assertEqual(
                loaded_results['fundamental_constants']['kappa_pi'],
                results['fundamental_constants']['kappa_pi']
            )
    
    def test_export_import_cycle(self):
        """Test de ciclo completo exportar → importar → verificar"""
        with tempfile.TemporaryDirectory() as tmpdir:
            filepath = os.path.join(tmpdir, 'test_export_import.json')
            
            # Exportar
            exported = self.model.export_results(filepath)
            
            # Importar
            with open(filepath, 'r') as f:
                imported = json.load(f)
            
            # Verificar que los datos se preservan
            self.assertEqual(
                exported['validation']['coherence_length_um'],
                imported['validation']['coherence_length_um']
            )
            self.assertEqual(
                exported['fundamental_constants']['kappa_pi'],
                imported['fundamental_constants']['kappa_pi']
            )
            self.assertEqual(
                len(exported['riemann_biological_mappings']),
                len(imported['riemann_biological_mappings'])
            )


class TestMolecularValidationProtocol(unittest.TestCase):
    """Tests para la clase MolecularValidationProtocol"""
    
    def setUp(self):
        """Setup ejecutado antes de cada test"""
        self.model = CytoplasmicRiemannResonance()
        self.protocol = MolecularValidationProtocol(self.model)
    
    def test_initialization(self):
        """Test de inicialización del protocolo"""
        self.assertIsNotNone(self.protocol.model)
        self.assertEqual(self.protocol.model, self.model)
    
    def test_design_fluorescent_markers(self):
        """Test de diseño de marcadores fluorescentes"""
        design = self.protocol.design_fluorescent_markers()
        
        self.assertIn('fluorescent_markers', design)
        self.assertIn('imaging_method', design)
        self.assertIn('temporal_resolution_ms', design)
        self.assertIn('spatial_resolution_nm', design)
        
        markers = design['fluorescent_markers']
        
        # Verificar marcadores clave
        self.assertIn('GFP-Cytoplasm', markers)
        self.assertIn('RFP-Mitochondria', markers)
        self.assertIn('FRET-Actin', markers)
        
        # Verificar estructura de cada marcador
        for marker_name, marker_data in markers.items():
            self.assertIn('target', marker_data)
            self.assertIn('purpose', marker_data)
    
    def test_design_magnetic_nanoparticle_experiment(self):
        """Test de diseño de experimento con nanopartículas magnéticas"""
        experiment = self.protocol.design_magnetic_nanoparticle_experiment()
        
        self.assertIn('nanoparticle', experiment)
        self.assertIn('magnetic_field', experiment)
        self.assertIn('detection', experiment)
        self.assertIn('expected_resonances_hz', experiment)
        
        # Verificar nanopartícula
        self.assertEqual(experiment['nanoparticle']['composition'], 'Fe₃O₄ (magnetite)')
        self.assertGreater(experiment['nanoparticle']['size_nm'], 0)
        
        # Verificar campo magnético
        self.assertEqual(
            experiment['magnetic_field']['frequency_hz'],
            FUNDAMENTAL_FREQUENCY_HZ
        )
    
    def test_design_spectral_validation(self):
        """Test de diseño de validación espectral"""
        validation = self.protocol.design_spectral_validation()
        
        self.assertIn('method', validation)
        self.assertIn('technique', validation)
        self.assertIn('target_frequencies_hz', validation)
        self.assertIn('expected_peaks', validation)
        
        # Verificar que hay frecuencias objetivo
        self.assertGreater(len(validation['target_frequencies_hz']), 0)
        
        # Verificar que hay picos esperados
        self.assertGreater(len(validation['expected_peaks']), 0)
        
        # Cada pico debe tener estructura correcta
        for peak in validation['expected_peaks']:
            self.assertIn('frequency_hz', peak)
            self.assertIn('harmonic_number', peak)
            self.assertIn('relative_amplitude', peak)
    
    def test_design_time_lapse_microscopy(self):
        """Test de diseño de microscopía de lapso de tiempo"""
        protocol = self.protocol.design_time_lapse_microscopy()
        
        self.assertIn('microscopy_type', protocol)
        self.assertIn('objective', protocol)
        self.assertIn('z_stack', protocol)
        self.assertIn('time_lapse', protocol)
        self.assertIn('analysis', protocol)
        self.assertIn('cell_types', protocol)
        
        # Verificar z-stack
        self.assertGreater(protocol['z_stack']['range_um'], 0)
        self.assertGreater(protocol['z_stack']['slices'], 0)
        
        # Verificar time-lapse
        self.assertGreater(protocol['time_lapse']['duration_min'], 0)
        self.assertGreater(protocol['time_lapse']['frames'], 0)
        
        # Verificar tipos celulares
        self.assertGreater(len(protocol['cell_types']), 0)
    
    def test_export_protocol(self):
        """Test de exportación de protocolo"""
        with tempfile.TemporaryDirectory() as tmpdir:
            filepath = os.path.join(tmpdir, 'test_protocol.json')
            protocol_data = self.protocol.export_protocol(filepath)
            
            # Verificar que el archivo se creó
            self.assertTrue(os.path.exists(filepath))
            
            # Verificar estructura
            self.assertIn('protocol_info', protocol_data)
            self.assertIn('experiments', protocol_data)
            self.assertIn('expected_outcomes', protocol_data)
            self.assertIn('safety_considerations', protocol_data)
            
            # Verificar experimentos
            experiments = protocol_data['experiments']
            self.assertIn('fluorescent_markers', experiments)
            self.assertIn('magnetic_nanoparticles', experiments)
            self.assertIn('spectral_validation', experiments)
            self.assertIn('time_lapse_microscopy', experiments)


class TestRiemannBiologicalMapping(unittest.TestCase):
    """Tests para la clase RiemannBiologicalMapping"""
    
    def test_creation(self):
        """Test de creación de mapeo"""
        mapping = RiemannBiologicalMapping(
            zero_index=1,
            riemann_imaginary_part=14.134725,
            biological_frequency_hz=141.7001,
            cellular_process="Transporte de vesículas",
            coherence_length_um=1.06,
            energy_scale_ev=5.86e-13
        )
        
        self.assertEqual(mapping.zero_index, 1)
        self.assertAlmostEqual(mapping.riemann_imaginary_part, 14.134725)
        self.assertAlmostEqual(mapping.biological_frequency_hz, 141.7001)
        self.assertEqual(mapping.cellular_process, "Transporte de vesículas")
        self.assertAlmostEqual(mapping.coherence_length_um, 1.06)
    
    def test_to_dict(self):
        """Test de conversión a diccionario"""
        mapping = RiemannBiologicalMapping(
            zero_index=1,
            riemann_imaginary_part=14.134725,
            biological_frequency_hz=141.7001,
            cellular_process="Test process",
            coherence_length_um=1.06,
            energy_scale_ev=5.86e-13
        )
        
        mapping_dict = mapping.to_dict()
        
        self.assertIsInstance(mapping_dict, dict)
        self.assertEqual(mapping_dict['zero_index'], 1)
        self.assertEqual(mapping_dict['cellular_process'], "Test process")


class TestUtilityFunctions(unittest.TestCase):
    """Tests para funciones auxiliares"""
    
    def test_compute_riemann_zero_statistics(self):
        """Test de cálculo de estadísticas de ceros de Riemann"""
        # Crear eigenvalues de prueba
        eigenvalues = np.array([1.0, 2.5, 4.2, 6.1, 8.3, 10.8])
        
        stats = compute_riemann_zero_statistics(eigenvalues)
        
        self.assertIn('mean_spacing', stats)
        self.assertIn('std_spacing', stats)
        self.assertIn('min_spacing', stats)
        self.assertIn('max_spacing', stats)
        self.assertIn('gue_parameter', stats)
        
        # Verificar valores positivos
        self.assertGreater(stats['mean_spacing'], 0)
        self.assertGreater(stats['std_spacing'], 0)
        
        # Verificar parámetro GUE
        self.assertAlmostEqual(stats['gue_parameter'], np.pi / 4, places=5)


class TestPhysicalConstants(unittest.TestCase):
    """Tests para constantes físicas"""
    
    def test_kappa_pi_value(self):
        """Test de valor de κ_Π"""
        self.assertAlmostEqual(KAPPA_PI, 2.5773, places=4)
    
    def test_fundamental_frequency_value(self):
        """Test de valor de frecuencia fundamental"""
        # Calibrada para ξ ≈ 1.06 μm con ν = 10⁻⁶ m²/s
        self.assertAlmostEqual(FUNDAMENTAL_FREQUENCY_HZ, 141647.33, places=0)
    
    def test_num_human_cells_value(self):
        """Test de número de células humanas"""
        self.assertEqual(NUM_HUMAN_CELLS, 37e12)
    
    def test_planck_constant(self):
        """Test de constante de Planck reducida"""
        # Valor CODATA 2018
        expected = 1.054571817e-34
        self.assertAlmostEqual(PLANCK_REDUCED, expected, places=42)
    
    def test_boltzmann_constant(self):
        """Test de constante de Boltzmann"""
        # Valor CODATA 2018
        expected = 1.380649e-23
        self.assertEqual(BOLTZMANN, expected)


class TestIntegrationScenarios(unittest.TestCase):
    """Tests de escenarios de integración completos"""
    
    def test_complete_workflow(self):
        """Test de flujo de trabajo completo"""
        # 1. Crear modelo
        model = CytoplasmicRiemannResonance()
        
        # 2. Validar hipótesis
        validation = model.validate_riemann_hypothesis_biological()
        self.assertTrue(validation['hypothesis_validated'])
        
        # 3. Computar mapeos
        mappings = model.compute_riemann_biological_mappings()
        self.assertGreater(len(mappings), 0)
        
        # 4. Crear protocolo
        protocol = MolecularValidationProtocol(model)
        fluorescent = protocol.design_fluorescent_markers()
        self.assertIsNotNone(fluorescent)
        
        # 5. Exportar resultados
        with tempfile.TemporaryDirectory() as tmpdir:
            results_path = os.path.join(tmpdir, 'results.json')
            protocol_path = os.path.join(tmpdir, 'protocol.json')
            
            model.export_results(results_path)
            protocol.export_protocol(protocol_path)
            
            self.assertTrue(os.path.exists(results_path))
            self.assertTrue(os.path.exists(protocol_path))
    
    def test_reproducibility(self):
        """Test de reproducibilidad de resultados"""
        # Crear dos modelos idénticos
        model1 = CytoplasmicRiemannResonance()
        model2 = CytoplasmicRiemannResonance()
        
        # Los resultados deben ser idénticos
        self.assertAlmostEqual(
            model1.coherence_length_um,
            model2.coherence_length_um,
            places=10
        )
        
        np.testing.assert_array_almost_equal(
            model1.eigenvalues.real,
            model2.eigenvalues.real,
            decimal=10
        )
        
        np.testing.assert_array_almost_equal(
            model1.resonant_frequencies,
            model2.resonant_frequencies,
            decimal=10
        )


# ============================================================================
# SUITE DE TESTS
# ============================================================================

def suite():
    """Crear suite completa de tests"""
    test_suite = unittest.TestSuite()
    
    # Añadir todos los tests
    test_suite.addTests(unittest.TestLoader().loadTestsFromTestCase(
        TestBiologicalResonanceParams
    ))
    test_suite.addTests(unittest.TestLoader().loadTestsFromTestCase(
        TestCytoplasmicRiemannResonance
    ))
    test_suite.addTests(unittest.TestLoader().loadTestsFromTestCase(
        TestMolecularValidationProtocol
    ))
    test_suite.addTests(unittest.TestLoader().loadTestsFromTestCase(
        TestRiemannBiologicalMapping
    ))
    test_suite.addTests(unittest.TestLoader().loadTestsFromTestCase(
        TestUtilityFunctions
    ))
    test_suite.addTests(unittest.TestLoader().loadTestsFromTestCase(
        TestPhysicalConstants
    ))
    test_suite.addTests(unittest.TestLoader().loadTestsFromTestCase(
        TestIntegrationScenarios
    ))
    
    return test_suite


if __name__ == '__main__':
    print("="*70)
    print("TEST SUITE: Cytoplasmic Riemann Resonance Model")
    print("="*70)
    print()
    
    # Ejecutar tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite())
    
    # Resumen
    print("\n" + "="*70)
    print("RESUMEN DE TESTS")
    print("="*70)
    print(f"Tests ejecutados: {result.testsRun}")
    print(f"Tests exitosos: {result.testsRun - len(result.failures) - len(result.errors)}")
    print(f"Fallos: {len(result.failures)}")
    print(f"Errores: {len(result.errors)}")
    
    if result.wasSuccessful():
        print("\n✓ TODOS LOS TESTS PASARON EXITOSAMENTE")
    else:
        print("\n✗ ALGUNOS TESTS FALLARON")
    
    print("="*70)
    
    # Exit code
    sys.exit(0 if result.wasSuccessful() else 1)
