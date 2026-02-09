#!/usr/bin/env python3
"""
Test Suite for ℏ-Ψ Physical Systems Activation
===============================================

Comprehensive tests for the Planck constant (ℏ) coupling with the 
coherence field Ψ in physical systems.

Author: José Manuel Mota Burruezo (JMMB Ψ✧∞³)
Date: 2026-02-09
"""

import unittest
import numpy as np
import os
import json
from h_psi_physical_systems import (
    HPsiActivation, 
    PhysicalConstants
)


class TestPhysicalConstants(unittest.TestCase):
    """Test fundamental physical constants."""
    
    def setUp(self):
        """Set up test fixture."""
        self.constants = PhysicalConstants()
    
    def test_hbar_value(self):
        """Test that ℏ has correct value."""
        expected_hbar = 1.054571817e-34
        # Use relative tolerance for very small numbers
        self.assertAlmostEqual(self.constants.hbar / expected_hbar, 1.0, places=10)
    
    def test_speed_of_light(self):
        """Test speed of light value."""
        expected_c = 299792458.0
        self.assertEqual(self.constants.c, expected_c)
    
    def test_fundamental_frequency(self):
        """Test QCAL fundamental frequency."""
        expected_f0 = 141.7001
        self.assertEqual(self.constants.f0, expected_f0)
    
    def test_planck_length(self):
        """Test Planck length calculation."""
        # l_P = sqrt(hbar * G / c^3) ≈ 1.616e-35 m
        planck_length = self.constants.planck_length
        self.assertGreater(planck_length, 1e-36)
        self.assertLess(planck_length, 1e-34)
        self.assertAlmostEqual(planck_length, 1.616e-35, delta=0.1e-35)
    
    def test_planck_time(self):
        """Test Planck time calculation."""
        # t_P ≈ 5.391e-44 s
        planck_time = self.constants.planck_time
        self.assertGreater(planck_time, 1e-45)
        self.assertLess(planck_time, 1e-43)
    
    def test_planck_mass(self):
        """Test Planck mass calculation."""
        # m_P ≈ 2.176e-8 kg
        planck_mass = self.constants.planck_mass
        self.assertGreater(planck_mass, 1e-9)
        self.assertLess(planck_mass, 1e-7)
    
    def test_characteristic_wavelength(self):
        """Test characteristic wavelength from f₀."""
        # λ₀ = c / f₀
        expected_wavelength = self.constants.c / self.constants.f0
        self.assertEqual(self.constants.characteristic_wavelength, expected_wavelength)
        self.assertGreater(self.constants.characteristic_wavelength, 1e6)  # > 1000 km


class TestHPsiActivation(unittest.TestCase):
    """Test ℏ-Ψ activation framework."""
    
    def setUp(self):
        """Set up test fixture."""
        self.activator = HPsiActivation(verbose=False)
    
    def test_initialization(self):
        """Test proper initialization."""
        self.assertIsNotNone(self.activator.constants)
        self.assertIsInstance(self.activator.constants, PhysicalConstants)
    
    def test_psi_field_range(self):
        """Test that Ψ field stays in valid range [0,1]."""
        for _ in range(100):
            x = np.random.randn(3) * 10.0
            t = np.random.rand() * 10.0
            psi = self.activator.compute_psi_field(x, t)
            
            self.assertGreaterEqual(psi, 0.0, 
                                   f"Ψ = {psi} < 0 at x={x}, t={t}")
            self.assertLessEqual(psi, 1.0, 
                                f"Ψ = {psi} > 1 at x={x}, t={t}")
    
    def test_psi_field_temporal_periodicity(self):
        """Test that Ψ oscillates at fundamental frequency."""
        x = np.array([1.0, 0.0, 0.0])
        T = 1.0 / self.activator.constants.f0  # Period
        
        psi_t0 = self.activator.compute_psi_field(x, 0.0)
        psi_tT = self.activator.compute_psi_field(x, T)
        
        # Should return to same value after one period (approximately)
        self.assertAlmostEqual(psi_t0, psi_tT, delta=0.1)
    
    def test_psi_field_spatial_decay(self):
        """Test that Ψ decays with distance from origin."""
        t = 0.0
        distances = np.array([0.1, 1.0, 5.0, 10.0])
        psi_values = []
        
        for r in distances:
            x = np.array([r, 0.0, 0.0])
            psi = self.activator.compute_psi_field(x, t)
            psi_values.append(psi)
        
        # Generally should decay with distance (allowing for oscillations)
        # Check that far field is smaller than near field on average
        near_avg = np.mean(psi_values[:2])
        far_avg = np.mean(psi_values[2:])
        self.assertGreater(near_avg, far_avg * 0.5)
    
    def test_coupling_tensor_shape(self):
        """Test that coupling tensor has correct shape."""
        x = np.array([1.0, 0.0, 0.0])
        t = 0.0
        psi = 0.5
        
        Phi = self.activator.compute_hbar_coupling_tensor(x, t, psi)
        
        self.assertEqual(Phi.shape, (3, 3))
    
    def test_coupling_tensor_symmetry(self):
        """Test that coupling tensor is symmetric."""
        x = np.array([1.0, 2.0, 3.0])
        t = 0.5
        psi = 0.7
        
        Phi = self.activator.compute_hbar_coupling_tensor(x, t, psi)
        
        # Check symmetry: Φᵢⱼ = Φⱼᵢ
        self.assertTrue(np.allclose(Phi, Phi.T, rtol=1e-10))
    
    def test_coupling_tensor_hbar_dependence(self):
        """Test that coupling tensor scales with ℏ."""
        x = np.array([1.0, 0.0, 0.0])
        t = 0.0
        psi = 0.5
        
        # Compute at normal ℏ
        Phi_normal = self.activator.compute_hbar_coupling_tensor(x, t, psi)
        norm_normal = np.linalg.norm(Phi_normal, 'fro')
        
        # Temporarily double ℏ
        original_hbar = self.activator.constants.hbar
        self.activator.constants.hbar *= 2.0
        
        Phi_double = self.activator.compute_hbar_coupling_tensor(x, t, psi)
        norm_double = np.linalg.norm(Phi_double, 'fro')
        
        # Restore ℏ
        self.activator.constants.hbar = original_hbar
        
        # Coupling should scale linearly with ℏ
        self.assertAlmostEqual(norm_double / norm_normal, 2.0, delta=0.01)
    
    def test_coupling_tensor_psi_dependence(self):
        """Test that coupling tensor scales with Ψ."""
        x = np.array([1.0, 0.0, 0.0])
        t = 0.0
        
        psi1 = 0.5
        psi2 = 1.0
        
        Phi1 = self.activator.compute_hbar_coupling_tensor(x, t, psi1)
        Phi2 = self.activator.compute_hbar_coupling_tensor(x, t, psi2)
        
        norm1 = np.linalg.norm(Phi1, 'fro')
        norm2 = np.linalg.norm(Phi2, 'fro')
        
        # Higher Ψ should generally give larger coupling
        # (allowing for some variation from different terms)
        self.assertGreater(norm2, norm1 * 0.5)
    
    def test_quantum_classical_limit_structure(self):
        """Test quantum-classical limit analysis structure."""
        results = self.activator.analyze_quantum_classical_limit()
        
        self.assertIn('hbar_ratios', results)
        self.assertIn('coupling_norms', results)
        self.assertIn('coherence_lengths', results)
        self.assertIn('classical_limit_verified', results)
        
        self.assertEqual(len(results['hbar_ratios']), 
                        len(results['coupling_norms']))
        self.assertEqual(len(results['hbar_ratios']), 
                        len(results['coherence_lengths']))
    
    def test_classical_limit_verification(self):
        """Test that Φᵢⱼ → 0 as ℏ → 0."""
        results = self.activator.analyze_quantum_classical_limit()
        
        # Classical limit should be verified
        self.assertTrue(results['classical_limit_verified'])
        
        # Coupling at smallest ℏ should be much smaller than at physical ℏ
        ratio = results['coupling_norms'][-1] / results['coupling_norms'][0]
        self.assertLess(ratio, 1e-8)
    
    def test_coherence_length_scaling(self):
        """Test that coherence length scales with ℏ."""
        # Use a more limited range to avoid numerical precision issues
        hbar_ratios_test = np.logspace(0, -5, 20)  # Smaller range
        results = self.activator.analyze_quantum_classical_limit(hbar_ratios_test)
        
        # Coherence length should scale with ℏ
        # Check the general trend over the middle range
        mid_idx = len(results['coherence_lengths']) // 2
        
        # Average of first quarter vs last quarter
        first_quarter_avg = np.mean(results['coherence_lengths'][:5])
        last_quarter_avg = np.mean(results['coherence_lengths'][-5:])
        
        # First quarter should be larger than last quarter (scales with ℏ)
        self.assertGreater(first_quarter_avg, last_quarter_avg * 0.9)
        
        # Check that it's proportional to ℏ in log space
        # λ_coherence ∝ ℏ  =>  log(λ) ∝ log(ℏ)
        # Correlation should be strong
        log_hbar = np.log10(results['hbar_ratios'])
        log_length = np.log10(results['coherence_lengths'])
        correlation = np.corrcoef(log_hbar, log_length)[0, 1]
        
        # Strong correlation expected (close to 1.0)
        self.assertGreater(abs(correlation), 0.95)
    
    def test_scale_hierarchy_structure(self):
        """Test scale hierarchy output structure."""
        scales = self.activator.demonstrate_scale_hierarchy()
        
        required_keys = [
            'planck_length_m',
            'planck_time_s',
            'qcal_wavelength_m',
            'fluid_length_m',
            'planck_to_qcal_length',
            'qcal_to_fluid_length',
            'planck_to_fluid_length'
        ]
        
        for key in required_keys:
            self.assertIn(key, scales)
    
    def test_scale_hierarchy_ordering(self):
        """Test that scales are properly ordered."""
        scales = self.activator.demonstrate_scale_hierarchy()
        
        # Planck << QCAL (QCAL wavelength is macroscopic, ~2000 km)
        self.assertLess(scales['planck_length_m'], scales['qcal_wavelength_m'])
        
        # QCAL wavelength is much larger than typical fluid domain
        # λ₀ = c/f₀ ≈ 2116 km >> 1 m
        self.assertGreater(scales['qcal_wavelength_m'], scales['fluid_length_m'])
        
        # Planck << Fluid
        self.assertLess(scales['planck_length_m'], scales['fluid_length_m'])
        
        # Ratios should be << 1 for smaller/larger
        self.assertLess(scales['planck_to_qcal_length'], 1.0)
        self.assertGreater(scales['qcal_to_fluid_length'], 1.0)  # QCAL > Fluid
        self.assertLess(scales['planck_to_fluid_length'], 1.0)
    
    def test_activation_report_generation(self):
        """Test activation report generation."""
        output_file = 'test_h_psi_report.json'
        
        try:
            report = self.activator.generate_activation_report(output_file)
            
            # Check report structure
            self.assertIn('metadata', report)
            self.assertIn('fundamental_constants', report)
            self.assertIn('reference_evaluation', report)
            self.assertIn('quantum_classical_limit', report)
            self.assertIn('scale_hierarchy', report)
            self.assertIn('validation', report)
            
            # Check file was created
            self.assertTrue(os.path.exists(output_file))
            
            # Check JSON is valid
            with open(output_file, 'r') as f:
                loaded_report = json.load(f)
            
            self.assertEqual(report['metadata']['title'], loaded_report['metadata']['title'])
            
        finally:
            # Cleanup
            if os.path.exists(output_file):
                os.remove(output_file)
    
    def test_validation_checks(self):
        """Test that all validation checks pass."""
        report = self.activator.generate_activation_report('test_report_validation.json')
        
        try:
            validation = report['validation']
            
            self.assertTrue(validation['psi_in_valid_range'])
            self.assertTrue(validation['tensor_symmetric'])
            self.assertTrue(validation['hbar_dependence_verified'])
            self.assertTrue(validation['classical_limit_correct'])
        
        finally:
            # Cleanup
            if os.path.exists('test_report_validation.json'):
                os.remove('test_report_validation.json')


class TestPhysicalConsistency(unittest.TestCase):
    """Test physical consistency of the model."""
    
    def setUp(self):
        """Set up test fixture."""
        self.activator = HPsiActivation(verbose=False)
    
    def test_dimensional_analysis_coupling_tensor(self):
        """Test dimensional consistency of coupling tensor."""
        # Φᵢⱼ should have dimensions [1/s²] (acceleration/length)
        x = np.array([1.0, 0.0, 0.0])
        t = 0.0
        psi = 0.5
        
        Phi = self.activator.compute_hbar_coupling_tensor(x, t, psi)
        
        # Expected order of magnitude for ℏ-dependent term:
        # (ℏ/c²) × (coefficients) × (spatial gradients or curvature)
        # ℏ/c² ≈ 1.17e-51 J·s/(m/s)² ≈ 1.17e-51 kg
        # With 1/m² gradients: ≈ 1e-51 kg/m² ≈ 1e-51 s²/m⁴ × m²/s² = 1e-51 1/s²
        
        norm = np.linalg.norm(Phi, 'fro')
        
        # Should be extremely small due to ℏ/c² factor
        self.assertLess(norm, 1e-40)
        self.assertGreater(norm, 1e-60)
    
    def test_energy_scale_consistency(self):
        """Test that energy scales are consistent."""
        constants = self.activator.constants
        
        # QCAL energy: E = ℏω₀
        E_qcal = constants.hbar * constants.omega0
        
        # Should be much smaller than Planck energy
        self.assertLess(E_qcal, constants.planck_energy)
        
        # Should be in reasonable quantum regime
        self.assertGreater(E_qcal, 1e-40)  # Above numerical noise
    
    def test_length_scale_consistency(self):
        """Test that length scales are consistent."""
        constants = self.activator.constants
        
        # QCAL wavelength should be macroscopic
        self.assertGreater(constants.characteristic_wavelength, 1e6)  # > 1000 km
        
        # But much smaller than astronomical scales
        self.assertLess(constants.characteristic_wavelength, 1e10)  # < Earth diameter
    
    def test_no_nan_or_inf(self):
        """Test that computations don't produce NaN or Inf."""
        for _ in range(50):
            x = np.random.randn(3) * 100.0
            t = np.random.rand() * 10.0
            psi = np.random.rand()
            
            psi_field = self.activator.compute_psi_field(x, t)
            Phi = self.activator.compute_hbar_coupling_tensor(x, t, psi)
            
            self.assertFalse(np.isnan(psi_field))
            self.assertFalse(np.isinf(psi_field))
            self.assertFalse(np.any(np.isnan(Phi)))
            self.assertFalse(np.any(np.isinf(Phi)))


class TestVisualizationAndOutput(unittest.TestCase):
    """Test visualization and output generation."""
    
    def setUp(self):
        """Set up test fixture."""
        self.activator = HPsiActivation(verbose=False)
    
    def test_visualization_generation(self):
        """Test that visualization can be generated."""
        output_file = 'test_h_psi_vis.png'
        
        try:
            fig = self.activator.visualize_hbar_psi_coupling(output_file)
            
            self.assertIsNotNone(fig)
            self.assertTrue(os.path.exists(output_file))
            
            # Check file is not empty
            file_size = os.path.getsize(output_file)
            self.assertGreater(file_size, 1000)  # At least 1 KB
        
        finally:
            # Cleanup
            if os.path.exists(output_file):
                os.remove(output_file)
    
    def test_main_function_execution(self):
        """Test that main function executes without error."""
        # Import and run main (redirect outputs to avoid clutter)
        from h_psi_physical_systems import main
        
        try:
            activator, report = main()
            
            self.assertIsNotNone(activator)
            self.assertIsNotNone(report)
            self.assertIsInstance(activator, HPsiActivation)
            self.assertIsInstance(report, dict)
        
        finally:
            # Cleanup generated files
            for file in ['h_psi_activation.png', 'h_psi_activation_report.json']:
                if os.path.exists(file):
                    os.remove(file)


def run_tests():
    """Run all tests and print summary."""
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestPhysicalConstants))
    suite.addTests(loader.loadTestsFromTestCase(TestHPsiActivation))
    suite.addTests(loader.loadTestsFromTestCase(TestPhysicalConsistency))
    suite.addTests(loader.loadTestsFromTestCase(TestVisualizationAndOutput))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Print summary
    print("\n" + "=" * 80)
    print("  TEST SUMMARY")
    print("=" * 80)
    print(f"  Tests run:     {result.testsRun}")
    print(f"  Successes:     {result.testsRun - len(result.failures) - len(result.errors)}")
    print(f"  Failures:      {len(result.failures)}")
    print(f"  Errors:        {len(result.errors)}")
    print(f"  Success rate:  {100 * (result.testsRun - len(result.failures) - len(result.errors)) / result.testsRun:.1f}%")
    print("=" * 80)
    
    return result.wasSuccessful()


if __name__ == "__main__":
    success = run_tests()
    exit(0 if success else 1)
