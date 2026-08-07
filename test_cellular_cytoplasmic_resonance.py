#!/usr/bin/env python3
"""
Test Suite for Cellular Cytoplasmic Resonance and Molecular Protocol
=====================================================================

Comprehensive tests for:
- cellular_cytoplasmic_resonance.py
- molecular_implementation_protocol.py

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
Date: 31 de enero de 2026
License: MIT
"""

import unittest
import numpy as np
import sys

# Import modules to test
from cellular_cytoplasmic_resonance import (
    CellularConstants,
    CoherenceLength,
    HarmonicSpectrum,
    HermitianFlowOperator,
    CytoplasmicFlowCell,
    RiemannBiologicalVerification,
    CellularResonanceState,
    compute_coherence_length_table,
)

from molecular_implementation_protocol import (
    FluorescentMarker,
    PhaseInterferenceMeasurement,
    SpectralValidator,
    ExperimentalProtocol,
    MarkerType,
    CellularStructure,
    create_standard_protocol,
)


class TestCellularConstants(unittest.TestCase):
    """Test cellular constants"""
    
    def test_constants_initialization(self):
        """Test that constants are properly initialized"""
        const = CellularConstants()
        
        self.assertEqual(const.F0_CARDIAC_HZ, 141.7001)
        self.assertEqual(const.VISCOSITY_M2_S, 1.0e-9)  # Corrected value
        self.assertEqual(const.KAPPA_PI, 2.5773)
        self.assertEqual(const.CELL_LENGTH_SCALE_M, 1e-6)


class TestCoherenceLength(unittest.TestCase):
    """Test coherence length calculations"""
    
    def test_coherence_length_calculation(self):
        """Test coherence length ξ = √(ν/ω)"""
        # Use cardiac frequency with corrected viscosity
        coh = CoherenceLength(
            viscosity_m2_s=1.0e-9,  # Corrected viscosity
            frequency_hz=141.7001
        )
        
        # Should be approximately 1.06 μm
        self.assertAlmostEqual(coh.xi_um, 1.06, places=1)
    
    def test_cellular_scale_matching(self):
        """Test that coherence length matches cellular scale"""
        coh = CoherenceLength(
            viscosity_m2_s=1.0e-9,  # Corrected viscosity
            frequency_hz=141.7001
        )
        
        # Should match 1 μm cell scale
        matches = coh.matches_cellular_scale(cell_size_m=1e-6, tolerance=0.2)
        self.assertTrue(matches)
    
    def test_omega_conversion(self):
        """Test angular frequency conversion"""
        coh = CoherenceLength(
            viscosity_m2_s=1e-6,
            frequency_hz=1.0
        )
        
        expected_omega = 2 * np.pi
        self.assertAlmostEqual(coh.omega_rad_s, expected_omega, places=5)


class TestHarmonicSpectrum(unittest.TestCase):
    """Test harmonic spectrum"""
    
    def test_harmonic_generation(self):
        """Test generation of harmonic frequencies"""
        spectrum = HarmonicSpectrum(f0_hz=141.7001, max_harmonic=5)
        
        harmonics = spectrum.harmonics_hz
        
        # Check length
        self.assertEqual(len(harmonics), 5)
        
        # Check values
        self.assertAlmostEqual(harmonics[0], 141.7001, places=3)
        self.assertAlmostEqual(harmonics[1], 283.4002, places=3)
        self.assertAlmostEqual(harmonics[2], 425.1003, places=3)
    
    def test_temporal_scales(self):
        """Test temporal scales τₙ = 1/fₙ"""
        spectrum = HarmonicSpectrum(f0_hz=100.0, max_harmonic=3)
        
        temporal_scales = spectrum.temporal_scales_s
        
        # τ₁ = 1/100 = 0.01 s
        self.assertAlmostEqual(temporal_scales[0], 0.01, places=5)
        # τ₂ = 1/200 = 0.005 s
        self.assertAlmostEqual(temporal_scales[1], 0.005, places=5)
    
    def test_get_harmonic(self):
        """Test getting specific harmonic"""
        spectrum = HarmonicSpectrum(f0_hz=141.7001)
        
        # 3rd harmonic
        f3 = spectrum.get_harmonic(3)
        self.assertAlmostEqual(f3, 3 * 141.7001, places=3)


class TestHermitianFlowOperator(unittest.TestCase):
    """Test Hermitian flow operator"""
    
    def test_healthy_operator_is_hermitian(self):
        """Test that healthy operator is hermitian"""
        op = HermitianFlowOperator(dimension=3)
        H = op.construct_healthy_operator(frequency_hz=141.7)
        
        # Check hermitian property: H = H^T for real symmetric
        np.testing.assert_array_almost_equal(H, H.T)
        
        # Eigenvalues should be real
        self.assertFalse(op.has_complex_eigenvalues())
        
        # State should be coherent
        self.assertEqual(op.get_state(), CellularResonanceState.COHERENT)
    
    def test_cancer_operator_breaks_symmetry(self):
        """Test that cancer operator breaks hermitian symmetry"""
        op = HermitianFlowOperator(dimension=3)
        H = op.construct_cancer_operator(frequency_hz=141.7, symmetry_breaking=0.5)
        
        # Should have complex eigenvalues
        self.assertTrue(op.has_complex_eigenvalues())
        
        # State should be broken
        self.assertEqual(op.get_state(), CellularResonanceState.SYMMETRY_BROKEN)
    
    def test_eigenvalue_reality(self):
        """Test eigenvalue properties"""
        op = HermitianFlowOperator(dimension=3)
        
        # Healthy: real eigenvalues
        H_healthy = op.construct_healthy_operator(frequency_hz=141.7)
        eigs_healthy = op.eigenvalues
        
        # All imaginary parts should be near zero
        for eig in eigs_healthy:
            self.assertAlmostEqual(np.imag(eig), 0.0, places=8)


class TestCytoplasmicFlowCell(unittest.TestCase):
    """Test cytoplasmic flow cell model"""
    
    def test_cell_initialization(self):
        """Test cell initialization"""
        cell = CytoplasmicFlowCell(cell_id="Test-001")
        
        self.assertEqual(cell.cell_id, "Test-001")
        self.assertEqual(cell.state, CellularResonanceState.COHERENT)
        self.assertEqual(cell.phase_coherence, 1.0)
    
    def test_coherence_length_computation(self):
        """Test coherence length computation for cell"""
        cell = CytoplasmicFlowCell()
        coh = cell.compute_coherence_length()
        
        # Should be around 1 μm
        self.assertGreater(coh.xi_um, 0.5)
        self.assertLess(coh.xi_um, 2.0)
    
    def test_critical_damping_verification(self):
        """Test critical damping verification"""
        cell = CytoplasmicFlowCell()
        result = cell.verify_critical_damping()
        
        self.assertIn('coherence_length_um', result)
        self.assertIn('critically_damped', result)
        
        # Should be critically damped at cardiac frequency
        self.assertTrue(result['critically_damped'])
    
    def test_healthy_to_cancer_transition(self):
        """Test transition from healthy to cancer state"""
        cell = CytoplasmicFlowCell()
        
        # Initially healthy
        cell.set_healthy_state()
        self.assertEqual(cell.state, CellularResonanceState.COHERENT)
        self.assertEqual(cell.phase_coherence, 1.0)
        
        # Induce cancer
        cell.induce_cancer_state(symmetry_breaking=0.5)
        self.assertEqual(cell.state, CellularResonanceState.SYMMETRY_BROKEN)
        self.assertLess(cell.phase_coherence, 1.0)
    
    def test_harmonic_spectrum_generation(self):
        """Test harmonic spectrum generation for cell"""
        cell = CytoplasmicFlowCell()
        spectrum = cell.get_harmonic_spectrum(max_harmonic=5)
        
        self.assertEqual(len(spectrum.harmonics_hz), 5)
        self.assertAlmostEqual(spectrum.f0_hz, 141.7001, places=3)


class TestRiemannBiologicalVerification(unittest.TestCase):
    """Test Riemann biological verification framework"""
    
    def test_cell_population_creation(self):
        """Test creation of cell population"""
        verifier = RiemannBiologicalVerification()
        cells = verifier.create_cell_population(n_cells=50)
        
        self.assertEqual(len(cells), 50)
        self.assertEqual(len(verifier.cells), 50)
        
        # All should be healthy initially
        for cell in cells:
            self.assertEqual(cell.state, CellularResonanceState.COHERENT)
    
    def test_phase_coherence_measurement(self):
        """Test phase coherence measurement"""
        verifier = RiemannBiologicalVerification()
        cells = verifier.create_cell_population(n_cells=10)
        
        # All healthy -> should have high coherence
        coherence = verifier.measure_phase_coherence()
        self.assertEqual(coherence, 1.0)
        
        # Make some cells cancerous
        cells[0].induce_cancer_state(symmetry_breaking=0.5)
        cells[1].induce_cancer_state(symmetry_breaking=0.7)
        
        # Coherence should decrease
        coherence_mixed = verifier.measure_phase_coherence()
        self.assertLess(coherence_mixed, 1.0)
    
    def test_harmonic_peak_verification(self):
        """Test verification of harmonic peaks"""
        verifier = RiemannBiologicalVerification()
        
        # Generate signal with harmonics
        t = np.linspace(0, 1.0, 10000)
        signal = np.sin(2 * np.pi * 141.7 * t) + 0.5 * np.sin(2 * np.pi * 283.4 * t)
        
        sampling_rate = 10000  # Hz
        
        results = verifier.verify_harmonic_peaks(
            signal, sampling_rate, expected_harmonics=2
        )
        
        self.assertIn('peaks', results)
        self.assertIn('verification_score', results)
        
        # Should find at least the first harmonic
        self.assertGreater(results['verification_score'], 0.0)


class TestFluorescentMarker(unittest.TestCase):
    """Test fluorescent marker"""
    
    def test_marker_creation(self):
        """Test marker creation"""
        marker = FluorescentMarker(
            name="Test-Marker",
            marker_type=MarkerType.MAGNETIC_NANOPARTICLE,
            target_structure=CellularStructure.CYTOPLASM,
            excitation_wavelength_nm=488,
            emission_wavelength_nm=520,
            em_sensitive=True,
            resonance_frequency_hz=141.7,
            sensitivity_bandwidth_hz=20.0
        )
        
        self.assertEqual(marker.name, "Test-Marker")
        self.assertTrue(marker.em_sensitive)
    
    def test_frequency_sensitivity(self):
        """Test frequency sensitivity check"""
        marker = FluorescentMarker(
            name="Test",
            marker_type=MarkerType.MAGNETIC_NANOPARTICLE,
            target_structure=CellularStructure.CYTOPLASM,
            excitation_wavelength_nm=488,
            emission_wavelength_nm=520,
            em_sensitive=True,
            resonance_frequency_hz=141.7,
            sensitivity_bandwidth_hz=20.0
        )
        
        # Should be sensitive at resonance
        self.assertTrue(marker.is_sensitive_at_frequency(141.7))
        
        # Should be sensitive within bandwidth
        self.assertTrue(marker.is_sensitive_at_frequency(145.0))
        
        # Should not be sensitive far from resonance
        self.assertFalse(marker.is_sensitive_at_frequency(200.0))


class TestPhaseInterferenceMeasurement(unittest.TestCase):
    """Test phase interference measurement"""
    
    def test_measurement_creation(self):
        """Test measurement creation"""
        measurement = PhaseInterferenceMeasurement(
            cell_id="Cell-001",
            cardiac_phase_rad=0.0,
            cytoplasm_phase_rad=0.1
        )
        
        self.assertEqual(measurement.cell_id, "Cell-001")
        self.assertAlmostEqual(measurement.phase_difference_rad, 0.1)
    
    def test_phase_coherence_calculation(self):
        """Test phase coherence calculation"""
        # Perfect phase lock (Δφ = 0)
        m1 = PhaseInterferenceMeasurement(
            cell_id="C1", cardiac_phase_rad=0.0, cytoplasm_phase_rad=0.0
        )
        self.assertAlmostEqual(m1.phase_coherence, 1.0)
        
        # Opposite phase (Δφ = π)
        m2 = PhaseInterferenceMeasurement(
            cell_id="C2", cardiac_phase_rad=0.0, cytoplasm_phase_rad=np.pi
        )
        self.assertAlmostEqual(m2.phase_coherence, 1.0)  # cos²(π) = 1
    
    def test_phase_lock_detection(self):
        """Test phase lock detection"""
        # Phase-locked (small difference)
        m1 = PhaseInterferenceMeasurement(
            cell_id="C1", cardiac_phase_rad=0.0, cytoplasm_phase_rad=0.1
        )
        self.assertTrue(m1.is_phase_locked(tolerance_deg=30.0))
        
        # Not phase-locked (large difference)
        m2 = PhaseInterferenceMeasurement(
            cell_id="C2", cardiac_phase_rad=0.0, cytoplasm_phase_rad=np.pi/2
        )
        self.assertFalse(m2.is_phase_locked(tolerance_deg=30.0))


class TestSpectralValidator(unittest.TestCase):
    """Test spectral validator"""
    
    def test_validator_creation(self):
        """Test validator creation"""
        validator = SpectralValidator(fundamental_hz=141.7001)
        self.assertEqual(validator.f0_hz, 141.7001)
    
    def test_expected_spectrum_generation(self):
        """Test expected spectrum generation"""
        validator = SpectralValidator(fundamental_hz=100.0)
        expected = validator.generate_expected_spectrum(max_harmonic=3)
        
        np.testing.assert_array_almost_equal(expected, [100.0, 200.0, 300.0])
    
    def test_spectrum_validation(self):
        """Test spectrum validation"""
        validator = SpectralValidator(fundamental_hz=100.0)
        
        # Create mock measured spectrum with harmonics
        measured_freqs = np.linspace(0, 500, 1000)
        measured_powers = np.zeros_like(measured_freqs)
        
        # Add peaks at harmonics
        for n in [1, 2, 3]:
            f_harmonic = n * 100.0
            idx = np.argmin(np.abs(measured_freqs - f_harmonic))
            measured_powers[idx] = 1.0
        
        results = validator.validate_spectrum(
            measured_freqs, measured_powers, max_harmonic=3
        )
        
        self.assertEqual(results['harmonics_found'], 3)
        self.assertEqual(results['harmonics_expected'], 3)
        self.assertEqual(results['validation_score'], 1.0)
        self.assertTrue(results['validated'])


class TestExperimentalProtocol(unittest.TestCase):
    """Test experimental protocol"""
    
    def test_protocol_creation(self):
        """Test protocol creation"""
        protocol = ExperimentalProtocol()
        self.assertEqual(len(protocol.markers), 0)
        self.assertEqual(len(protocol.measurements), 0)
    
    def test_marker_panel_design(self):
        """Test marker panel design"""
        protocol = ExperimentalProtocol()
        markers = protocol.design_marker_panel()
        
        # Should have multiple markers
        self.assertGreater(len(markers), 0)
        
        # Should target different structures
        targets = {m.target_structure for m in markers}
        self.assertGreater(len(targets), 1)
    
    def test_measurement_simulation(self):
        """Test measurement simulation"""
        protocol = ExperimentalProtocol()
        measurements = protocol.simulate_measurement(n_cells=20)
        
        self.assertEqual(len(measurements), 20)
        
        # All should have valid coherence
        for m in measurements:
            self.assertGreaterEqual(m.phase_coherence, 0.0)
            self.assertLessEqual(m.phase_coherence, 1.0)
    
    def test_population_coherence_analysis(self):
        """Test population coherence analysis"""
        protocol = ExperimentalProtocol()
        measurements = protocol.simulate_measurement(n_cells=50, phase_noise_std_rad=0.2)
        
        analysis = protocol.analyze_population_coherence()
        
        self.assertEqual(analysis['n_cells'], 50)
        self.assertGreaterEqual(analysis['mean_coherence'], 0.0)
        self.assertLessEqual(analysis['mean_coherence'], 1.0)
        self.assertGreaterEqual(analysis['fraction_phase_locked'], 0.0)
        self.assertLessEqual(analysis['fraction_phase_locked'], 1.0)
    
    def test_signal_generation(self):
        """Test test signal generation"""
        protocol = ExperimentalProtocol()
        t, signal = protocol.generate_test_signal(
            duration_s=0.1,
            harmonics=[1, 2, 3]
        )
        
        self.assertGreater(len(t), 0)
        self.assertEqual(len(t), len(signal))


class TestIntegration(unittest.TestCase):
    """Integration tests"""
    
    def test_full_workflow(self):
        """Test complete workflow from cells to validation"""
        # Create cell population
        verifier = RiemannBiologicalVerification()
        cells = verifier.create_cell_population(n_cells=30)
        
        # Make some cancerous
        for i in range(5):
            cells[i].induce_cancer_state(symmetry_breaking=0.5)
        
        # Measure coherence
        coherence = verifier.measure_phase_coherence()
        
        # Should be less than 1 due to cancer cells
        self.assertLess(coherence, 1.0)
        self.assertGreater(coherence, 0.5)  # But not too low
    
    def test_coherence_length_matches_theory(self):
        """Test that coherence length matches theoretical prediction"""
        result = compute_coherence_length_table()
        
        # Should find match at cardiac frequency
        for row in result['table']:
            if abs(row['frequency_hz'] - 141.7001) < 1.0:
                self.assertTrue(row['matches_cell_scale'])


def run_tests():
    """Run all tests"""
    print("="*80)
    print("Cellular Cytoplasmic Resonance - Test Suite")
    print("="*80)
    print()
    
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestCellularConstants))
    suite.addTests(loader.loadTestsFromTestCase(TestCoherenceLength))
    suite.addTests(loader.loadTestsFromTestCase(TestHarmonicSpectrum))
    suite.addTests(loader.loadTestsFromTestCase(TestHermitianFlowOperator))
    suite.addTests(loader.loadTestsFromTestCase(TestCytoplasmicFlowCell))
    suite.addTests(loader.loadTestsFromTestCase(TestRiemannBiologicalVerification))
    suite.addTests(loader.loadTestsFromTestCase(TestFluorescentMarker))
    suite.addTests(loader.loadTestsFromTestCase(TestPhaseInterferenceMeasurement))
    suite.addTests(loader.loadTestsFromTestCase(TestSpectralValidator))
    suite.addTests(loader.loadTestsFromTestCase(TestExperimentalProtocol))
    suite.addTests(loader.loadTestsFromTestCase(TestIntegration))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    print()
    print("="*80)
    print("Test Summary")
    print("="*80)
    print(f"Tests run: {result.testsRun}")
    print(f"Successes: {result.testsRun - len(result.failures) - len(result.errors)}")
    print(f"Failures: {len(result.failures)}")
    print(f"Errors: {len(result.errors)}")
    print("="*80)
    
    return result.wasSuccessful()


if __name__ == "__main__":
    success = run_tests()
    sys.exit(0 if success else 1)
