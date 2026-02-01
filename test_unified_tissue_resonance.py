#!/usr/bin/env python3
"""
Tests for Unified Tissue Resonance Model
=========================================

Tests the integration of:
1. Hilbert-Pólya operator
2. Navier-Stokes biofluid coupling
3. Magicicada scaling law
4. INGΝIO CMI & AURON systems

Author: José Manuel Mota Burruezo
Date: 31 de enero de 2026
License: MIT
"""

import unittest
import numpy as np
from hilbert_polya_operator import (
    HilbertPolyaOperator,
    HilbertPolyaParameters,
    get_riemann_zeros,
    map_to_biological_frequencies
)
from unified_tissue_resonance import (
    UnifiedTissueResonance,
    TissueType,
    TISSUE_PARAMETERS
)
from ingnio_auron_system import (
    INGNIOCMISystem,
    AURONProtectionSystem,
    ResonanceTherapySystem
)


class TestHilbertPolyaOperator(unittest.TestCase):
    """Test Hilbert-Pólya operator functionality"""
    
    def setUp(self):
        """Set up test fixtures"""
        self.operator = HilbertPolyaOperator()
        self.phi = (1 + np.sqrt(5)) / 2
    
    def test_riemann_zeros_available(self):
        """Test that Riemann zeros are available"""
        zeros = get_riemann_zeros(10)
        self.assertEqual(len(zeros), 10)
        self.assertGreater(zeros[0], 0)
        self.assertTrue(np.all(np.diff(zeros) > 0))  # Monotonically increasing
    
    def test_golden_ratio_value(self):
        """Test golden ratio calculation"""
        self.assertAlmostEqual(self.phi, 1.618033988749895, places=10)
    
    def test_biological_frequency_mapping(self):
        """Test mapping of Riemann zeros to biological frequencies"""
        eigenvalues = np.array([14.134725142])  # First Riemann zero
        freqs = map_to_biological_frequencies(eigenvalues, self.phi, 1e-6)
        
        # Should be in reasonable biological range
        self.assertGreater(freqs[0], 0)
        self.assertLess(freqs[0], 1000)
    
    def test_operator_initialization(self):
        """Test operator initializes correctly"""
        self.assertIsNotNone(self.operator.eigenvalues)
        self.assertIsNotNone(self.operator.bio_frequencies)
        self.assertEqual(len(self.operator.eigenvalues), len(self.operator.bio_frequencies))
    
    def test_spectrum_generation(self):
        """Test spectrum generation in frequency range"""
        spectrum = self.operator.get_spectrum(100, 200)
        
        self.assertIn('frequencies', spectrum)
        self.assertIn('amplitudes', spectrum)
        
        # All frequencies should be in range
        self.assertTrue(np.all(spectrum['frequencies'] >= 100))
        self.assertTrue(np.all(spectrum['frequencies'] <= 200))
    
    def test_target_frequency_validation(self):
        """Test validation of 141.7 Hz target"""
        validation = self.operator.validate_target_frequency(141.7)
        
        self.assertIn('target_frequency', validation)
        self.assertIn('nearest_eigenfrequency', validation)
        self.assertIn('deviation_hz', validation)
        
        # Should be reasonably close
        self.assertLess(validation['deviation_hz'], 50)


class TestUnifiedTissueResonance(unittest.TestCase):
    """Test unified tissue resonance model"""
    
    def setUp(self):
        """Set up test fixtures"""
        self.cardiac_model = UnifiedTissueResonance(TissueType.CARDIAC)
        self.neural_model = UnifiedTissueResonance(TissueType.NEURAL)
    
    def test_tissue_parameters_defined(self):
        """Test that all tissue types have parameters"""
        for tissue_type in [TissueType.CARDIAC, TissueType.NEURAL, 
                           TissueType.EPITHELIAL, TissueType.MUSCULAR]:
            self.assertIn(tissue_type, TISSUE_PARAMETERS)
            params = TISSUE_PARAMETERS[tissue_type]
            
            # Weights should sum to 1.0
            total = (params.hilbert_polya_weight + 
                    params.navier_stokes_weight + 
                    params.magicicada_weight)
            self.assertAlmostEqual(total, 1.0, places=10)
    
    def test_cardiac_base_frequency(self):
        """Test cardiac tissue has correct base frequency"""
        self.assertAlmostEqual(self.cardiac_model.f_base, 141.7, places=1)
    
    def test_hilbert_polya_integration(self):
        """Test Hilbert-Pólya integration"""
        hp_freqs = self.cardiac_model.hilbert_polya_eigenfrequencies()
        self.assertIsInstance(hp_freqs, np.ndarray)
        self.assertGreater(len(hp_freqs), 0)
    
    def test_navier_stokes_integration(self):
        """Test Navier-Stokes integration"""
        ns_freq = self.cardiac_model.navier_stokes_regularized()
        
        # Should be in reasonable range
        self.assertGreater(ns_freq, 100)
        self.assertLess(ns_freq, 200)
    
    def test_magicicada_scaling(self):
        """Test Magicicada scaling law"""
        magic_data = self.cardiac_model.magicicada_scaling_law()
        
        self.assertIn('f_magicicada_13yr', magic_data)
        self.assertIn('f_magicicada_17yr', magic_data)
        self.assertIn('f_cytoplasma', magic_data)
        self.assertIn('scale_ratio', magic_data)
        
        # Cytoplasmic frequency should be ~141.7 Hz
        self.assertAlmostEqual(magic_data['f_cytoplasma'], 142.857, places=0)
        
        # Scale ratio should be enormous
        self.assertGreater(magic_data['scale_ratio'], 1e10)
    
    def test_spectrum_prediction(self):
        """Test spectrum prediction"""
        freqs, amps = self.cardiac_model.predict_spectrum(50, 250)
        
        self.assertEqual(len(freqs), len(amps))
        self.assertGreater(len(freqs), 0)
        
        # Find peak
        peak_idx = np.argmax(amps)
        peak_freq = freqs[peak_idx]
        
        # Peak should be near 141.7 Hz for cardiac
        self.assertLess(abs(peak_freq - 141.7), 10)
    
    def test_141hz_validation(self):
        """Test validation of 141.7 Hz prediction"""
        validation = self.cardiac_model.validate_141hz()
        
        self.assertIn('unified_frequency', validation)
        self.assertIn('validated', validation)
        self.assertIn('tissue_type', validation)
        
        # Should validate successfully
        self.assertLess(validation['total_deviation'], 10)
    
    def test_different_tissue_types(self):
        """Test that different tissues have different predictions"""
        cardiac = UnifiedTissueResonance(TissueType.CARDIAC)
        neural = UnifiedTissueResonance(TissueType.NEURAL)
        
        # Should have different base frequencies
        self.assertNotEqual(cardiac.f_base, neural.f_base)


class TestINGNIOAURONSystem(unittest.TestCase):
    """Test INGΝIO CMI and AURON systems"""
    
    def setUp(self):
        """Set up test fixtures"""
        self.ingnio = INGNIOCMISystem()
        self.auron = AURONProtectionSystem()
        self.therapy = ResonanceTherapySystem()
    
    def test_ingnio_frequency(self):
        """Test INGΝIO operates at 141.7001 Hz"""
        self.assertAlmostEqual(self.ingnio.frequency, 141.7001, places=4)
    
    def test_auron_frequency(self):
        """Test AURON operates at 151.7001 Hz"""
        self.assertAlmostEqual(self.auron.frequency, 151.7001, places=4)
    
    def test_protection_band(self):
        """Test protection band is 141.7 - 151.7 Hz"""
        band = self.auron.get_protection_band()
        
        self.assertAlmostEqual(band['lower_frequency'], 141.7, places=1)
        self.assertAlmostEqual(band['upper_frequency'], 151.7001, places=4)
        self.assertAlmostEqual(band['bandwidth'], 10.0001, places=4)
    
    def test_biological_validation(self):
        """Test INGΝIO biological connection"""
        validation = self.ingnio.validate_biological_connection()
        
        self.assertIn('ingnio_frequency', validation)
        self.assertIn('biological_resonance', validation)
        self.assertIn('deviation_hz', validation)
        
        # Deviation should be minimal
        self.assertLess(validation['deviation_hz'], 0.001)
        self.assertLess(validation['deviation_percent'], 0.001)
    
    def test_frequency_protection(self):
        """Test frequency protection logic"""
        # 141.7 Hz should be protected
        self.assertTrue(self.auron.is_frequency_protected(141.7))
        
        # 145.0 Hz should be protected
        self.assertTrue(self.auron.is_frequency_protected(145.0))
        
        # 151.7001 Hz should be protected (upper bound)
        self.assertTrue(self.auron.is_frequency_protected(151.7001))
        
        # 140.0 Hz should NOT be protected
        self.assertFalse(self.auron.is_frequency_protected(140.0))
        
        # 160.0 Hz should NOT be protected
        self.assertFalse(self.auron.is_frequency_protected(160.0))
    
    def test_system_coherence(self):
        """Test overall system coherence"""
        validation = self.therapy.validate_system()
        
        self.assertTrue(validation['ingnio_validated'])
        self.assertTrue(validation['ingnio_in_protection_band'])
        self.assertTrue(validation['system_coherent'])
    
    def test_therapeutic_protocol(self):
        """Test therapeutic protocol configuration"""
        protocol = self.therapy.protocol
        
        # Check phase frequencies
        self.assertAlmostEqual(protocol.phase_1_freq, 141.7, places=1)
        self.assertAlmostEqual(protocol.phase_2_freq, 151.7001, places=4)
        self.assertAlmostEqual(protocol.phase_3_freq, 888.0, places=1)
        
        # Check total duration
        total = (protocol.phase_1_duration_min + 
                protocol.phase_2_duration_min + 
                protocol.phase_3_duration_min)
        self.assertEqual(total, protocol.total_duration_min)
    
    def test_tissue_diagnosis(self):
        """Test tissue resonance diagnosis"""
        # Perfect resonance
        diagnosis1 = self.therapy.diagnose_tissue_resonance(141.7)
        self.assertLess(diagnosis1['deviation'], 0.5)
        self.assertIn('Excellent', diagnosis1['recommendation'])
        
        # Moderate deviation
        diagnosis2 = self.therapy.diagnose_tissue_resonance(144.0)
        self.assertGreater(diagnosis2['deviation'], 2.0)
        self.assertLess(diagnosis2['deviation'], 5.0)
        
        # Large deviation
        diagnosis3 = self.therapy.diagnose_tissue_resonance(130.0)
        self.assertGreater(diagnosis3['deviation'], 10.0)


class TestTheoryUnification(unittest.TestCase):
    """Test the unification of all three theories"""
    
    def setUp(self):
        """Set up test fixtures"""
        self.model = UnifiedTissueResonance(TissueType.CARDIAC)
    
    def test_all_theories_converge(self):
        """Test that all three theories converge to similar frequencies"""
        # Get contributions from each theory
        hp_freqs = self.model.hilbert_polya_eigenfrequencies()
        ns_freq = self.model.navier_stokes_regularized()
        magic_data = self.model.magicicada_scaling_law()
        
        # Unify
        results = self.model.unify_theories(hp_freqs, ns_freq, magic_data)
        
        # All should be within reasonable range of 141.7 Hz
        target = 141.7
        tolerance = 20.0  # Hz
        
        self.assertLess(abs(results['hilbert_polya_contribution'] - target), tolerance)
        self.assertLess(abs(results['navier_stokes_contribution'] - target), tolerance)
        self.assertLess(abs(results['magicicada_contribution'] - target), tolerance)
    
    def test_convergence_quality(self):
        """Test convergence quality metric"""
        validation = self.model.validate_141hz()
        
        # Convergence quality should be high
        self.assertGreater(validation['convergence_quality'], 0.5)
    
    def test_ingnio_connection(self):
        """Test connection between tissue model and INGΝIO"""
        validation = self.model.validate_141hz()
        ingnio = INGNIOCMISystem()
        
        # Unified frequency should be very close to INGΝIO
        unified = validation['unified_frequency']
        deviation = abs(unified - ingnio.frequency)
        
        # Should be within 1 Hz
        self.assertLess(deviation, 1.0)


def run_all_tests():
    """Run all tests and print summary"""
    print("=" * 80)
    print("UNIFIED TISSUE RESONANCE MODEL - TEST SUITE")
    print("=" * 80)
    print()
    
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test cases
    suite.addTests(loader.loadTestsFromTestCase(TestHilbertPolyaOperator))
    suite.addTests(loader.loadTestsFromTestCase(TestUnifiedTissueResonance))
    suite.addTests(loader.loadTestsFromTestCase(TestINGNIOAURONSystem))
    suite.addTests(loader.loadTestsFromTestCase(TestTheoryUnification))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Print summary
    print()
    print("=" * 80)
    print("TEST SUMMARY")
    print("=" * 80)
    print(f"Tests run: {result.testsRun}")
    print(f"Successes: {result.testsRun - len(result.failures) - len(result.errors)}")
    print(f"Failures: {len(result.failures)}")
    print(f"Errors: {len(result.errors)}")
    print()
    
    if result.wasSuccessful():
        print("✓ ALL TESTS PASSED")
    else:
        print("✗ SOME TESTS FAILED")
    
    return result.wasSuccessful()


if __name__ == "__main__":
    success = run_all_tests()
    exit(0 if success else 1)
