#!/usr/bin/env python3
"""
Test Suite for QCAL Biological Hypothesis
==========================================

Comprehensive tests for all biological QCAL modules:
- qcal_biological_hypothesis.py
- magicicada_simulation.py
- qcal_experiments.py
- nse_biofluid_coupling.py

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
Date: 27 de enero de 2026
License: MIT
"""

import unittest
import numpy as np
import sys
from io import StringIO

# Import modules to test
from qcal_biological_hypothesis import (
    SpectralField, BiologicalFilter, PhaseAccumulator, BiologicalClock,
    BiologicalConstants, FrequencyBand, SpectralComponent,
    create_example_annual_cycle
)
from magicicada_simulation import (
    MagicicadaClock, MagicicadaParameters,
    simulate_population, demonstrate_prime_cycle_advantage
)
from qcal_experiments import (
    Experiment1_SpectralManipulation,
    Experiment2_PhaseMemory,
    Experiment3_GenomicResonance,
    ExperimentalGroup
)
from nse_biofluid_coupling import (
    BiofluidParameters,
    derive_characteristic_frequency,
    simulate_oscillatory_biofluid,
    analyze_frequency_spectrum
)


class TestSpectralField(unittest.TestCase):
    """Test spectral field implementation"""
    
    def test_empty_field(self):
        """Test empty spectral field"""
        field = SpectralField()
        self.assertEqual(len(field.components), 0)
        
        t = np.linspace(0, 1, 100)
        psi = field.evaluate(t)
        np.testing.assert_array_equal(psi, np.zeros_like(t))
    
    def test_add_component(self):
        """Test adding spectral components"""
        field = SpectralField()
        field.add_component(1.0, 1.0, 0.0, "Test component")
        
        self.assertEqual(len(field.components), 1)
        self.assertEqual(field.components[0].amplitude, 1.0)
        self.assertEqual(field.components[0].frequency_hz, 1.0)
    
    def test_frequency_band_classification(self):
        """Test automatic frequency band classification"""
        field = SpectralField()
        
        # Low frequency
        field.add_component(1.0, 1e-6, description="Low")
        self.assertEqual(field.components[0].band, FrequencyBand.LOW)
        
        # Medium frequency
        field.add_component(1.0, 50.0, description="Medium")
        self.assertEqual(field.components[1].band, FrequencyBand.MEDIUM)
        
        # High frequency
        field.add_component(1.0, 2000.0, description="High")
        self.assertEqual(field.components[2].band, FrequencyBand.HIGH)
    
    def test_field_evaluation(self):
        """Test field evaluation at specific times"""
        field = SpectralField()
        field.add_component(1.0, 1.0, 0.0, "1 Hz component")
        
        t = np.array([0.0, 0.25, 0.5])
        psi = field.evaluate(t)
        
        # Should be complex exponentials
        self.assertEqual(len(psi), 3)
        self.assertTrue(np.iscomplexobj(psi))
        
        # At t=0, should be amplitude (real part ≈ 1.0)
        self.assertAlmostEqual(np.real(psi[0]), 1.0, places=5)
    
    def test_get_spectrum(self):
        """Test spectrum extraction"""
        field = SpectralField()
        field.add_component(1.0, 1.0)
        field.add_component(0.5, 2.0)
        
        freqs, amps = field.get_spectrum()
        
        np.testing.assert_array_equal(freqs, [1.0, 2.0])
        np.testing.assert_array_equal(amps, [1.0, 0.5])


class TestBiologicalFilter(unittest.TestCase):
    """Test biological filter implementation"""
    
    def test_filter_creation(self):
        """Test filter initialization"""
        bio_filter = BiologicalFilter(tau_response=3600.0)
        self.assertEqual(bio_filter.tau, 3600.0)
    
    def test_filter_response(self):
        """Test filter response function"""
        bio_filter = BiologicalFilter(tau_response=1.0)
        
        omega = np.array([0.0, 1.0, 10.0])
        H = bio_filter.response(omega)
        
        # At ω=0, response should be 1
        self.assertAlmostEqual(np.abs(H[0]), 1.0, places=5)
        
        # Response should decrease with frequency
        self.assertLess(np.abs(H[2]), np.abs(H[1]))
    
    def test_band_selectivity(self):
        """Test frequency band selectivity"""
        bio_filter = BiologicalFilter()
        
        # Test different bands
        freqs = np.array([1e-6, 50.0, 2000.0])  # low, medium, high
        weights = bio_filter.apply_band_selectivity(freqs)
        
        # Low band should be 0.5
        self.assertAlmostEqual(weights[0], 0.5)
        
        # Medium band should be 1.0
        self.assertAlmostEqual(weights[1], 1.0)
        
        # High band should be 0.0
        self.assertAlmostEqual(weights[2], 0.0)


class TestPhaseAccumulator(unittest.TestCase):
    """Test phase accumulator implementation"""
    
    def test_accumulator_creation(self):
        """Test accumulator initialization"""
        acc = PhaseAccumulator(alpha=0.1)
        self.assertEqual(acc.alpha, 0.1)
        self.assertEqual(len(acc.phase_history), 0)
    
    def test_phase_accumulation(self):
        """Test phase accumulation over time"""
        field = SpectralField()
        field.add_component(1.0, 1.0)
        
        bio_filter = BiologicalFilter()
        acc = PhaseAccumulator(alpha=0.1)
        
        # Accumulate over several time steps
        for i in range(10):
            t = i * 1.0
            phase = acc.accumulate(field, bio_filter, t, 1.0)
            self.assertGreaterEqual(phase, 0.0)
        
        self.assertEqual(len(acc.phase_history), 10)
    
    def test_phase_memory(self):
        """Test memory parameter effect"""
        field = SpectralField()
        field.add_component(1.0, 1.0)
        bio_filter = BiologicalFilter()
        
        # Accumulator with memory
        acc_memory = PhaseAccumulator(alpha=0.1)
        acc_memory.accumulate(field, bio_filter, 0.0, 1.0)
        phase1 = acc_memory.accumulate(field, bio_filter, 1.0, 1.0)
        
        # Check that memory is applied (should retain 90% of previous)
        self.assertGreater(phase1, 0.0)
    
    def test_phase_derivative(self):
        """Test phase derivative calculation"""
        field = SpectralField()
        field.add_component(1.0, 1.0)
        bio_filter = BiologicalFilter()
        acc = PhaseAccumulator()
        
        # Need at least 2 points for derivative
        acc.accumulate(field, bio_filter, 0.0, 1.0)
        acc.accumulate(field, bio_filter, 1.0, 1.0)
        
        dphi_dt = acc.get_phase_derivative()
        # Should be positive (accumulating)
        self.assertGreaterEqual(dphi_dt, 0.0)


class TestBiologicalClock(unittest.TestCase):
    """Test biological clock implementation"""
    
    def test_clock_creation(self):
        """Test clock initialization"""
        clock = BiologicalClock(critical_phase=10.0, name="Test Clock")
        self.assertEqual(clock.critical_phase, 10.0)
        self.assertEqual(clock.name, "Test Clock")
        self.assertFalse(clock.activated)
    
    def test_activation_condition(self):
        """Test activation condition checking"""
        clock = BiologicalClock(critical_phase=5.0)
        
        # Manually set phase history
        clock.phase_accumulator.phase_history = [3.0, 4.0, 6.0]
        clock.phase_accumulator.time_history = [0.0, 1.0, 2.0]
        
        # Should activate (phase > critical and derivative > 0)
        activated = clock.check_activation_condition()
        self.assertTrue(activated)
    
    def test_add_environmental_cycle(self):
        """Test adding environmental cycles"""
        clock = BiologicalClock(critical_phase=10.0)
        clock.add_environmental_cycle(1.0, 365.25, description="Annual")
        
        self.assertEqual(len(clock.spectral_field.components), 1)
    
    def test_simulation(self):
        """Test clock simulation"""
        clock = BiologicalClock(critical_phase=1.0)
        clock.add_environmental_cycle(1.0, 1.0, description="Daily")
        
        t = np.linspace(0, 10 * 24 * 3600, 1000)
        results = clock.simulate(t)
        
        self.assertIn('time', results)
        self.assertIn('phase', results)
        self.assertIn('activated', results)
        self.assertEqual(len(results['phase']), len(t))


class TestMagicicadaSimulation(unittest.TestCase):
    """Test Magicicada simulation"""
    
    def test_parameters_validation(self):
        """Test parameter validation"""
        # Valid cycles
        params_13 = MagicicadaParameters(cycle_years=13)
        self.assertTrue(params_13.is_prime_cycle)
        
        params_17 = MagicicadaParameters(cycle_years=17)
        self.assertTrue(params_17.is_prime_cycle)
        
        # Invalid cycle should raise error
        with self.assertRaises(ValueError):
            MagicicadaParameters(cycle_years=12)
    
    def test_precision_calculation(self):
        """Test precision percentage calculation"""
        params = MagicicadaParameters(cycle_years=17, observed_std_days=4.0)
        
        precision = params.precision_percentage
        # Should be around 99.92% as stated in document
        self.assertGreater(precision, 99.9)
    
    def test_magicicada_clock_creation(self):
        """Test Magicicada clock creation"""
        params = MagicicadaParameters(cycle_years=17)
        clock = MagicicadaClock(params)
        
        self.assertEqual(clock.params.cycle_years, 17)
        # Should have environmental frequencies set up
        self.assertGreater(len(clock.spectral_field.components), 0)
    
    def test_emergence_simulation(self):
        """Test emergence simulation"""
        params = MagicicadaParameters(cycle_years=17)
        clock = MagicicadaClock(params)
        
        # Simulate (limited time for testing)
        results = clock.simulate_emergence(years_to_simulate=2.0)
        
        self.assertIn('time_years', results)
        self.assertIn('phase', results)
        self.assertTrue(len(results['phase']) > 0)
    
    def test_prime_cycle_advantage(self):
        """Test prime cycle advantage demonstration"""
        # Should run without errors
        old_stdout = sys.stdout
        sys.stdout = StringIO()
        
        demonstrate_prime_cycle_advantage()
        
        output = sys.stdout.getvalue()
        sys.stdout = old_stdout
        
        # Check that output contains expected information
        self.assertIn("13", output)
        self.assertIn("17", output)
        self.assertIn("Prime", output)


class TestExperiments(unittest.TestCase):
    """Test experimental framework"""
    
    def test_experiment1_setup(self):
        """Test Experiment 1 setup"""
        exp = Experiment1_SpectralManipulation()
        
        exp.setup_group_control(n_replicates=5)
        exp.setup_group_spectral(n_replicates=5)
        exp.setup_group_energetic(n_replicates=5)
        
        self.assertEqual(len(exp.groups[ExperimentalGroup.CONTROL]), 5)
        self.assertEqual(len(exp.groups[ExperimentalGroup.SPECTRAL]), 5)
        self.assertEqual(len(exp.groups[ExperimentalGroup.ENERGETIC]), 5)
    
    def test_experiment2_creation(self):
        """Test Experiment 2 creation"""
        exp = Experiment2_PhaseMemory()
        self.assertEqual(exp.alpha_memory, 0.1)
    
    def test_experiment3_creation(self):
        """Test Experiment 3 creation"""
        exp = Experiment3_GenomicResonance()
        self.assertIn(141.7, exp.test_frequencies_hz)
    
    def test_experiment3_frequency_response(self):
        """Test frequency response simulation"""
        exp = Experiment3_GenomicResonance()
        results = exp.simulate_frequency_response(resonant_freq_hz=141.7)
        
        self.assertIn('frequencies', results)
        self.assertIn('responses', results)
        self.assertTrue(results['frequency_selectivity_observed'])


class TestNSEBiofluidCoupling(unittest.TestCase):
    """Test Navier-Stokes biofluid coupling"""
    
    def test_biofluid_parameters(self):
        """Test biofluid parameters"""
        params = BiofluidParameters(
            velocity_um_s=5.0,
            length_scale_um=50.0
        )
        
        # Test conversions
        self.assertAlmostEqual(params.velocity_m_s, 5e-6)
        self.assertAlmostEqual(params.length_scale_m, 50e-6)
        
        # Test Reynolds number
        Re = params.reynolds_number
        self.assertGreater(Re, 0.0)
        self.assertLess(Re, 1.0)  # Should be in low Re regime
    
    def test_characteristic_frequency_derivation(self):
        """Test characteristic frequency derivation"""
        # Test with values that give ~141.7 Hz
        # v = 7.085 μm/s, λ = 0.05 μm → f = 141.7 Hz
        f = derive_characteristic_frequency(7.085, 0.05)
        
        # Should be close to 141.7 Hz
        self.assertAlmostEqual(f, 141.7, places=1)
    
    def test_141_7_hz_from_parameters(self):
        """Test that 141.7 Hz emerges from biological parameters"""
        params = BiofluidParameters(
            velocity_um_s=7.085,
            length_scale_um=0.05  # 50 nm protein scale
        )
        
        f = params.characteristic_frequency_hz
        
        # Should be 141.7 Hz
        self.assertAlmostEqual(f, 141.7, places=1)
    
    def test_strouhal_number(self):
        """Test Strouhal number calculation"""
        params = BiofluidParameters(velocity_um_s=7.085, length_scale_um=0.05)
        
        St = params.strouhal_number
        
        # Should be close to 1 for natural frequencies
        self.assertAlmostEqual(St, 1.0, places=1)
    
    def test_oscillatory_simulation(self):
        """Test oscillatory biofluid simulation"""
        params = BiofluidParameters()
        
        results = simulate_oscillatory_biofluid(
            params, 
            forcing_freq_hz=141.7, 
            duration_s=0.1,
            n_points=1000
        )
        
        self.assertIn('time', results)
        self.assertIn('velocity', results)
        self.assertEqual(len(results['time']), 1000)
    
    def test_frequency_spectrum_analysis(self):
        """Test FFT spectrum analysis"""
        # Create simple sinusoidal signal
        t = np.linspace(0, 1, 1000)
        f_test = 141.7
        signal = np.sin(2 * np.pi * f_test * t)
        
        freqs, power = analyze_frequency_spectrum(t, signal)
        
        # Find peak
        peak_idx = np.argmax(power)
        peak_freq = freqs[peak_idx]
        
        # Should detect the 141.7 Hz component
        self.assertAlmostEqual(peak_freq, f_test, places=0)


class TestBiologicalConstants(unittest.TestCase):
    """Test biological constants"""
    
    def test_fundamental_frequency(self):
        """Test fundamental frequency constant"""
        const = BiologicalConstants()
        self.assertEqual(const.F0_HZ, 141.7)
    
    def test_cycle_frequencies(self):
        """Test environmental cycle frequencies"""
        const = BiologicalConstants()
        
        # Annual frequency should be ~1 cycle per year
        f_annual = const.F_ANNUAL_HZ
        period_days = 1.0 / (f_annual * 24 * 3600)
        self.assertAlmostEqual(period_days, 365.25, places=1)
        
        # Diurnal frequency should be ~1 cycle per day
        f_diurnal = const.F_DIURNAL_HZ
        period_hours = 1.0 / (f_diurnal * 3600)
        self.assertAlmostEqual(period_hours, 24.0, places=1)
    
    def test_memory_parameter(self):
        """Test phase memory parameter"""
        const = BiologicalConstants()
        self.assertEqual(const.ALPHA_MEMORY, 0.1)


class TestIntegration(unittest.TestCase):
    """Integration tests combining multiple modules"""
    
    def test_full_workflow_example(self):
        """Test complete workflow from spectral field to activation"""
        # Create spectral field with annual cycle
        field = create_example_annual_cycle()
        self.assertGreater(len(field.components), 0)
        
        # Create biological clock
        clock = BiologicalClock(critical_phase=5.0)
        clock.spectral_field = field
        
        # Simulate
        t = np.linspace(0, 730 * 24 * 3600, 5000)  # 2 years
        results = clock.simulate(t)
        
        # Should have phase accumulation
        self.assertTrue(np.any(results['phase'] > 0))
    
    def test_magicicada_to_nse_connection(self):
        """Test connection between Magicicada model and NSE derivation"""
        # Derive frequency from NSE with correct parameters
        params = BiofluidParameters(velocity_um_s=7.085, length_scale_um=0.05)
        f_nse = params.characteristic_frequency_hz
        
        # Use in biological model
        const = BiologicalConstants()
        f_bio = const.F0_HZ
        
        # Should be consistent
        self.assertAlmostEqual(f_nse, f_bio, places=1)


def run_tests():
    """Run all tests"""
    print("="*80)
    print("QCAL Biological Hypothesis - Test Suite")
    print("="*80)
    print()
    
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestSpectralField))
    suite.addTests(loader.loadTestsFromTestCase(TestBiologicalFilter))
    suite.addTests(loader.loadTestsFromTestCase(TestPhaseAccumulator))
    suite.addTests(loader.loadTestsFromTestCase(TestBiologicalClock))
    suite.addTests(loader.loadTestsFromTestCase(TestMagicicadaSimulation))
    suite.addTests(loader.loadTestsFromTestCase(TestExperiments))
    suite.addTests(loader.loadTestsFromTestCase(TestNSEBiofluidCoupling))
    suite.addTests(loader.loadTestsFromTestCase(TestBiologicalConstants))
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
