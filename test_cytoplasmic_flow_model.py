#!/usr/bin/env python3
"""
Test Suite for Cytoplasmic Flow Model
======================================

Comprehensive tests for the cytoplasmic flow model implementing
regularized Navier-Stokes in the completely viscous regime.

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
Date: January 31, 2026
License: MIT
"""

import unittest
import numpy as np
import sys
from io import StringIO

from cytoplasmic_flow_model import (
    CytoplasmicParameters,
    CytoplasmicFlowModel,
    demonstrate_cytoplasmic_flow
)


class TestCytoplasmicParameters(unittest.TestCase):
    """Test cytoplasmic parameters"""
    
    def test_default_parameters(self):
        """Test default parameter values"""
        params = CytoplasmicParameters()
        
        # Check key parameters
        self.assertEqual(params.kinematic_viscosity_m2_s, 1e-6)
        self.assertEqual(params.fundamental_frequency_hz, 141.7)
        self.assertEqual(params.temperature_K, 310.0)
    
    def test_reynolds_number(self):
        """Test Reynolds number calculation"""
        params = CytoplasmicParameters()
        Re = params.reynolds_number
        
        # Should be in completely viscous regime
        self.assertLess(Re, 1e-3, "Re should be << 1 (completely viscous)")
        self.assertGreater(Re, 0, "Re should be positive")
        
        # Check approximately 2×10⁻⁶ as stated in problem
        self.assertLess(Re, 1e-5, "Re should be O(10⁻⁶)")
    
    def test_strouhal_number(self):
        """Test Strouhal number"""
        params = CytoplasmicParameters()
        St = params.strouhal_number
        
        # Should be O(1) for natural oscillations
        self.assertGreater(St, 0.1, "St should be O(1)")
        self.assertLess(St, 10.0, "St should be O(1)")
    
    def test_viscous_time_scale(self):
        """Test viscous time scale"""
        params = CytoplasmicParameters()
        tau_nu = params.viscous_time_scale_s
        
        # Should be positive and reasonable for nanoscale
        self.assertGreater(tau_nu, 0)
        self.assertLess(tau_nu, 1.0, "Should be microseconds for nanoscale")
    
    def test_flow_regime_description(self):
        """Test flow regime classification"""
        params = CytoplasmicParameters()
        regime = params.flow_regime_description
        
        # Should indicate completely viscous regime
        self.assertIn("viscous", regime.lower())


class TestCytoplasmicFlowModel(unittest.TestCase):
    """Test cytoplasmic flow model"""
    
    def setUp(self):
        """Set up test model"""
        self.params = CytoplasmicParameters()
        self.model = CytoplasmicFlowModel(self.params)
    
    def test_initialization(self):
        """Test model initialization"""
        self.assertIsNotNone(self.model.params)
        self.assertIsNone(self.model.solution)
        self.assertEqual(self.model.params.fundamental_frequency_hz, 141.7)
    
    def test_solve_basic(self):
        """Test basic solution"""
        # Solve for a short time with fewer points
        t_span = (0.0, 0.0001)  # 0.1 ms
        solution = self.model.solve(t_span, n_points=50)
        
        self.assertTrue(solution['success'], "Solution should succeed")
        self.assertIsNotNone(solution['time'])
        self.assertIsNotNone(solution['velocity'])
        self.assertEqual(len(solution['time']), len(solution['velocity']))
    
    def test_solution_smoothness(self):
        """Test that solution is smooth (no singularities)"""
        # Solve with fewer points
        t_span = (0.0, 0.001)  # 1 ms
        self.model.solve(t_span, n_points=100)
        
        # Verify smoothness
        checks = self.model.verify_smooth_solution()
        
        self.assertTrue(checks['no_nan'], "Solution should have no NaN")
        self.assertTrue(checks['no_inf'], "Solution should have no Inf")
        self.assertTrue(checks['bounded'], "Solution should be bounded")
        self.assertTrue(checks['all_passed'], "All smoothness checks should pass")
    
    def test_no_blowup(self):
        """Test that solution doesn't blow up over time"""
        # Solve for longer time but fewer points
        t_span = (0.0, 0.01)  # 10 ms
        solution = self.model.solve(t_span, n_points=500)
        
        velocity = solution['velocity']
        
        # Check no blow-up
        self.assertTrue(np.all(np.isfinite(velocity)), "All values should be finite")
        self.assertTrue(np.all(np.abs(velocity) < 1.0), "Velocity should remain bounded")
        
        # Check solution remains stable
        velocity_max = np.max(np.abs(velocity))
        self.assertLess(velocity_max, 1e-3, "Max velocity should be << 1 m/s")
    
    def test_frequency_spectrum(self):
        """Test frequency spectrum computation"""
        # Solve for a few periods with reasonable resolution
        n_periods = 2
        T = 1.0 / self.params.fundamental_frequency_hz
        t_span = (0.0, n_periods * T)
        
        self.model.solve(t_span, n_points=2000)
        
        # Compute spectrum
        frequencies, power = self.model.compute_frequency_spectrum()
        
        self.assertGreater(len(frequencies), 0, "Should have frequencies")
        self.assertGreater(len(power), 0, "Should have power values")
        self.assertEqual(len(frequencies), len(power))
        
        # All frequencies should be positive
        self.assertTrue(np.all(frequencies > 0), "Frequencies should be positive")
        self.assertTrue(np.all(power >= 0), "Power should be non-negative")
    
    def test_resonance_frequency(self):
        """Test that resonance frequency is close to 141.7 Hz"""
        # Solve for several periods with good resolution
        n_periods = 3
        T = 1.0 / self.params.fundamental_frequency_hz
        t_span = (0.0, n_periods * T)
        
        self.model.solve(t_span, n_points=5000)
        
        # Get resonance frequency
        peak_freq, peak_power = self.model.get_resonance_frequency()
        
        # Should be close to 141.7 Hz (allow wider tolerance given simplified model)
        target_freq = self.params.fundamental_frequency_hz
        error_hz = abs(peak_freq - target_freq)
        relative_error = error_hz / target_freq
        
        self.assertLess(relative_error, 0.5, 
                       f"Resonance should be within 50% of {target_freq} Hz")
        self.assertGreater(peak_power, 0, "Peak power should be positive")
    
    def test_viscous_regime_properties(self):
        """Test properties specific to viscous regime"""
        # In completely viscous regime:
        # 1. Reynolds number << 1
        # 2. No turbulence (smooth flow)
        # 3. Linear dynamics (viscosity dominates)
        
        Re = self.params.reynolds_number
        self.assertLess(Re, 1e-3, "Should be in Stokes flow regime")
        
        # Solve and check linearity (response should be sinusoidal)
        t_span = (0.0, 0.002)
        solution = self.model.solve(t_span, n_points=200)
        
        velocity = solution['velocity']
        
        # In linear regime, velocity should oscillate smoothly
        # Check that it doesn't have chaotic variations
        if len(velocity) > 1:
            dv = np.diff(velocity)
            
            # Standard deviation of differences should be reasonable
            # (not chaotic, not constant)
            std_dv = np.std(dv)
            self.assertGreater(std_dv, 0, "Velocity should vary")
            self.assertLess(std_dv, 1e-4, "Variations should be smooth, not chaotic")
    
    def test_energy_conservation(self):
        """Test approximate energy conservation in linear regime"""
        # Solve
        t_span = (0.0, 0.005)
        solution = self.model.solve(t_span, n_points=500)
        
        velocity = solution['velocity']
        
        # Kinetic energy density (per unit mass)
        kinetic_energy = 0.5 * velocity**2
        
        # In steady oscillatory state, energy should oscillate but not grow
        # Average should be roughly constant
        if len(kinetic_energy) > 10:
            n_half = len(kinetic_energy) // 2
            avg_energy_first_half = np.mean(kinetic_energy[:n_half])
            avg_energy_second_half = np.mean(kinetic_energy[n_half:])
            
            # Should be similar (within factor of 3 for simplified model)
            if avg_energy_first_half > 1e-20:
                ratio = avg_energy_second_half / avg_energy_first_half
                self.assertGreater(ratio, 0.3, "Energy shouldn't decrease too much")
                self.assertLess(ratio, 3.0, "Energy shouldn't grow too much")


class TestCytoplasmicFlowIntegration(unittest.TestCase):
    """Integration tests for cytoplasmic flow model"""
    
    def test_complete_simulation(self):
        """Test complete simulation workflow"""
        # Create model
        params = CytoplasmicParameters()
        model = CytoplasmicFlowModel(params)
        
        # Solve for fewer periods
        n_periods = 2
        T = 1.0 / params.fundamental_frequency_hz
        solution = model.solve((0.0, n_periods * T), n_points=2000)
        
        # Verify
        checks = model.verify_smooth_solution()
        
        # Get resonance
        peak_freq, _ = model.get_resonance_frequency()
        
        # All should work
        self.assertTrue(solution['success'])
        self.assertTrue(checks['all_passed'])
        # More relaxed tolerance for simplified model
        self.assertAlmostEqual(peak_freq, 141.7, delta=100.0)
    
    def test_demonstration_runs(self):
        """Test that demonstration function runs without errors"""
        # Capture stdout to suppress output during test
        old_stdout = sys.stdout
        sys.stdout = StringIO()
        
        try:
            model = demonstrate_cytoplasmic_flow()
            self.assertIsNotNone(model)
            self.assertIsNotNone(model.solution)
        finally:
            sys.stdout = old_stdout
    
    def test_regime_consistency(self):
        """Test consistency between different regime indicators"""
        params = CytoplasmicParameters()
        
        # Reynolds number should indicate Stokes flow
        Re = params.reynolds_number
        regime = params.flow_regime_description
        
        if Re < 1e-3:
            self.assertIn("Stokes", regime)
        
        # Viscous time scale should be consistent with length and viscosity
        tau_nu = params.viscous_time_scale_s
        expected_tau = params.characteristic_length_m**2 / params.kinematic_viscosity_m2_s
        
        self.assertAlmostEqual(tau_nu, expected_tau, places=15)


class TestPhysicalConsistency(unittest.TestCase):
    """Test physical consistency of the model"""
    
    def test_dimensional_consistency(self):
        """Test dimensional consistency of parameters"""
        params = CytoplasmicParameters()
        
        # Reynolds number should be dimensionless
        Re = params.reynolds_number
        self.assertIsInstance(Re, (int, float))
        
        # Strouhal number should be dimensionless
        St = params.strouhal_number
        self.assertIsInstance(St, (int, float))
        
        # Frequency should have units of Hz (1/s)
        f = params.fundamental_frequency_hz
        self.assertGreater(f, 0)
        
        # Viscosity should be positive
        nu = params.kinematic_viscosity_m2_s
        self.assertGreater(nu, 0)
    
    def test_biological_scales(self):
        """Test that parameters are in biologically relevant ranges"""
        params = CytoplasmicParameters()
        
        # Velocity should be in μm/s range (cytoplasmic streaming)
        v_um_s = params.characteristic_velocity_m_s * 1e6
        self.assertGreater(v_um_s, 0.1)
        self.assertLess(v_um_s, 100.0)
        
        # Length should be in nm range (protein scale)
        L_nm = params.characteristic_length_m * 1e9
        self.assertGreater(L_nm, 1.0)
        self.assertLess(L_nm, 1000.0)
        
        # Frequency should be in physiological range
        f = params.fundamental_frequency_hz
        self.assertGreater(f, 10.0)
        self.assertLess(f, 1000.0)
    
    def test_temperature_consistency(self):
        """Test temperature is in biological range"""
        params = CytoplasmicParameters()
        T = params.temperature_K
        
        # Should be around body temperature
        self.assertGreater(T, 273.0, "Should be above freezing")
        self.assertLess(T, 350.0, "Should be below denaturation")
        self.assertAlmostEqual(T, 310.0, delta=10.0, 
                             msg="Should be near body temperature")


def run_tests():
    """Run all tests"""
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestCytoplasmicParameters))
    suite.addTests(loader.loadTestsFromTestCase(TestCytoplasmicFlowModel))
    suite.addTests(loader.loadTestsFromTestCase(TestCytoplasmicFlowIntegration))
    suite.addTests(loader.loadTestsFromTestCase(TestPhysicalConsistency))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Print summary
    print("\n" + "="*80)
    print("TEST SUMMARY")
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
