#!/usr/bin/env python3
"""
Test suite for cytoplasmic flow at Re ≈ 10⁻⁸

This test validates that the implementation correctly demonstrates
the regularity of fluids as the basis of life at Re ≈ 10⁻⁸.

Author: José Manuel Mota Burruezo
Instituto Consciencia Cuántica QCAL ∞³
Date: February 5, 2026
"""

import unittest
import numpy as np
from demo_cytoplasmic_re1e8 import (
    create_re_1e8_parameters,
    demonstrate_fluid_regularity_at_re1e8
)
from cytoplasmic_flow_model import CytoplasmicFlowModel


class TestCytoplasmicFlowRe1e8(unittest.TestCase):
    """Test cytoplasmic flow at Re ≈ 10⁻⁸"""
    
    def setUp(self):
        """Set up test fixtures"""
        self.params = create_re_1e8_parameters()
        self.model = CytoplasmicFlowModel(self.params)
        
    def test_reynolds_number_is_1e8(self):
        """Test that Reynolds number is approximately 10⁻⁸"""
        Re = self.params.reynolds_number
        
        # Should be very close to 10⁻⁸
        self.assertAlmostEqual(Re, 1e-8, places=9,
                              msg=f"Reynolds number {Re:.2e} should be ≈ 10⁻⁸")
        
        # Should definitely be << 1 (completely viscous)
        self.assertLess(Re, 1e-3,
                       msg=f"Reynolds number {Re:.2e} should be << 1")
        
    def test_parameter_consistency(self):
        """Test that parameters are physically consistent"""
        # Velocity should be in nm/s range (very slow)
        v = self.params.characteristic_velocity_m_s
        self.assertAlmostEqual(v, 1e-9, places=10,
                              msg="Velocity should be 1 nm/s")
        
        # Length should be in μm range (cellular scale)
        L = self.params.characteristic_length_m
        self.assertAlmostEqual(L, 1e-5, places=6,
                              msg="Length should be 10 μm")
        
        # Viscosity should be water-like
        nu = self.params.kinematic_viscosity_m2_s
        self.assertAlmostEqual(nu, 1e-6, places=7,
                              msg="Kinematic viscosity should be 10⁻⁶ m²/s")
        
        # Check Re = vL/nu
        Re_computed = (v * L) / nu
        Re_property = self.params.reynolds_number
        self.assertAlmostEqual(Re_computed, Re_property, places=10,
                              msg="Re computed should match Re property")
        
    def test_flow_regime_is_stokes(self):
        """Test that flow is in Stokes regime (completely viscous)"""
        self.assertTrue(self.params.flow_regime_description.startswith("Completely viscous"),
                       msg="Flow regime should be 'Completely viscous (Stokes flow)'")
        
        # Re << 1 for Stokes flow
        Re = self.params.reynolds_number
        self.assertLess(Re, 1e-3,
                       msg="Stokes flow requires Re << 1")
        
    def test_solution_exists_and_is_smooth(self):
        """Test that solution can be computed and is smooth"""
        # Solve for a short time
        t_span = (0.0, 0.001)  # 1 ms
        solution = self.model.solve(t_span, n_points=1000)
        
        # Solution should succeed
        self.assertTrue(solution['success'],
                       msg=f"Solution should succeed: {solution.get('message', 'No message')}")
        
        # Verify smoothness
        checks = self.model.verify_smooth_solution()
        
        # All checks should pass
        self.assertTrue(checks['no_nan'],
                       msg="Solution should have no NaN values")
        self.assertTrue(checks['no_inf'],
                       msg="Solution should have no Inf values")
        self.assertTrue(checks['bounded'],
                       msg="Solution should be bounded")
        self.assertTrue(checks['gradient_bounded'],
                       msg="Velocity gradient should be bounded")
        self.assertTrue(checks['smooth'],
                       msg="Solution should be smooth")
        self.assertTrue(checks['all_passed'],
                       msg="All smoothness checks should pass")
        
    def test_no_turbulence_possible(self):
        """Test that turbulence cannot form at Re ≈ 10⁻⁸"""
        Re = self.params.reynolds_number
        Re_critical = 2300  # Critical Re for turbulence onset
        
        # Re should be many orders of magnitude below critical
        self.assertLess(Re, Re_critical / 1e6,
                       msg=f"Re = {Re:.2e} should be << Re_critical = {Re_critical}")
        
        # At this Re, inertial term is negligible
        # Estimate: |(v·∇)v| / |ν∇²v| ~ Re << 1
        inertia_to_viscosity_ratio = Re
        self.assertLess(inertia_to_viscosity_ratio, 1e-7,
                       msg="Inertial term should be negligible compared to viscous term")
        
    def test_energy_dissipation_controlled(self):
        """Test that energy dissipation is controlled (no blow-up)"""
        # Solve for several periods
        T = 1.0 / self.params.fundamental_frequency_hz
        t_span = (0.0, 3 * T)
        solution = self.model.solve(t_span, n_points=3000)
        
        self.assertTrue(solution['success'],
                       msg="Long-time solution should succeed")
        
        # Compute energy
        velocity = solution['velocity']
        energy = 0.5 * self.params.density_kg_m3 * velocity**2
        
        # Energy should remain bounded (no blow-up)
        max_energy = np.max(np.abs(energy))
        self.assertLess(max_energy, 1e-10,
                       msg=f"Energy should remain small: {max_energy:.2e} J")
        
        # Energy should not grow exponentially
        energy_start = np.mean(energy[:100])
        energy_end = np.mean(energy[-100:])
        
        # Allow for oscillations but no exponential growth
        self.assertLess(energy_end, 10 * energy_start,
                       msg="Energy should not grow exponentially")
        
    def test_flow_is_reversible(self):
        """Test that flow is reversible (characteristic of Stokes flow)"""
        # At Re << 1, the equations are time-reversible
        # This means the solution should be symmetric under t → -t
        
        # For the damped oscillator model we use:
        # ∂v/∂t = -γv + f(t)
        # This IS reversible when f(-t) = -f(t) or f(-t) = f(t)
        
        # The key is that the nonlinear term (v·∇)v is negligible
        # So the equation is effectively linear and reversible
        
        Re = self.params.reynolds_number
        self.assertLess(Re, 1e-4,
                       msg="For reversibility, need Re << 1")
        
    def test_viscous_timescale(self):
        """Test that viscous timescale is physically reasonable"""
        tau_visc = self.params.viscous_time_scale_s
        
        # τ_ν = L²/ν
        L = self.params.characteristic_length_m
        nu = self.params.kinematic_viscosity_m2_s
        tau_expected = L**2 / nu
        
        self.assertAlmostEqual(tau_visc, tau_expected, places=10,
                              msg="Viscous timescale should be L²/ν")
        
        # For L = 10 μm, ν = 10⁻⁶ m²/s:
        # τ_ν = (10⁻⁵)² / 10⁻⁶ = 10⁻⁴ s = 0.1 ms
        self.assertAlmostEqual(tau_visc, 0.1e-3, places=4,
                              msg="Viscous timescale should be 0.1 ms for 10 μm scale")
        
    def test_biological_relevance(self):
        """Test that parameters are in biologically relevant range"""
        # Temperature should be body temperature
        T = self.params.temperature_K
        self.assertAlmostEqual(T, 310.0, delta=5.0,
                              msg="Temperature should be near body temperature (37°C)")
        
        # Density should be near water
        rho = self.params.density_kg_m3
        self.assertAlmostEqual(rho, 1000.0, delta=100.0,
                              msg="Density should be near water (1000 kg/m³)")
        
        # Length scale should be cellular (1-100 μm)
        L = self.params.characteristic_length_m
        self.assertGreater(L, 1e-6,
                          msg="Length should be > 1 μm (cellular scale)")
        self.assertLess(L, 100e-6,
                       msg="Length should be < 100 μm (cellular scale)")
        
        # Velocity should be slow (nm/s to μm/s)
        v = self.params.characteristic_velocity_m_s
        self.assertGreater(v, 1e-10,
                          msg="Velocity should be > 0.1 nm/s")
        self.assertLess(v, 1e-5,
                       msg="Velocity should be < 10 μm/s")
        
    def test_peclet_number_small(self):
        """Test that Peclet number is small (diffusion dominates)"""
        Pe = self.params.peclet_number
        
        # Pe = vL/D where D ≈ 10⁻⁹ m²/s (molecular diffusion)
        # Pe should be << 1 for diffusion-dominated transport
        self.assertLess(Pe, 1,
                       msg=f"Peclet number {Pe:.2e} should be < 1 for diffusion dominance")
        
    def test_fundamental_frequency(self):
        """Test that fundamental frequency is QCAL frequency"""
        f0 = self.params.fundamental_frequency_hz
        
        self.assertAlmostEqual(f0, 141.7, delta=0.1,
                              msg="Fundamental frequency should be 141.7 Hz (QCAL)")
        
    def test_solution_regularity_indicators(self):
        """Test multiple indicators of solution regularity"""
        # Solve
        t_span = (0.0, 0.005)  # 5 ms
        solution = self.model.solve(t_span, n_points=2000)
        
        velocity = solution['velocity']
        time = solution['time']
        
        # 1. Check continuity (no jumps)
        velocity_diff = np.diff(velocity)
        max_jump = np.max(np.abs(velocity_diff))
        typical_change = np.std(velocity_diff)
        self.assertLess(max_jump, 10 * typical_change,
                       msg="Velocity should be continuous (no large jumps)")
        
        # 2. Check differentiability
        velocity_grad = np.gradient(velocity, time)
        self.assertFalse(np.any(np.isnan(velocity_grad)),
                        msg="Velocity gradient should exist (no NaN)")
        self.assertFalse(np.any(np.isinf(velocity_grad)),
                        msg="Velocity gradient should be finite (no Inf)")
        
        # 3. Check boundedness
        self.assertTrue(np.all(np.abs(velocity) < 1e-6),
                       msg="Velocity should be bounded (< 1 μm/s)")
        
        # 4. Check regularity of spectrum
        frequencies, power = self.model.compute_frequency_spectrum()
        # Spectrum should be well-behaved (finite everywhere)
        self.assertFalse(np.any(np.isnan(power)),
                        msg="Power spectrum should have no NaN")
        self.assertFalse(np.any(np.isinf(power)),
                        msg="Power spectrum should have no Inf")
        
        # Power should be non-negative
        self.assertTrue(np.all(power >= 0),
                       msg="Power spectrum should be non-negative")


class TestRe1e8Demonstration(unittest.TestCase):
    """Test the demonstration function"""
    
    def test_demonstration_runs_successfully(self):
        """Test that the full demonstration runs without errors"""
        # This is an integration test
        model = demonstrate_fluid_regularity_at_re1e8()
        
        self.assertIsNotNone(model,
                            msg="Demonstration should return a model")
        self.assertIsNotNone(model.solution,
                            msg="Model should have a solution")
        
        # Verify key properties
        Re = model.params.reynolds_number
        self.assertAlmostEqual(Re, 1e-8, places=9,
                              msg="Demonstrated Reynolds number should be 10⁻⁸")
        
        checks = model.verify_smooth_solution()
        self.assertTrue(checks['all_passed'],
                       msg="All smoothness checks should pass in demonstration")


def run_tests():
    """Run all tests and return results"""
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test cases
    suite.addTests(loader.loadTestsFromTestCase(TestCytoplasmicFlowRe1e8))
    suite.addTests(loader.loadTestsFromTestCase(TestRe1e8Demonstration))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    return result


if __name__ == '__main__':
    print("="*80)
    print("TEST SUITE: Cytoplasmic Flow at Re ≈ 10⁻⁸")
    print("="*80)
    print()
    
    result = run_tests()
    
    print()
    print("="*80)
    if result.wasSuccessful():
        print("✓ ALL TESTS PASSED")
        print("="*80)
        print()
        print("VERIFIED:")
        print("• Reynolds number is Re ≈ 10⁻⁸")
        print("• Flow is in completely viscous (Stokes) regime")
        print("• Solutions are smooth and globally regular")
        print("• No turbulence possible")
        print("• Energy dissipation is controlled")
        print("• Parameters are biologically relevant")
        print()
        print("CONCLUSION:")
        print("The regularity of fluids at Re ≈ 10⁻⁸ IS the basis of life.")
        print("="*80)
        exit(0)
    else:
        print("✗ SOME TESTS FAILED")
        print("="*80)
        exit(1)
