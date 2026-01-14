#!/usr/bin/env python3
"""
Tests for QCAL-SYNC-1/7 Global Synchronization Protocol
========================================================

Validates all components of the synchronization protocol:
- Mathematical-Physical synchronization (Navier-Stokes)
- Economic coupling (πCODE-888 & PSIX)
- Phase validation across repositories
- Dashboard generation and monitoring

Author: JMMB Ψ✧∞³
License: MIT
"""

import unittest
import numpy as np
import json
import os
from qcal_sync_protocol import (
    QCALSyncProtocol, 
    ProtocolConstants, 
    SyncState,
    SyncVector
)


class TestProtocolConstants(unittest.TestCase):
    """Test protocol constants are correctly defined."""
    
    def setUp(self):
        self.constants = ProtocolConstants()
    
    def test_unification_factor(self):
        """Test unification factor equals 1/7."""
        expected = 1/7
        self.assertAlmostEqual(self.constants.UNIFICATION_FACTOR, expected, places=6)
        self.assertAlmostEqual(self.constants.UNIFICATION_FACTOR, 0.1428, places=3)
    
    def test_fundamental_frequency(self):
        """Test fundamental frequency f₀ = 141.7001 Hz."""
        self.assertEqual(self.constants.F0_HZ, 141.7001)
    
    def test_resonance_frequency(self):
        """Test resonance frequency f∞ = 888.8 Hz."""
        self.assertEqual(self.constants.F_RESONANCE_HZ, 888.8)
    
    def test_kappa_pi(self):
        """Test consensus constant κ_Π = 2.5773."""
        self.assertEqual(self.constants.KAPPA_PI, 2.5773)
    
    def test_coherence_thresholds(self):
        """Test coherence thresholds are properly ordered."""
        self.assertEqual(self.constants.PSI_PERFECT, 1.0)
        self.assertEqual(self.constants.PSI_HIGH_COHERENCE, 0.95)
        self.assertEqual(self.constants.PSI_LOW_COHERENCE, 0.70)
        self.assertGreater(self.constants.PSI_PERFECT, self.constants.PSI_HIGH_COHERENCE)
        self.assertGreater(self.constants.PSI_HIGH_COHERENCE, self.constants.PSI_LOW_COHERENCE)
    
    def test_frequency_ordering(self):
        """Test that resonance frequency exceeds fundamental frequency."""
        self.assertGreater(self.constants.F_RESONANCE_HZ, self.constants.F0_HZ)


class TestNavierStokesSynchronization(unittest.TestCase):
    """Test Navier-Stokes data flow synchronization."""
    
    def setUp(self):
        self.protocol = QCALSyncProtocol()
    
    def test_laminar_flow_detection(self):
        """Test laminar flow is correctly detected with low velocity."""
        velocity_field = np.array([0.1, 0.1, 0.1])
        nu_adjusted, is_laminar = self.protocol.adjust_viscosity_laminar(
            velocity_field, time=0.0
        )
        
        self.assertTrue(is_laminar)
        self.assertEqual(self.protocol.data_flow_turbulence, 0.0)
        self.assertAlmostEqual(nu_adjusted, self.protocol.constants.NU_VISCOSITY)
    
    def test_turbulent_flow_detection(self):
        """Test turbulent flow triggers viscosity adjustment."""
        # High velocity field to trigger turbulence
        velocity_field = np.array([10.0, 10.0, 10.0])
        nu_adjusted, is_laminar = self.protocol.adjust_viscosity_laminar(
            velocity_field, time=0.0
        )
        
        self.assertFalse(is_laminar)
        self.assertGreater(self.protocol.data_flow_turbulence, 0.0)
        self.assertGreater(nu_adjusted, self.protocol.constants.NU_VISCOSITY)
    
    def test_viscosity_adjustment_factor(self):
        """Test that viscosity adjustment uses 1/7 factor."""
        velocity_field = np.array([15.0, 15.0, 15.0])
        nu_adjusted, is_laminar = self.protocol.adjust_viscosity_laminar(
            velocity_field, time=0.0
        )
        
        # Adjustment should involve the unification factor
        expected_min = self.protocol.constants.NU_VISCOSITY
        expected_max = expected_min * (1 + self.protocol.constants.UNIFICATION_FACTOR * 15)
        
        self.assertGreater(nu_adjusted, expected_min)
        self.assertLess(nu_adjusted, expected_max)


class TestEconomicCoupling(unittest.TestCase):
    """Test economic coupling with PSIX ledger."""
    
    def setUp(self):
        self.protocol = QCALSyncProtocol()
    
    def test_resonance_detection_exact(self):
        """Test exact resonance at 888.8 Hz."""
        at_resonance = self.protocol.check_resonance_peak(888.8)
        self.assertTrue(at_resonance)
        self.assertEqual(self.protocol.psix_ledger_pulses, 1)
    
    def test_resonance_detection_within_tolerance(self):
        """Test resonance detection within 1% tolerance."""
        # Within 1% of 888.8 Hz
        at_resonance = self.protocol.check_resonance_peak(888.8 + 8.0)  # ~0.9%
        self.assertTrue(at_resonance)
    
    def test_no_resonance_outside_tolerance(self):
        """Test no resonance outside tolerance."""
        initial_pulses = self.protocol.psix_ledger_pulses
        at_resonance = self.protocol.check_resonance_peak(800.0)
        self.assertFalse(at_resonance)
        # No new pulse should be sent
        self.assertEqual(self.protocol.psix_ledger_pulses, initial_pulses)
    
    def test_high_coherence_deflation(self):
        """Test deflation with high coherence."""
        self.protocol.coherence_score = 0.96
        initial_scarcity = self.protocol.token_scarcity
        
        self.protocol._send_psix_pulse()
        
        # Deflation should increase scarcity
        self.assertGreater(self.protocol.token_scarcity, initial_scarcity)
    
    def test_low_coherence_healing(self):
        """Test auto-healing with low coherence."""
        self.protocol.coherence_score = 0.65
        initial_scarcity = self.protocol.token_scarcity
        
        self.protocol._send_psix_pulse()
        
        # Healing should decrease scarcity (stabilization)
        self.assertLess(self.protocol.token_scarcity, initial_scarcity)
    
    def test_psix_pulse_increment(self):
        """Test that PSIX pulses increment correctly."""
        initial_pulses = self.protocol.psix_ledger_pulses
        
        self.protocol._send_psix_pulse()
        self.assertEqual(self.protocol.psix_ledger_pulses, initial_pulses + 1)
        
        self.protocol._send_psix_pulse()
        self.assertEqual(self.protocol.psix_ledger_pulses, initial_pulses + 2)


class TestPhaseValidation(unittest.TestCase):
    """Test phase validation across repositories."""
    
    def setUp(self):
        self.protocol = QCALSyncProtocol()
    
    def test_kappa_pi_exact_match(self):
        """Test exact κ_Π match validates."""
        is_valid = self.protocol.validate_kappa_pi_consistency(
            "formal/PsiNSE", 2.5773
        )
        self.assertTrue(is_valid)
        self.assertIn("formal/PsiNSE", self.protocol.validated_repos)
    
    def test_kappa_pi_within_tolerance(self):
        """Test κ_Π within tolerance validates."""
        is_valid = self.protocol.validate_kappa_pi_consistency(
            "src/oscillators", 2.57731  # Within 1e-4
        )
        self.assertTrue(is_valid)
    
    def test_kappa_pi_outside_tolerance(self):
        """Test κ_Π outside tolerance fails validation."""
        is_valid = self.protocol.validate_kappa_pi_consistency(
            "contracts/invalid", 2.58  # Too far off
        )
        self.assertFalse(is_valid)
        self.assertNotIn("contracts/invalid", self.protocol.validated_repos)
    
    def test_multiple_validations(self):
        """Test multiple repository validations."""
        self.protocol.validate_kappa_pi_consistency("repo1", 2.5773)
        self.protocol.validate_kappa_pi_consistency("repo2", 2.5773)
        self.protocol.validate_kappa_pi_consistency("repo3", 2.5773)
        
        self.assertEqual(len(self.protocol.validated_repos), 3)


class TestCoherenceComputation(unittest.TestCase):
    """Test coherence computation and noise handling."""
    
    def setUp(self):
        self.protocol = QCALSyncProtocol()
    
    def test_perfect_coherence_no_noise(self):
        """Test perfect coherence with no noise or turbulence."""
        self.protocol.data_flow_turbulence = 0.0
        psi = self.protocol.compute_coherence(noise_level=0.0)
        self.assertEqual(psi, 1.0)
    
    def test_coherence_with_noise(self):
        """Test coherence decreases with noise."""
        self.protocol.data_flow_turbulence = 0.0
        psi = self.protocol.compute_coherence(noise_level=0.5)
        
        # Should decrease due to noise penalty
        expected_penalty = 0.5 * self.protocol.constants.UNIFICATION_FACTOR
        expected_psi = 1.0 - expected_penalty
        self.assertAlmostEqual(psi, expected_psi, places=6)
    
    def test_coherence_with_turbulence(self):
        """Test coherence decreases with turbulence."""
        self.protocol.data_flow_turbulence = 1.0
        psi = self.protocol.compute_coherence(noise_level=0.0)
        
        expected_penalty = 1.0 * self.protocol.constants.UNIFICATION_FACTOR
        expected_psi = 1.0 - expected_penalty
        self.assertAlmostEqual(psi, expected_psi, places=6)
    
    def test_coherence_bounded(self):
        """Test coherence stays within [0, 1] bounds."""
        # Extreme noise and turbulence
        self.protocol.data_flow_turbulence = 10.0
        psi = self.protocol.compute_coherence(noise_level=10.0)
        
        self.assertGreaterEqual(psi, 0.0)
        self.assertLessEqual(psi, 1.0)
    
    def test_unification_factor_in_penalty(self):
        """Test that unification factor (1/7) affects penalty."""
        self.protocol.data_flow_turbulence = 0.0
        noise = 1.0
        psi = self.protocol.compute_coherence(noise_level=noise)
        
        # Penalty should be noise * (1/7)
        penalty = noise * (1/7)
        expected = 1.0 - penalty
        self.assertAlmostEqual(psi, expected, places=6)


class TestDashboard(unittest.TestCase):
    """Test dashboard generation."""
    
    def setUp(self):
        self.protocol = QCALSyncProtocol()
    
    def test_dashboard_generation(self):
        """Test that dashboard generates without errors."""
        dashboard = self.protocol.generate_dashboard()
        
        self.assertIsInstance(dashboard, str)
        self.assertIn("DASHBOARD DE EJECUCIÓN", dashboard)
        self.assertIn("QCAL-SYNC-1/7", dashboard)
    
    def test_dashboard_contains_frequencies(self):
        """Test dashboard contains all frequency components."""
        dashboard = self.protocol.generate_dashboard()
        
        self.assertIn("141.7001", dashboard)  # f₀
        self.assertIn("888.8", dashboard)     # f∞
        self.assertIn("2.5773", dashboard)    # κ_Π
        self.assertIn("1/7", dashboard)       # Unification factor
    
    def test_dashboard_shows_coherence(self):
        """Test dashboard displays coherence score."""
        self.protocol.coherence_score = 0.85
        dashboard = self.protocol.generate_dashboard()
        
        self.assertIn("0.850", dashboard)
    
    def test_dashboard_warning_low_coherence(self):
        """Test dashboard shows warning for low coherence."""
        self.protocol.coherence_score = 0.90
        dashboard = self.protocol.generate_dashboard()
        
        self.assertIn("Advertencia de Coherencia", dashboard)
        self.assertIn("ruido", dashboard)


class TestSynchronizationCycle(unittest.TestCase):
    """Test full synchronization cycle execution."""
    
    def setUp(self):
        self.protocol = QCALSyncProtocol()
    
    def test_cycle_execution(self):
        """Test synchronization cycle completes successfully."""
        metrics = self.protocol.run_synchronization_cycle(duration=0.5, dt=0.01)
        
        self.assertIsInstance(metrics, dict)
        self.assertIn('time', metrics)
        self.assertIn('coherence', metrics)
        self.assertIn('turbulence', metrics)
        self.assertIn('frequency', metrics)
    
    def test_cycle_produces_data(self):
        """Test cycle produces time series data."""
        metrics = self.protocol.run_synchronization_cycle(duration=0.5, dt=0.01)
        
        # Should have ~50 time points (0.5s / 0.01s)
        self.assertGreater(len(metrics['time']), 40)
        self.assertEqual(len(metrics['time']), len(metrics['coherence']))
        self.assertEqual(len(metrics['time']), len(metrics['turbulence']))
        self.assertEqual(len(metrics['time']), len(metrics['frequency']))
    
    def test_cycle_validates_repos(self):
        """Test cycle validates κ_Π in multiple locations."""
        initial_repos = len(self.protocol.validated_repos)
        self.protocol.run_synchronization_cycle(duration=0.1, dt=0.01)
        
        # Should have validated at least 3 repos
        self.assertGreaterEqual(len(self.protocol.validated_repos), 3)


class TestStateExport(unittest.TestCase):
    """Test state export functionality."""
    
    def setUp(self):
        self.protocol = QCALSyncProtocol()
        self.test_file = "/tmp/test_qcal_sync_state.json"
    
    def tearDown(self):
        if os.path.exists(self.test_file):
            os.remove(self.test_file)
    
    def test_export_creates_file(self):
        """Test that export creates JSON file."""
        self.protocol.export_sync_state(self.test_file)
        self.assertTrue(os.path.exists(self.test_file))
    
    def test_export_valid_json(self):
        """Test exported file is valid JSON."""
        self.protocol.export_sync_state(self.test_file)
        
        with open(self.test_file, 'r') as f:
            state = json.load(f)
        
        self.assertIsInstance(state, dict)
    
    def test_export_contains_required_fields(self):
        """Test exported state contains all required fields."""
        self.protocol.coherence_score = 0.95
        self.protocol.psix_ledger_pulses = 5
        self.protocol.export_sync_state(self.test_file)
        
        with open(self.test_file, 'r') as f:
            state = json.load(f)
        
        self.assertIn('unification_factor', state)
        self.assertIn('coherence_score', state)
        self.assertIn('psix_pulses', state)
        self.assertIn('constants', state)
        
        # Check constants
        self.assertEqual(state['constants']['f0'], 141.7001)
        self.assertEqual(state['constants']['f_resonance'], 888.8)
        self.assertEqual(state['constants']['kappa_pi'], 2.5773)
    
    def test_export_preserves_state(self):
        """Test exported state matches protocol state."""
        self.protocol.coherence_score = 0.88
        self.protocol.psix_ledger_pulses = 3
        self.protocol.token_scarcity = 1.25
        
        self.protocol.export_sync_state(self.test_file)
        
        with open(self.test_file, 'r') as f:
            state = json.load(f)
        
        self.assertEqual(state['coherence_score'], 0.88)
        self.assertEqual(state['psix_pulses'], 3)
        self.assertEqual(state['token_scarcity'], 1.25)


class TestSyncVector(unittest.TestCase):
    """Test SyncVector functionality."""
    
    def test_sync_vector_creation(self):
        """Test creating sync vectors."""
        protocol = QCALSyncProtocol()
        protocol.update_sync_vector(
            "test_component", 
            141.7001, 
            SyncState.STABLE,
            "Test synchronization"
        )
        
        self.assertEqual(len(protocol.sync_vectors), 1)
        vector = protocol.sync_vectors[0]
        self.assertEqual(vector.frequency_hz, 141.7001)
        self.assertEqual(vector.state, SyncState.STABLE)


def run_tests():
    """Run all tests and generate report."""
    print("="*80)
    print("  QCAL-SYNC-1/7 Protocol Test Suite")
    print("="*80)
    
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestProtocolConstants))
    suite.addTests(loader.loadTestsFromTestCase(TestNavierStokesSynchronization))
    suite.addTests(loader.loadTestsFromTestCase(TestEconomicCoupling))
    suite.addTests(loader.loadTestsFromTestCase(TestPhaseValidation))
    suite.addTests(loader.loadTestsFromTestCase(TestCoherenceComputation))
    suite.addTests(loader.loadTestsFromTestCase(TestDashboard))
    suite.addTests(loader.loadTestsFromTestCase(TestSynchronizationCycle))
    suite.addTests(loader.loadTestsFromTestCase(TestStateExport))
    suite.addTests(loader.loadTestsFromTestCase(TestSyncVector))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Print summary
    print("\n" + "="*80)
    print("  Test Summary")
    print("="*80)
    print(f"  Tests run: {result.testsRun}")
    print(f"  Successes: {result.testsRun - len(result.failures) - len(result.errors)}")
    print(f"  Failures: {len(result.failures)}")
    print(f"  Errors: {len(result.errors)}")
    print("="*80)
    
    return result.wasSuccessful()


if __name__ == "__main__":
    success = run_tests()
    exit(0 if success else 1)
