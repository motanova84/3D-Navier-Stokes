#!/usr/bin/env python3
"""
Tests for Haar Measure Navier-Stokes Kernel
"""

import unittest
import numpy as np
from qcal.haar_navier_stokes_kernel import (
    F0, DT, PRIMES_C7, RIEMANN_ZEROS_GAMMA,
    build_translation_matrix, verify_unitarity,
    HaarNavierStokesKernel,
    build_ramsey_hamiltonian_c7, align_ramsey_spectrum,
    sincronizar_gaps_b_c
)


class TestTranslationMatrix(unittest.TestCase):
    """Test suite for the translation matrix operator."""
    
    def test_build_translation_matrix_shape(self):
        """Translation matrix should have correct shape."""
        V = build_translation_matrix(7)
        self.assertEqual(V.shape, (7, 7))
    
    def test_translation_matrix_is_permutation(self):
        """Translation matrix should be a permutation matrix."""
        V = build_translation_matrix(7)
        # Each row and column should have exactly one 1
        self.assertTrue(np.allclose(np.sum(V, axis=0), 1))
        self.assertTrue(np.allclose(np.sum(V, axis=1), 1))
    
    def test_translation_matrix_cyclic(self):
        """V^7 should equal identity for C₇."""
        V = build_translation_matrix(7)
        V7 = np.linalg.matrix_power(V, 7)
        I = np.eye(7)
        self.assertTrue(np.allclose(V7, I))
    
    def test_verify_unitarity_determinant(self):
        """Translation matrix should have determinant 1."""
        V = build_translation_matrix(7)
        result = verify_unitarity(V)
        self.assertTrue(result["det_is_one"])
        self.assertAlmostEqual(result["determinant"], 1.0, places=10)
    
    def test_verify_unitarity_orthogonal(self):
        """Translation matrix should be orthogonal: V†V = I."""
        V = build_translation_matrix(7)
        result = verify_unitarity(V)
        self.assertTrue(result["orthogonal"])
    
    def test_verify_unitarity_isometry(self):
        """Translation matrix should preserve norms (isometry)."""
        V = build_translation_matrix(7)
        result = verify_unitarity(V)
        self.assertTrue(result["isometry"])
    
    def test_verify_unitarity_complete(self):
        """Translation matrix should pass all unitarity tests."""
        V = build_translation_matrix(7)
        result = verify_unitarity(V)
        self.assertTrue(result["unitarity_verified"])
        self.assertEqual(result["gap_b_status"], "UNITARIA 𓂀")


class TestHaarNavierStokesKernel(unittest.TestCase):
    """Test suite for the Haar-based Navier-Stokes kernel."""
    
    def setUp(self):
        """Set up test kernel."""
        self.kernel = HaarNavierStokesKernel(n_nodes=7, f0=F0)
    
    def test_kernel_initialization(self):
        """Kernel should initialize with correct parameters."""
        self.assertEqual(self.kernel.n_nodes, 7)
        self.assertEqual(self.kernel.f0, F0)
        self.assertAlmostEqual(self.kernel.dt, 1.0 / F0)
        self.assertTrue(self.kernel.unitarity["unitarity_verified"])
    
    def test_evolve_step_shape(self):
        """Evolve step should preserve state shape."""
        state = np.random.randn(7) + 1j * np.random.randn(7)
        new_state = self.kernel.evolve_step(state)
        self.assertEqual(new_state.shape, state.shape)
    
    def test_evolve_step_norm_conservation(self):
        """Evolve step should conserve norm (unitarity)."""
        state = np.random.randn(7) + 1j * np.random.randn(7)
        new_state = self.kernel.evolve_step(state)
        
        norm_initial = np.linalg.norm(state)
        norm_final = np.linalg.norm(new_state)
        
        self.assertAlmostEqual(norm_initial, norm_final, places=10)
    
    def test_evolve_multiple_steps(self):
        """Evolution should work for multiple steps."""
        state = np.ones(7, dtype=complex) / np.sqrt(7)
        n_steps = 10
        trajectory = self.kernel.evolve(state, n_steps)
        
        self.assertEqual(trajectory.shape, (n_steps + 1, 7))
    
    def test_evolve_periodicity(self):
        """Evolution should be periodic with period 7 for C₇."""
        state = np.random.randn(7) + 1j * np.random.randn(7)
        trajectory = self.kernel.evolve(state, n_steps=7)
        
        # After 7 steps, should return to initial state
        self.assertTrue(np.allclose(trajectory[0], trajectory[7]))
    
    def test_compute_energy(self):
        """Energy computation should match L² norm squared."""
        state = np.array([1, 2, 3, 4, 5, 6, 7], dtype=complex)
        energy = self.kernel.compute_energy(state)
        expected_energy = np.sum(np.abs(state)**2)
        
        self.assertAlmostEqual(energy, expected_energy)
    
    def test_energy_conservation(self):
        """Energy should be conserved during evolution."""
        state = np.ones(7, dtype=complex) / np.sqrt(7)
        result = self.kernel.verify_energy_conservation(state, n_steps=100)
        
        self.assertTrue(result["energy_conserved"])
        self.assertLess(result["max_deviation"], 1e-10)
        self.assertTrue(result["incompressible"])
        self.assertEqual(result["gap_b_status"], "SELLADA ✅")
    
    def test_energy_conservation_random_state(self):
        """Energy conservation should work for random initial states."""
        state = np.random.randn(7) + 1j * np.random.randn(7)
        result = self.kernel.verify_energy_conservation(state, n_steps=50)
        
        self.assertTrue(result["energy_conserved"])
        self.assertLess(result["max_deviation"], 1e-10)


class TestRamseyHamiltonian(unittest.TestCase):
    """Test suite for the Ramsey-Riemann Hamiltonian."""
    
    def test_build_hamiltonian_shape(self):
        """Hamiltonian should have correct shape."""
        H = build_ramsey_hamiltonian_c7()
        self.assertEqual(H.shape, (7, 7))
    
    def test_hamiltonian_hermitian(self):
        """Hamiltonian should be Hermitian: H = H†."""
        H = build_ramsey_hamiltonian_c7()
        self.assertTrue(np.allclose(H, H.conj().T))
    
    def test_hamiltonian_with_custom_zeros(self):
        """Hamiltonian should accept custom Riemann zeros."""
        custom_zeros = [10.0, 20.0, 30.0, 40.0, 50.0, 60.0, 70.0]
        H = build_ramsey_hamiltonian_c7(gamma_n=custom_zeros)
        self.assertEqual(H.shape, (7, 7))
    
    def test_hamiltonian_eigenvalues_real_part(self):
        """Hamiltonian eigenvalues should have real parts (energy levels)."""
        H = build_ramsey_hamiltonian_c7()
        eigenvalues = np.linalg.eigvals(H)
        
        # All eigenvalues should have non-zero real parts (site energies)
        for ev in eigenvalues:
            self.assertGreater(np.real(ev), 0)
    
    def test_align_ramsey_spectrum(self):
        """Spectrum alignment should check against target zeros."""
        H = build_ramsey_hamiltonian_c7()
        result = align_ramsey_spectrum(H, RIEMANN_ZEROS_GAMMA)
        
        self.assertIn("aligned", result)
        self.assertIn("eigenvalues", result)
        self.assertIn("gamma_computed", result)
        self.assertIn("alignment_error", result)
    
    def test_spectrum_alignment_error(self):
        """Alignment error should be computed correctly."""
        H = build_ramsey_hamiltonian_c7()
        result = align_ramsey_spectrum(H, RIEMANN_ZEROS_GAMMA)
        
        self.assertGreaterEqual(result["alignment_error"], 0)
        self.assertGreaterEqual(result["relative_error"], 0)


class TestGapSynchronization(unittest.TestCase):
    """Test suite for Gap B and Gap C synchronization."""
    
    def test_sincronizar_gaps_structure(self):
        """Synchronization should return complete system state."""
        result = sincronizar_gaps_b_c(n_steps=10)
        
        self.assertIn("frecuencia_maestra", result)
        self.assertIn("dt_sincronizado", result)
        self.assertIn("gap_b", result)
        self.assertIn("gap_c", result)
        self.assertIn("sistema_completo", result)
    
    def test_sincronizar_gaps_frequency(self):
        """Synchronization should use correct frequency."""
        result = sincronizar_gaps_b_c(n_steps=10)
        
        self.assertEqual(result["frecuencia_maestra"], F0)
        self.assertAlmostEqual(result["dt_sincronizado"], 1.0 / F0)
    
    def test_gap_b_unitarity(self):
        """Gap B should verify unitarity and energy conservation."""
        result = sincronizar_gaps_b_c(n_steps=50)
        
        self.assertTrue(result["gap_b"]["unitariedad_verificada"])
        self.assertTrue(result["gap_b"]["energia_conservada"])
        self.assertLess(result["gap_b"]["desviacion_energia"], 1e-10)
    
    def test_gap_c_resonance(self):
        """Gap C should check spectral alignment."""
        result = sincronizar_gaps_b_c(n_steps=50)
        
        self.assertIn("espectro_alineado", result["gap_c"])
        self.assertIn("error_alineacion", result["gap_c"])
    
    def test_sistema_completo(self):
        """Complete system should report closure status."""
        result = sincronizar_gaps_b_c(n_steps=50)
        
        self.assertIn("gaps_cerrados", result["sistema_completo"])
        self.assertIn("estado", result["sistema_completo"])
        self.assertIn("mecanismo_cierre", result["sistema_completo"])
        self.assertIn("latido", result["sistema_completo"])


class TestConstants(unittest.TestCase):
    """Test suite for module constants."""
    
    def test_f0_value(self):
        """F0 should be the canonical QCAL frequency."""
        self.assertAlmostEqual(F0, 141.7001, places=4)
    
    def test_dt_value(self):
        """DT should be the reciprocal of F0."""
        self.assertAlmostEqual(DT, 1.0 / F0)
        self.assertAlmostEqual(DT * 1000, 7.057, places=2)  # ~7.06 ms
    
    def test_primes_c7(self):
        """PRIMES_C7 should contain the first 7 primes."""
        self.assertEqual(PRIMES_C7, [2, 3, 5, 7, 11, 13, 17])
    
    def test_riemann_zeros_length(self):
        """RIEMANN_ZEROS_GAMMA should have at least 7 zeros."""
        self.assertGreaterEqual(len(RIEMANN_ZEROS_GAMMA), 7)
    
    def test_riemann_zeros_sorted(self):
        """Riemann zeros should be in ascending order."""
        for i in range(len(RIEMANN_ZEROS_GAMMA) - 1):
            self.assertLess(RIEMANN_ZEROS_GAMMA[i], RIEMANN_ZEROS_GAMMA[i + 1])


class TestPhysicalInterpretation(unittest.TestCase):
    """Test suite for physical interpretation and consistency."""
    
    def test_incompressibility_from_unitarity(self):
        """Unitarity should imply incompressibility."""
        kernel = HaarNavierStokesKernel(n_nodes=7)
        state = np.ones(7, dtype=complex) / np.sqrt(7)
        
        result = kernel.verify_energy_conservation(state, n_steps=20)
        
        # If energy is conserved, fluid is incompressible
        self.assertEqual(
            result["energy_conserved"],
            result["incompressible"]
        )
    
    def test_synchronization_with_f0(self):
        """Each discrete step should occur at frequency f0."""
        kernel = HaarNavierStokesKernel(n_nodes=7)
        
        # dt * f0 = 1 cycle
        self.assertAlmostEqual(kernel.dt * kernel.f0, 1.0)
    
    def test_seven_node_topology(self):
        """System should have 7-node heptagon topology."""
        kernel = HaarNavierStokesKernel(n_nodes=7)
        
        self.assertEqual(kernel.n_nodes, 7)
        self.assertEqual(len(PRIMES_C7), 7)
        
        # Verify cyclic structure
        state = np.array([1, 0, 0, 0, 0, 0, 0], dtype=complex)
        trajectory = kernel.evolve(state, n_steps=7)
        
        # After 7 steps, should return to initial position
        self.assertTrue(np.allclose(trajectory[0], trajectory[7]))


class TestNumericalStability(unittest.TestCase):
    """Test suite for numerical stability."""
    
    def test_long_evolution_stability(self):
        """Long evolution should remain stable."""
        kernel = HaarNavierStokesKernel(n_nodes=7)
        state = np.ones(7, dtype=complex) / np.sqrt(7)
        
        # Evolve for many steps
        result = kernel.verify_energy_conservation(state, n_steps=1000)
        
        # Energy should still be conserved
        self.assertTrue(result["energy_conserved"])
        self.assertLess(result["max_deviation"], 1e-9)
    
    def test_large_amplitude_state(self):
        """Large amplitude states should be handled correctly."""
        kernel = HaarNavierStokesKernel(n_nodes=7)
        state = np.ones(7, dtype=complex) * 1000.0
        
        E0 = kernel.compute_energy(state)
        new_state = kernel.evolve_step(state)
        E1 = kernel.compute_energy(new_state)
        
        self.assertAlmostEqual(E0, E1, places=5)
    
    def test_small_amplitude_state(self):
        """Small amplitude states should be handled correctly."""
        kernel = HaarNavierStokesKernel(n_nodes=7)
        state = np.ones(7, dtype=complex) * 1e-10
        
        E0 = kernel.compute_energy(state)
        new_state = kernel.evolve_step(state)
        E1 = kernel.compute_energy(new_state)
        
        self.assertAlmostEqual(E0, E1, places=15)


def run_tests():
    """Run all tests and display results."""
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestTranslationMatrix))
    suite.addTests(loader.loadTestsFromTestCase(TestHaarNavierStokesKernel))
    suite.addTests(loader.loadTestsFromTestCase(TestRamseyHamiltonian))
    suite.addTests(loader.loadTestsFromTestCase(TestGapSynchronization))
    suite.addTests(loader.loadTestsFromTestCase(TestConstants))
    suite.addTests(loader.loadTestsFromTestCase(TestPhysicalInterpretation))
    suite.addTests(loader.loadTestsFromTestCase(TestNumericalStability))
    
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    return result.wasSuccessful()


if __name__ == "__main__":
    success = run_tests()
    exit(0 if success else 1)
