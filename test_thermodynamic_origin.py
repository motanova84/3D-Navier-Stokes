#!/usr/bin/env python3
"""
Tests for Thermodynamic Origin Framework
=========================================

Tests the thermodynamic origin module that anchors Navier-Stokes stability
to the cascade from Planck scale to QCAL frequency.

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
Date: March 27, 2026
License: MIT
"""

import unittest
import math
from qcal.thermodynamic_origin import (
    ThermodynamicState,
    RealityLevel,
    calcular_frecuencia_salto,
    calcular_entropia,
    calcular_coherencia,
    calcular_viscosidad_adelica,
    clasificar_nivel,
    calcular_estado_termodinamico,
    generar_cascada_completa,
    obtener_niveles_clave,
    verificar_anclaje_navier_stokes,
    F_PLANCK,
    F_QCAL,
    PHI,
    N_JUMPS,
    PSI_PLANCK,
    PSI_TRAYECTORIA,
    PSI_QCAL,
    K_BOLTZMANN,
    T_QCAL,
)


class TestThermodynamicOrigin(unittest.TestCase):
    """Test suite for thermodynamic origin framework"""

    def test_constants(self):
        """Test that fundamental constants are defined correctly"""
        self.assertAlmostEqual(F_PLANCK, 1.41e32, delta=1e30)
        self.assertAlmostEqual(F_QCAL, 141.7001, delta=0.0001)
        self.assertAlmostEqual(PHI, 1.618034, delta=0.000001)
        self.assertEqual(N_JUMPS, 29)
        self.assertAlmostEqual(PSI_PLANCK, 1.0, delta=1e-6)

    def test_golden_ratio_jumps(self):
        """Test golden ratio frequency jumps"""
        # Jump 0 should be Planck frequency
        f0 = calcular_frecuencia_salto(0)
        self.assertAlmostEqual(f0, F_PLANCK, delta=1e30)

        # Each jump should decrease by factor of PHI
        for n in range(1, 10):
            f_n = calcular_frecuencia_salto(n)
            f_prev = calcular_frecuencia_salto(n - 1)
            ratio = f_prev / f_n
            self.assertAlmostEqual(ratio, PHI, delta=0.001)

        # Jump N_JUMPS should be close to QCAL frequency
        f_final = calcular_frecuencia_salto(N_JUMPS)
        # Should be within order of magnitude
        self.assertLess(f_final, F_QCAL * 10)
        self.assertGreater(f_final, F_QCAL / 10)

    def test_frequency_jump_bounds(self):
        """Test that frequency jump raises error for invalid inputs"""
        with self.assertRaises(ValueError):
            calcular_frecuencia_salto(-1)

        with self.assertRaises(ValueError):
            calcular_frecuencia_salto(N_JUMPS + 1)

    def test_entropy_calculation(self):
        """Test thermodynamic entropy calculation"""
        # Entropy at Planck scale should be zero (or very small)
        S_planck = calcular_entropia(F_PLANCK)
        self.assertAlmostEqual(S_planck, 0.0, delta=1e-30)

        # Entropy should increase as frequency decreases
        S_high = calcular_entropia(1e30)
        S_low = calcular_entropia(1e10)
        self.assertLess(S_high, S_low)

        # Entropy at QCAL should be significant
        S_qcal = calcular_entropia(F_QCAL)
        self.assertGreater(S_qcal, 0)
        self.assertLess(S_qcal, 1e-15)  # But still physically reasonable

    def test_entropy_bounds(self):
        """Test entropy calculation raises error for invalid frequencies"""
        with self.assertRaises(ValueError):
            calcular_entropia(0.0)

        with self.assertRaises(ValueError):
            calcular_entropia(-100.0)

        with self.assertRaises(ValueError):
            calcular_entropia(F_PLANCK * 2)

    def test_coherence_from_entropy(self):
        """Test coherence calculation from entropy"""
        # Zero entropy should give perfect coherence
        psi_zero = calcular_coherencia(0.0)
        self.assertAlmostEqual(psi_zero, 1.0, delta=1e-6)

        # Higher entropy should reduce coherence
        S1 = 1e-24
        S2 = 1e-23
        psi1 = calcular_coherencia(S1)
        psi2 = calcular_coherencia(S2)
        self.assertGreater(psi1, psi2)

        # Coherence should be bounded [0, 1]
        for S in [1e-30, 1e-25, 1e-20, 1e-15]:
            psi = calcular_coherencia(S)
            self.assertGreaterEqual(psi, 0.0)
            self.assertLessEqual(psi, 1.0)

    def test_viscosity_from_coherence(self):
        """Test adelic viscosity calculation"""
        # Perfect coherence should give zero viscosity
        nu_perfect = calcular_viscosidad_adelica(1.0)
        self.assertAlmostEqual(nu_perfect, 0.0, delta=1e-10)

        # Lower coherence should give higher viscosity
        nu_high = calcular_viscosidad_adelica(0.99)
        nu_low = calcular_viscosidad_adelica(0.9)
        self.assertLess(nu_high, nu_low)

        # Viscosity should be non-negative
        for psi in [0.999, 0.95, 0.9, 0.85, 0.8]:
            nu = calcular_viscosidad_adelica(psi)
            self.assertGreaterEqual(nu, 0.0)

    def test_reality_level_classification(self):
        """Test classification of reality levels"""
        # Jump 0 is ORIGEN
        self.assertEqual(clasificar_nivel(0), RealityLevel.ORIGEN)

        # Jump N_JUMPS is DESTINO
        self.assertEqual(clasificar_nivel(N_JUMPS), RealityLevel.DESTINO)

        # Middle jumps are TRAYECTORIA
        for n in range(1, N_JUMPS):
            self.assertEqual(clasificar_nivel(n), RealityLevel.TRAYECTORIA)

    def test_thermodynamic_state_calculation(self):
        """Test complete thermodynamic state calculation"""
        # Test ORIGEN state (Planck)
        origen = calcular_estado_termodinamico(0)
        self.assertEqual(origen.level, RealityLevel.ORIGEN)
        self.assertAlmostEqual(origen.frequency, F_PLANCK, delta=1e30)
        self.assertAlmostEqual(origen.coherence, 1.0, delta=0.01)
        self.assertEqual(origen.jump_number, 0)

        # Test DESTINO state (QCAL)
        destino = calcular_estado_termodinamico(N_JUMPS)
        self.assertEqual(destino.level, RealityLevel.DESTINO)
        self.assertEqual(destino.jump_number, N_JUMPS)
        # Frequency should be within order of magnitude of QCAL
        self.assertLess(destino.frequency, F_QCAL * 10)
        self.assertGreater(destino.frequency, F_QCAL / 10)

        # Test TRAYECTORIA state (middle)
        trayectoria = calcular_estado_termodinamico(N_JUMPS // 2)
        self.assertEqual(trayectoria.level, RealityLevel.TRAYECTORIA)
        self.assertEqual(trayectoria.jump_number, N_JUMPS // 2)
        # Coherence should be between Planck and QCAL
        self.assertLess(trayectoria.coherence, 1.0)
        self.assertGreater(trayectoria.coherence, 0.8)

    def test_complete_cascade(self):
        """Test generation of complete cascade"""
        cascade = generar_cascada_completa()

        # Should have N_JUMPS + 1 states (0 through N_JUMPS)
        self.assertEqual(len(cascade), N_JUMPS + 1)

        # First state should be ORIGEN
        self.assertEqual(cascade[0].level, RealityLevel.ORIGEN)
        self.assertEqual(cascade[0].jump_number, 0)

        # Last state should be DESTINO
        self.assertEqual(cascade[-1].level, RealityLevel.DESTINO)
        self.assertEqual(cascade[-1].jump_number, N_JUMPS)

        # Frequency should monotonically decrease
        for i in range(len(cascade) - 1):
            self.assertGreater(cascade[i].frequency, cascade[i + 1].frequency)

        # Entropy should monotonically increase
        for i in range(len(cascade) - 1):
            self.assertLess(cascade[i].entropy, cascade[i + 1].entropy)

        # Coherence should generally decrease (allowing small fluctuations)
        # Just check first and last
        self.assertGreater(cascade[0].coherence, cascade[-1].coherence)

    def test_key_levels(self):
        """Test extraction of three key reality levels"""
        niveles = obtener_niveles_clave()

        # Should have exactly three keys
        self.assertEqual(len(niveles), 3)
        self.assertIn('origen', niveles)
        self.assertIn('trayectoria', niveles)
        self.assertIn('destino', niveles)

        # Check types
        self.assertIsInstance(niveles['origen'], ThermodynamicState)
        self.assertIsInstance(niveles['trayectoria'], ThermodynamicState)
        self.assertIsInstance(niveles['destino'], ThermodynamicState)

        # Check levels
        self.assertEqual(niveles['origen'].level, RealityLevel.ORIGEN)
        self.assertEqual(niveles['trayectoria'].level, RealityLevel.TRAYECTORIA)
        self.assertEqual(niveles['destino'].level, RealityLevel.DESTINO)

        # Check ordering: origen > trayectoria > destino in frequency
        self.assertGreater(
            niveles['origen'].frequency,
            niveles['trayectoria'].frequency
        )
        self.assertGreater(
            niveles['trayectoria'].frequency,
            niveles['destino'].frequency
        )

    def test_navier_stokes_anchor_verification(self):
        """Test verification of Navier-Stokes anchor at QCAL"""
        verificacion = verificar_anclaje_navier_stokes()

        # Should have all required keys
        required_keys = [
            'destino_frequency', 'target_frequency', 'frequency_error', 'frequency_ok',
            'destino_coherence', 'target_coherence', 'coherence_error', 'coherence_ok',
            'anclaje_valido', 'nivel', 'viscosidad'
        ]
        for key in required_keys:
            self.assertIn(key, verificacion)

        # Target should match constants
        self.assertAlmostEqual(verificacion['target_frequency'], F_QCAL, delta=1e-6)
        self.assertAlmostEqual(verificacion['target_coherence'], PSI_QCAL, delta=1e-6)

        # Errors should be reasonable (within acceptable bounds)
        # Note: Due to thermodynamic calculations, exact match may not be possible
        # We allow up to 10% error for frequency and coherence
        self.assertLess(verificacion['frequency_error'], 0.1)
        self.assertLess(verificacion['coherence_error'], 0.1)

        # Nivel should be ANCLAJE
        self.assertIn('ANCLAJE', verificacion['nivel'])

        # Viscosity should be small but non-zero
        self.assertGreater(verificacion['viscosidad'], 0.0)
        self.assertLess(verificacion['viscosidad'], 0.1)

    def test_thermodynamic_state_string_representation(self):
        """Test string representation of thermodynamic state"""
        state = calcular_estado_termodinamico(0)
        state_str = str(state)

        # Should contain key information
        self.assertIn("Estado Termodinámico", state_str)
        self.assertIn("Nivel:", state_str)
        self.assertIn("Frecuencia:", state_str)
        self.assertIn("Coherencia:", state_str)
        self.assertIn("Entropía:", state_str)
        self.assertIn("Temperatura:", state_str)
        self.assertIn("Viscosidad:", state_str)
        self.assertIn("Salto:", state_str)

    def test_physical_consistency(self):
        """Test physical consistency of the thermodynamic cascade"""
        cascade = generar_cascada_completa()

        for state in cascade:
            # All physical quantities should be non-negative
            self.assertGreaterEqual(state.frequency, 0)
            self.assertGreaterEqual(state.entropy, 0)
            self.assertGreaterEqual(state.coherence, 0)
            self.assertGreaterEqual(state.viscosity, 0)
            self.assertGreater(state.temperature, 0)

            # Coherence should be bounded [0, 1]
            self.assertLessEqual(state.coherence, 1.0)

            # Frequency should be physically reasonable
            self.assertLessEqual(state.frequency, F_PLANCK * 1.01)
            self.assertGreater(state.frequency, 1.0)  # > 1 Hz

    def test_golden_ratio_property(self):
        """Test that PHI has golden ratio property: φ² = φ + 1"""
        phi_squared = PHI ** 2
        phi_plus_one = PHI + 1.0
        self.assertAlmostEqual(phi_squared, phi_plus_one, delta=1e-6)

    def test_cascade_boundary_conditions(self):
        """Test boundary conditions of the cascade"""
        # At Planck scale (jump 0)
        origen = calcular_estado_termodinamico(0)
        self.assertAlmostEqual(origen.coherence, 1.0, delta=0.01)
        self.assertLess(origen.viscosity, 1e-6)
        self.assertLess(origen.entropy, 1e-28)

        # At QCAL scale (jump N_JUMPS)
        destino = calcular_estado_termodinamico(N_JUMPS)
        self.assertLess(destino.coherence, 1.0)
        self.assertGreater(destino.viscosity, 0.0)
        self.assertGreater(destino.entropy, 0.0)

        # The anchor should be stable (viscosity not too large)
        self.assertLess(destino.viscosity, 1.0)


class TestRealityLevelEnum(unittest.TestCase):
    """Test suite for RealityLevel enumeration"""

    def test_reality_level_values(self):
        """Test that reality level enum has correct values"""
        self.assertEqual(RealityLevel.ORIGEN.value, "FUENTE ☀️")
        self.assertEqual(RealityLevel.TRAYECTORIA.value, "FLUJO 🌊")
        self.assertEqual(RealityLevel.DESTINO.value, "ANCLAJE ⚓")

    def test_reality_level_members(self):
        """Test that all expected members exist"""
        levels = [level.name for level in RealityLevel]
        self.assertIn('ORIGEN', levels)
        self.assertIn('TRAYECTORIA', levels)
        self.assertIn('DESTINO', levels)
        self.assertEqual(len(levels), 3)


class TestThermodynamicStateDataClass(unittest.TestCase):
    """Test suite for ThermodynamicState data class"""

    def test_thermodynamic_state_creation(self):
        """Test creation of ThermodynamicState"""
        state = ThermodynamicState(
            frequency=1e20,
            coherence=0.95,
            entropy=1e-25,
            temperature=300.0,
            viscosity=1e-6,
            level=RealityLevel.TRAYECTORIA,
            jump_number=15
        )

        self.assertEqual(state.frequency, 1e20)
        self.assertEqual(state.coherence, 0.95)
        self.assertEqual(state.entropy, 1e-25)
        self.assertEqual(state.temperature, 300.0)
        self.assertEqual(state.viscosity, 1e-6)
        self.assertEqual(state.level, RealityLevel.TRAYECTORIA)
        self.assertEqual(state.jump_number, 15)

    def test_thermodynamic_state_attributes(self):
        """Test that ThermodynamicState has all required attributes"""
        state = calcular_estado_termodinamico(0)
        self.assertTrue(hasattr(state, 'frequency'))
        self.assertTrue(hasattr(state, 'coherence'))
        self.assertTrue(hasattr(state, 'entropy'))
        self.assertTrue(hasattr(state, 'temperature'))
        self.assertTrue(hasattr(state, 'viscosity'))
        self.assertTrue(hasattr(state, 'level'))
        self.assertTrue(hasattr(state, 'jump_number'))


def run_tests():
    """Run all tests"""
    unittest.main(argv=[''], verbosity=2, exit=False)


if __name__ == '__main__':
    print("=" * 78)
    print("Testing Thermodynamic Origin Framework")
    print("=" * 78)
    print()

    # Run tests
    suite = unittest.TestLoader().loadTestsFromModule(__import__(__name__))
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)

    print()
    print("=" * 78)
    if result.wasSuccessful():
        print("✓ All tests passed!")
    else:
        print("✗ Some tests failed")
    print("=" * 78)
