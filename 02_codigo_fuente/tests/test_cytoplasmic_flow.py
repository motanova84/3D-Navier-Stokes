#!/usr/bin/env python3
"""
Comprehensive Tests for Cytoplasmic Flow Model
==============================================

Tests para verificar:
1. Cálculo del número de Reynolds
2. Regímenes de flujo (viscoso, laminar, turbulento)
3. Existencia de soluciones suaves
4. Operador hermítico de Hilbert-Pólya
5. Eigenfrequencias y resonancia
6. Conexión con la hipótesis de Riemann

Author: José Manuel Mota Burruezo
Date: 31 de enero de 2026
"""

import sys
import os
import unittest
import numpy as np

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'teoria_principal'))

from cytoplasmic_flow_model import (
    CytoplasmicFlowModel,
    CytoplasmaParams
)


class TestCytoplasmaParams(unittest.TestCase):
    """Test CytoplasmaParams dataclass"""
    
    def test_default_params(self):
        """Test default parameter values"""
        params = CytoplasmaParams()
        
        self.assertEqual(params.density, 1000.0)
        self.assertEqual(params.kinematic_viscosity, 1e-6)
        self.assertEqual(params.cell_scale, 1e-6)
        self.assertEqual(params.flow_velocity, 1e-8)
    
    def test_custom_params(self):
        """Test custom parameter values"""
        params = CytoplasmaParams(
            density=1100.0,
            kinematic_viscosity=2e-6,
            cell_scale=2e-6,
            flow_velocity=2e-8
        )
        
        self.assertEqual(params.density, 1100.0)
        self.assertEqual(params.kinematic_viscosity, 2e-6)
        self.assertEqual(params.cell_scale, 2e-6)
        self.assertEqual(params.flow_velocity, 2e-8)
    
    def test_invalid_density(self):
        """Test that negative density raises error"""
        with self.assertRaises(ValueError):
            CytoplasmaParams(density=-1000.0)
    
    def test_invalid_viscosity(self):
        """Test that negative viscosity raises error"""
        with self.assertRaises(ValueError):
            CytoplasmaParams(kinematic_viscosity=-1e-6)
    
    def test_invalid_scale(self):
        """Test that negative scale raises error"""
        with self.assertRaises(ValueError):
            CytoplasmaParams(cell_scale=-1e-6)
    
    def test_invalid_velocity(self):
        """Test that negative velocity raises error"""
        with self.assertRaises(ValueError):
            CytoplasmaParams(flow_velocity=-1e-8)


class TestReynoldsNumber(unittest.TestCase):
    """Test Reynolds number calculations"""
    
    def test_default_reynolds(self):
        """Test Reynolds number with default params"""
        model = CytoplasmicFlowModel()
        Re = model.get_reynolds_number()
        
        # Re = (1e-8 * 1e-6) / 1e-6 = 1e-8
        self.assertAlmostEqual(Re, 1e-8, places=15)
    
    def test_viscous_regime_reynolds(self):
        """Test Reynolds number in viscous regime"""
        params = CytoplasmaParams(flow_velocity=1e-9)
        model = CytoplasmicFlowModel(params)
        Re = model.get_reynolds_number()
        
        # Should be very small
        self.assertLess(Re, 0.1)
        self.assertTrue(model.is_viscous_regime())
    
    def test_laminar_regime_reynolds(self):
        """Test Reynolds number in laminar regime"""
        params = CytoplasmaParams(flow_velocity=1e-2, cell_scale=1e-4)
        model = CytoplasmicFlowModel(params)
        Re = model.get_reynolds_number()
        
        # Re = (1e-2 * 1e-4) / 1e-6 = 10
        self.assertGreater(Re, 1)
        self.assertLess(Re, 100)
        self.assertFalse(model.is_viscous_regime())
    
    def test_turbulent_regime_reynolds(self):
        """Test Reynolds number in turbulent regime"""
        params = CytoplasmaParams(flow_velocity=2.5, cell_scale=1e-3)
        model = CytoplasmicFlowModel(params)
        Re = model.get_reynolds_number()
        
        # Re = (2.5 * 1e-3) / 1e-6 = 2500
        self.assertGreater(Re, 2300)
        self.assertFalse(model.is_viscous_regime())


class TestFlowRegime(unittest.TestCase):
    """Test flow regime classification"""
    
    def test_completely_viscous_regime(self):
        """Test completely viscous (Stokes) regime"""
        model = CytoplasmicFlowModel()
        regime = model.get_flow_regime()
        
        self.assertEqual(regime, "COMPLETAMENTE VISCOSO - Stokes flow")
        self.assertTrue(model.is_viscous_regime())
    
    def test_viscous_regime(self):
        """Test viscous (creeping) regime"""
        params = CytoplasmaParams(flow_velocity=1e-5, cell_scale=1e-5)
        model = CytoplasmicFlowModel(params)
        regime = model.get_flow_regime()
        
        # Re = (1e-5 * 1e-5) / 1e-6 = 0.0001
        self.assertEqual(regime, "VISCOSO - Creeping flow")
    
    def test_laminar_regime(self):
        """Test laminar regime"""
        params = CytoplasmaParams(flow_velocity=1e-2, cell_scale=1e-4)
        model = CytoplasmicFlowModel(params)
        regime = model.get_flow_regime()
        
        # Re = (1e-2 * 1e-4) / 1e-6 = 10
        self.assertEqual(regime, "LAMINAR - Flujo laminar")
    
    def test_transition_regime(self):
        """Test transition regime"""
        params = CytoplasmaParams(flow_velocity=1.5, cell_scale=1e-3)
        model = CytoplasmicFlowModel(params)
        regime = model.get_flow_regime()
        
        # Re = (1.5 * 1e-3) / 1e-6 = 1500
        self.assertEqual(regime, "TRANSICIÓN - Posible turbulencia")
    
    def test_turbulent_regime(self):
        """Test turbulent regime"""
        params = CytoplasmaParams(flow_velocity=2.5, cell_scale=1e-3)
        model = CytoplasmicFlowModel(params)
        regime = model.get_flow_regime()
        
        # Re = (2.5 * 1e-3) / 1e-6 = 2500
        self.assertEqual(regime, "TURBULENTO - Régimen turbulento")


class TestSmoothSolution(unittest.TestCase):
    """Test smooth solution existence"""
    
    def test_smooth_solution_in_viscous_regime(self):
        """Test that smooth solution exists in viscous regime"""
        model = CytoplasmicFlowModel()
        
        self.assertTrue(model.has_smooth_solution())
        self.assertTrue(model.is_viscous_regime())
    
    def test_no_smooth_solution_in_turbulent_regime(self):
        """Test that smooth solution may not exist in turbulent regime"""
        params = CytoplasmaParams(flow_velocity=2.5, cell_scale=1e-3)
        model = CytoplasmicFlowModel(params)
        
        # In turbulent regime, we cannot guarantee smooth solution
        self.assertFalse(model.has_smooth_solution())
        self.assertFalse(model.is_viscous_regime())


class TestFlowCoherence(unittest.TestCase):
    """Test flow coherence calculations"""
    
    def test_coherence_in_viscous_regime(self):
        """Test that coherence is very low in viscous regime"""
        model = CytoplasmicFlowModel()
        coherence = model.get_flow_coherence()
        
        # In viscous regime, coherence should be very close to 0
        self.assertLess(coherence, 0.01)
        self.assertGreaterEqual(coherence, 0.0)
    
    def test_coherence_increases_with_reynolds(self):
        """Test that coherence increases with Reynolds number"""
        model1 = CytoplasmicFlowModel(CytoplasmaParams(flow_velocity=1e-8))
        model2 = CytoplasmicFlowModel(CytoplasmaParams(flow_velocity=1e-7))
        model3 = CytoplasmicFlowModel(CytoplasmaParams(flow_velocity=1e-6))
        
        c1 = model1.get_flow_coherence()
        c2 = model2.get_flow_coherence()
        c3 = model3.get_flow_coherence()
        
        # Coherence should increase with Reynolds
        self.assertLess(c1, c2)
        self.assertLess(c2, c3)
    
    def test_coherence_bounds(self):
        """Test that coherence is always between 0 and 1"""
        velocities = [1e-10, 1e-8, 1e-6, 1e-4, 1e-2, 1e0]
        
        for v in velocities:
            model = CytoplasmicFlowModel(CytoplasmaParams(flow_velocity=v))
            coherence = model.get_flow_coherence()
            
            self.assertGreaterEqual(coherence, 0.0)
            self.assertLessEqual(coherence, 1.0)


class TestHilbertPolyaOperator(unittest.TestCase):
    """Test Hilbert-Pólya operator properties"""
    
    def test_operator_exists_in_viscous_regime(self):
        """Test that Hilbert-Pólya operator exists in viscous regime"""
        model = CytoplasmicFlowModel()
        
        self.assertTrue(model.hilbert_polya_operator_exists())
        self.assertTrue(model.is_hermitian())
    
    def test_operator_does_not_exist_in_turbulent_regime(self):
        """Test that operator may not exist in turbulent regime"""
        params = CytoplasmaParams(flow_velocity=2.5, cell_scale=1e-3)
        model = CytoplasmicFlowModel(params)
        
        self.assertFalse(model.hilbert_polya_operator_exists())
        self.assertFalse(model.is_hermitian())
    
    def test_physical_medium(self):
        """Test physical medium description"""
        model = CytoplasmicFlowModel()
        medium = model.get_physical_medium()
        
        self.assertEqual(medium, "TEJIDO BIOLÓGICO VIVO (citoplasma)")
    
    def test_physical_medium_turbulent(self):
        """Test physical medium in turbulent regime"""
        params = CytoplasmaParams(flow_velocity=2.5, cell_scale=1e-3)
        model = CytoplasmicFlowModel(params)
        medium = model.get_physical_medium()
        
        self.assertEqual(medium, "No aplicable (régimen turbulento)")


class TestEigenfrequencies(unittest.TestCase):
    """Test eigenfrequency calculations"""
    
    def test_fundamental_frequency(self):
        """Test fundamental frequency value"""
        model = CytoplasmicFlowModel()
        f0 = model.get_fundamental_frequency()
        
        self.assertAlmostEqual(f0, 141.7001, places=4)
    
    def test_eigenfrequencies_count(self):
        """Test that correct number of eigenfrequencies are returned"""
        model = CytoplasmicFlowModel()
        
        for n in [1, 3, 5, 10, 20]:
            eigenfreqs = model.get_eigenfrequencies(n)
            self.assertEqual(len(eigenfreqs), n)
    
    def test_eigenfrequencies_increasing(self):
        """Test that eigenfrequencies are increasing"""
        model = CytoplasmicFlowModel()
        eigenfreqs = model.get_eigenfrequencies(10)
        
        for i in range(len(eigenfreqs) - 1):
            self.assertLess(eigenfreqs[i], eigenfreqs[i+1])
    
    def test_eigenfrequencies_positive(self):
        """Test that all eigenfrequencies are positive"""
        model = CytoplasmicFlowModel()
        eigenfreqs = model.get_eigenfrequencies(10)
        
        for freq in eigenfreqs:
            self.assertGreater(freq, 0)
    
    def test_first_eigenfrequency_is_fundamental(self):
        """Test that first eigenfrequency equals fundamental"""
        model = CytoplasmicFlowModel()
        eigenfreqs = model.get_eigenfrequencies(5)
        f0 = model.get_fundamental_frequency()
        
        self.assertAlmostEqual(eigenfreqs[0], f0, places=4)
    
    def test_eigenfrequencies_values(self):
        """Test specific eigenfrequency values"""
        model = CytoplasmicFlowModel()
        eigenfreqs = model.get_eigenfrequencies(5)
        
        # Check approximate values from expected output
        self.assertAlmostEqual(eigenfreqs[0], 141.7001, places=1)
        self.assertAlmostEqual(eigenfreqs[1], 210.69, places=0)
        self.assertAlmostEqual(eigenfreqs[2], 250.69, places=0)
        self.assertAlmostEqual(eigenfreqs[3], 305.00, places=0)
        self.assertAlmostEqual(eigenfreqs[4], 330.06, places=0)


class TestRiemannConnection(unittest.TestCase):
    """Test connection to Riemann Hypothesis"""
    
    def test_riemann_proven_in_viscous_regime(self):
        """Test that Riemann condition is satisfied in viscous regime"""
        model = CytoplasmicFlowModel()
        
        self.assertTrue(model.riemann_hypothesis_proven_in_biology())
    
    def test_riemann_not_proven_in_turbulent_regime(self):
        """Test that Riemann condition is not satisfied in turbulent regime"""
        params = CytoplasmaParams(flow_velocity=2.5, cell_scale=1e-3)
        model = CytoplasmicFlowModel(params)
        
        self.assertFalse(model.riemann_hypothesis_proven_in_biology())
    
    def test_riemann_requires_hermitian(self):
        """Test that Riemann proof requires hermitian operator"""
        model1 = CytoplasmicFlowModel()
        model2 = CytoplasmicFlowModel(CytoplasmaParams(flow_velocity=2.5, cell_scale=1e-3))
        
        # Should be proven when hermitian
        self.assertTrue(model1.is_hermitian())
        self.assertTrue(model1.riemann_hypothesis_proven_in_biology())
        
        # Should not be proven when not hermitian
        self.assertFalse(model2.is_hermitian())
        self.assertFalse(model2.riemann_hypothesis_proven_in_biology())


class TestSummary(unittest.TestCase):
    """Test summary generation"""
    
    def test_summary_contains_all_keys(self):
        """Test that summary contains all required keys"""
        model = CytoplasmicFlowModel()
        summary = model.get_summary()
        
        required_keys = [
            "density_kg_m3",
            "kinematic_viscosity_m2_s",
            "cell_scale_m",
            "flow_velocity_m_s",
            "reynolds_number",
            "flow_regime",
            "is_viscous",
            "has_smooth_solution",
            "flow_coherence",
            "hilbert_polya_exists",
            "is_hermitian",
            "physical_medium",
            "fundamental_frequency_hz",
            "eigenfrequencies_hz",
            "riemann_proven_in_biology"
        ]
        
        for key in required_keys:
            self.assertIn(key, summary)
    
    def test_summary_values(self):
        """Test summary values for default params"""
        model = CytoplasmicFlowModel()
        summary = model.get_summary()
        
        self.assertEqual(summary["density_kg_m3"], 1000.0)
        self.assertAlmostEqual(summary["reynolds_number"], 1e-8)
        self.assertTrue(summary["is_viscous"])
        self.assertTrue(summary["has_smooth_solution"])
        self.assertTrue(summary["hilbert_polya_exists"])
        self.assertTrue(summary["is_hermitian"])
        self.assertTrue(summary["riemann_proven_in_biology"])
        self.assertEqual(len(summary["eigenfrequencies_hz"]), 5)


class TestDemonstration(unittest.TestCase):
    """Test demonstration output"""
    
    def test_print_demonstration_runs(self):
        """Test that print_demonstration runs without error"""
        import io
        from contextlib import redirect_stdout
        
        model = CytoplasmicFlowModel()
        
        # Capture output
        f = io.StringIO()
        with redirect_stdout(f):
            model.print_demonstration()
        
        output = f.getvalue()
        
        # Check that output contains key phrases
        self.assertIn("NAVIER-STOKES EN CITOPLASMA", output)
        self.assertIn("REYNOLDS", output)
        self.assertIn("HILBERT-PÓLYA", output)
        self.assertIn("141.7001", output)
        self.assertIn("RIEMANN", output)


def run_tests():
    """Run all tests"""
    unittest.main(argv=[''], verbosity=2, exit=False)


if __name__ == "__main__":
    run_tests()
