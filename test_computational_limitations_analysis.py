#!/usr/bin/env python3
"""
Test suite for computational_limitations_analysis.py

Verifies that the analysis script runs correctly and produces expected output.
"""

import unittest
import sys
import io
from contextlib import redirect_stdout


class TestComputationalLimitationsAnalysis(unittest.TestCase):
    """Test cases for computational limitations analysis script"""
    
    def setUp(self):
        """Set up test fixtures"""
        # Import the module
        import computational_limitations_analysis
        self.module = computational_limitations_analysis
    
    def test_module_imports(self):
        """Test that module imports successfully"""
        self.assertIsNotNone(self.module)
    
    def test_print_header_function_exists(self):
        """Test that print_header function exists"""
        self.assertTrue(hasattr(self.module, 'print_header'))
        self.assertTrue(callable(self.module.print_header))
    
    def test_print_viable_strategies_function_exists(self):
        """Test that print_viable_strategies function exists"""
        self.assertTrue(hasattr(self.module, 'print_viable_strategies'))
        self.assertTrue(callable(self.module.print_viable_strategies))
    
    def test_print_final_conclusion_function_exists(self):
        """Test that print_final_conclusion function exists"""
        self.assertTrue(hasattr(self.module, 'print_final_conclusion'))
        self.assertTrue(callable(self.module.print_final_conclusion))
    
    def test_print_technical_summary_function_exists(self):
        """Test that print_technical_summary function exists"""
        self.assertTrue(hasattr(self.module, 'print_technical_summary'))
        self.assertTrue(callable(self.module.print_technical_summary))
    
    def test_print_psi_nse_benefits_function_exists(self):
        """Test that print_psi_nse_benefits function exists"""
        self.assertTrue(hasattr(self.module, 'print_psi_nse_benefits'))
        self.assertTrue(callable(self.module.print_psi_nse_benefits))
    
    def test_print_recommendations_function_exists(self):
        """Test that print_recommendations function exists"""
        self.assertTrue(hasattr(self.module, 'print_recommendations'))
        self.assertTrue(callable(self.module.print_recommendations))
    
    def test_main_function_exists(self):
        """Test that main function exists"""
        self.assertTrue(hasattr(self.module, 'main'))
        self.assertTrue(callable(self.module.main))
    
    def test_print_header_output(self):
        """Test that print_header produces output"""
        f = io.StringIO()
        with redirect_stdout(f):
            self.module.print_header()
        output = f.getvalue()
        self.assertIn("ANÁLISIS DE LIMITACIONES COMPUTACIONALES", output)
        self.assertIn("Navier-Stokes", output)
    
    def test_print_viable_strategies_output(self):
        """Test that print_viable_strategies produces expected output"""
        f = io.StringIO()
        with redirect_stdout(f):
            self.module.print_viable_strategies()
        output = f.getvalue()
        self.assertIn("ESTRATEGIAS VIABLES", output)
        self.assertIn("OPCIÓN A", output)
        self.assertIn("Ψ-NSE", output)
        self.assertIn("OPCIÓN B", output)
        self.assertIn("OPCIÓN C", output)
        self.assertIn("RECOMENDACIÓN", output)
    
    def test_print_final_conclusion_output(self):
        """Test that print_final_conclusion produces expected output"""
        f = io.StringIO()
        with redirect_stdout(f):
            self.module.print_final_conclusion()
        output = f.getvalue()
        self.assertIn("CONCLUSIÓN FINAL", output)
        self.assertIn("PUEDE LA COMPUTACIÓN", output)
        self.assertIn("BARRERA MATEMÁTICA FUNDAMENTAL", output)
        self.assertIn("Φ_ij", output)
    
    def test_print_technical_summary_output(self):
        """Test that print_technical_summary produces expected output"""
        f = io.StringIO()
        with redirect_stdout(f):
            self.module.print_technical_summary()
        output = f.getvalue()
        self.assertIn("RESUMEN TÉCNICO", output)
        self.assertIn("LIMITACIONES COMPUTACIONALES", output)
        self.assertIn("NP-hard", output)
        self.assertIn("Ψ-NSE", output)
    
    def test_print_psi_nse_benefits_output(self):
        """Test that print_psi_nse_benefits produces expected output"""
        f = io.StringIO()
        with redirect_stdout(f):
            self.module.print_psi_nse_benefits()
        output = f.getvalue()
        self.assertIn("BENEFICIOS", output)
        self.assertIn("Ψ-NSE", output)
        self.assertIn("Física Completa", output)
        self.assertIn("141.7001 Hz", output)
        self.assertIn("Lean4", output)
    
    def test_print_recommendations_output(self):
        """Test that print_recommendations produces expected output"""
        f = io.StringIO()
        with redirect_stdout(f):
            self.module.print_recommendations()
        output = f.getvalue()
        self.assertIn("RECOMENDACIONES", output)
        self.assertIn("investigadores", output)
        self.assertIn("Próximos Pasos", output)
    
    def test_main_runs_without_errors(self):
        """Test that main function runs without errors"""
        f = io.StringIO()
        try:
            with redirect_stdout(f):
                self.module.main()
            success = True
        except Exception as e:
            success = False
            self.fail(f"main() raised exception: {e}")
        
        self.assertTrue(success)
        output = f.getvalue()
        # Verify key sections are present
        self.assertIn("ESTRATEGIAS VIABLES", output)
        self.assertIn("CONCLUSIÓN FINAL", output)
        self.assertIn("FIN DEL ANÁLISIS", output)
    
    def test_output_contains_all_three_options(self):
        """Test that output contains all three strategic options"""
        f = io.StringIO()
        with redirect_stdout(f):
            self.module.print_viable_strategies()
        output = f.getvalue()
        
        # Check for all three options
        self.assertIn("OPCIÓN A", output)
        self.assertIn("OPCIÓN B", output)
        self.assertIn("OPCIÓN C", output)
        
        # Check for key details of each option
        self.assertIn("ENFOQUE HÍBRIDO", output)
        self.assertIn("CASOS ESPECIALES", output)
        self.assertIn("BLOW-UP CONSTRUCTIVO", output)
    
    def test_output_contains_key_conclusions(self):
        """Test that output contains key conclusions"""
        f = io.StringIO()
        with redirect_stdout(f):
            self.module.print_final_conclusion()
        output = f.getvalue()
        
        # Check for key messages
        self.assertIn("N O", output)  # The answer "NO"
        self.assertIn("SOLUCIÓN CORRECTA", output)
        self.assertIn("Computacionalmente factible", output)
        self.assertIn("Experimentalmente verificable", output)
        self.assertIn("Matemáticamente riguroso", output)


def run_tests():
    """Run all tests"""
    print("\n" + "="*70)
    print("COMPUTATIONAL LIMITATIONS ANALYSIS - Test Suite")
    print("="*70 + "\n")
    
    # Create test suite
    suite = unittest.TestLoader().loadTestsFromTestCase(
        TestComputationalLimitationsAnalysis
    )
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Print summary
    print("\n" + "="*70)
    print("RESUMEN DE PRUEBAS")
    print("="*70)
    print(f"Tests ejecutados: {result.testsRun}")
    print(f"Éxitos: {result.testsRun - len(result.failures) - len(result.errors)}")
    print(f"Fallos: {len(result.failures)}")
    print(f"Errores: {len(result.errors)}")
    print("="*70)
    
    if result.wasSuccessful():
        print("\n✅ [ALL TESTS PASSED SUCCESSFULLY]\n")
        return 0
    else:
        print("\n❌ [SOME TESTS FAILED]\n")
        return 1


if __name__ == "__main__":
    sys.exit(run_tests())
