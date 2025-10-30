"""
Tests for the AI Agent

Basic tests to validate the AI agent functionality
"""

import sys
import os
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent))

def test_import():
    """Test that all modules can be imported"""
    print("Testing imports...")
    try:
        from ai_agent import NavierStokesAIAgent
        from ai_agent import EquationParser
        from ai_agent import MathematicalMemory
        from ai_agent import ScriptGenerator
        from ai_agent import EquationVisualizer
        print("✓ All modules imported successfully")
        return True
    except Exception as e:
        print(f"✗ Import failed: {e}")
        return False


def test_equation_parser():
    """Test equation parsing"""
    print("\nTesting EquationParser...")
    try:
        from ai_agent import EquationParser
        
        parser = EquationParser()
        
        # Test parsing text with equations
        text = """
        The Navier-Stokes equations are:
        ∂u/∂t + (u·∇)u = -∇p + ν∆u + f
        
        The BKM criterion states:
        ∫₀^T ‖ω(t)‖_{L∞} dt < ∞ ⇒ no blow-up
        
        With constants: ν = 1e-3, C_BKM = 2.0
        """
        
        results = parser.parse_text(text, source="test")
        
        assert results['total_equations'] > 0, "No equations extracted"
        assert 'equations' in results, "Missing equations key"
        assert 'categories' in results, "Missing categories key"
        
        print(f"✓ Extracted {results['total_equations']} equations")
        return True
    except Exception as e:
        print(f"✗ EquationParser test failed: {e}")
        return False


def test_mathematical_memory():
    """Test mathematical memory"""
    print("\nTesting MathematicalMemory...")
    try:
        from ai_agent import MathematicalMemory
        
        memory = MathematicalMemory()
        
        # Test adding equation
        memory.add_equation(
            name="Test Equation",
            formula="x + y = z",
            description="Test equation",
            category="general"
        )
        
        # Test adding constant
        memory.add_constant(
            name="test_const",
            description="Test constant",
            typical_value="1.0"
        )
        
        # Test search
        results = memory.search("Test")
        assert len(results) > 0, "Search returned no results"
        
        # Test summary
        summary = memory.get_summary()
        assert summary['total_equations'] > 0, "No equations in memory"
        assert summary['total_constants'] > 0, "No constants in memory"
        
        print(f"✓ Memory stores {summary['total_equations']} equations and {summary['total_constants']} constants")
        return True
    except Exception as e:
        print(f"✗ MathematicalMemory test failed: {e}")
        return False


def test_script_generator():
    """Test script generation"""
    print("\nTesting ScriptGenerator...")
    try:
        from ai_agent import ScriptGenerator
        import tempfile
        
        # Create temporary directory
        with tempfile.TemporaryDirectory() as tmpdir:
            generator = ScriptGenerator(output_dir=tmpdir)
            
            # Test verification script generation
            equations = [
                {
                    'name': 'Test Equation',
                    'formula': 'x = y',
                    'description': 'Test',
                    'category': 'general'
                }
            ]
            
            script_path = generator.generate_verification_script(
                equations,
                output_file="test_verify.py"
            )
            
            assert Path(script_path).exists(), "Script not generated"
            
            # Check script contains expected content
            with open(script_path, 'r') as f:
                content = f.read()
                assert 'class EquationVerifier' in content, "Missing class definition"
                assert 'def verify_' in content, "Missing verification methods"
            
            print("✓ Scripts generated successfully")
            return True
    except Exception as e:
        print(f"✗ ScriptGenerator test failed: {e}")
        return False


def test_agent_initialization():
    """Test AI agent initialization"""
    print("\nTesting NavierStokesAIAgent...")
    try:
        from ai_agent import NavierStokesAIAgent
        import tempfile
        
        with tempfile.TemporaryDirectory() as tmpdir:
            agent = NavierStokesAIAgent(workspace_dir=tmpdir)
            
            # Check that agent has required components
            assert agent.parser is not None, "Parser not initialized"
            assert agent.memory is not None, "Memory not initialized"
            assert agent.generator is not None, "Generator not initialized"
            assert agent.visualizer is not None, "Visualizer not initialized"
            
            # Check pre-loaded knowledge
            summary = agent.memory.get_summary()
            assert summary['total_equations'] > 0, "No pre-loaded equations"
            assert summary['total_constants'] > 0, "No pre-loaded constants"
            
            print(f"✓ Agent initialized with {summary['total_equations']} equations and {summary['total_constants']} constants")
            return True
    except Exception as e:
        print(f"✗ NavierStokesAIAgent test failed: {e}")
        return False


def test_text_processing():
    """Test processing of text content"""
    print("\nTesting text processing...")
    try:
        from ai_agent import NavierStokesAIAgent
        import tempfile
        
        with tempfile.TemporaryDirectory() as tmpdir:
            agent = NavierStokesAIAgent(workspace_dir=tmpdir)
            
            # Create test text file
            test_file = Path(tmpdir) / "test.md"
            test_file.write_text("""
# Test Document

The vorticity equation: ω = ∇ × u

Energy estimate: ‖u‖_{L²} ≤ C

Riccati inequality: d/dt X ≤ A - B X log(X)
            """)
            
            # Create test directory structure
            test_dir = Path(tmpdir) / "test_docs"
            test_dir.mkdir()
            (test_dir / "doc1.md").write_text("Test equation: x = 1")
            
            # Process the directory
            results = agent.process_documentation(str(test_dir))
            
            assert results['files_processed'] > 0, "No files processed"
            assert results['total_equations'] >= 0, "Equation count missing"
            
            print(f"✓ Processed {results['files_processed']} files")
            return True
    except Exception as e:
        print(f"✗ Text processing test failed: {e}")
        return False


def run_all_tests():
    """Run all tests"""
    print("="*70)
    print("AI AGENT TEST SUITE")
    print("="*70)
    
    tests = [
        test_import,
        test_equation_parser,
        test_mathematical_memory,
        test_script_generator,
        test_agent_initialization,
        test_text_processing,
    ]
    
    results = []
    for test in tests:
        try:
            result = test()
            results.append(result)
        except Exception as e:
            print(f"✗ Test crashed: {e}")
            results.append(False)
    
    print("\n" + "="*70)
    print("TEST SUMMARY")
    print("="*70)
    
    passed = sum(results)
    total = len(results)
    
    print(f"\nPassed: {passed}/{total}")
    
    if passed == total:
        print("\n✓ ALL TESTS PASSED")
        return 0
    else:
        print(f"\n✗ {total - passed} TEST(S) FAILED")
        return 1


if __name__ == "__main__":
    exit_code = run_all_tests()
    sys.exit(exit_code)
