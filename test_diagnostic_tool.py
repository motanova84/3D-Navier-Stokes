#!/usr/bin/env python3
"""
Test suite for the diagnostic tool.
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))

from diagnostic_tool import LeanFileAnalyzer, analyze_directory


def test_basic_lean():
    """Test Basic.lean file analysis."""
    filepath = "/home/runner/work/3D-Navier-Stokes/3D-Navier-Stokes/PsiNSE/Basic.lean"
    analyzer = LeanFileAnalyzer(filepath)
    stats = analyzer.get_stats()
    
    print(f"Testing {filepath}")
    print(f"  Lemmas: {stats['lemmas']}")
    print(f"  Sorry: {stats['sorry']}")
    
    assert stats['sorry'] == 1, f"Expected 1 sorry, got {stats['sorry']}"
    assert stats['lemmas'] == 6, f"Expected 6 lemmas, got {stats['lemmas']}"
    print("  ✓ Basic.lean tests passed")


def test_local_existence():
    """Test LocalExistence.lean file analysis."""
    filepath = "/home/runner/work/3D-Navier-Stokes/3D-Navier-Stokes/PsiNSE/LocalExistence.lean"
    analyzer = LeanFileAnalyzer(filepath)
    stats = analyzer.get_stats()
    
    print(f"\nTesting {filepath}")
    print(f"  Lemmas: {stats['lemmas']}")
    print(f"  Sorry: {stats['sorry']}")
    
    assert stats['sorry'] == 3, f"Expected 3 sorry, got {stats['sorry']}"
    assert stats['lemmas'] == 3, f"Expected 3 lemmas, got {stats['lemmas']}"
    print("  ✓ LocalExistence.lean tests passed")


def test_complete_analysis():
    """Test complete directory analysis."""
    base_dir = "/home/runner/work/3D-Navier-Stokes/3D-Navier-Stokes"
    files = [
        "PsiNSE/Basic.lean",
        "PsiNSE/LocalExistence.lean",
        "PsiNSE/EnergyEstimates.lean",
        "PsiNSE/GlobalRegularity.lean",
        "PsiNSE/CouplingTensor.lean",
        "PsiNSE/FrequencyEmergence.lean"
    ]
    
    results = analyze_directory(base_dir, files)
    
    print("\nTesting complete analysis:")
    print(f"  Files analyzed: {len(results)}")
    
    total_lemmas = sum(r['total_lemmas'] for r in results)
    total_sorry = sum(r['sorry_count'] for r in results)
    
    print(f"  Total lemmas: {total_lemmas}")
    print(f"  Total sorry: {total_sorry}")
    
    assert len(results) == 6, f"Expected 6 files, got {len(results)}"
    assert total_lemmas == 22, f"Expected 22 lemmas, got {total_lemmas}"
    assert total_sorry == 12, f"Expected 12 sorry, got {total_sorry}"
    print("  ✓ Complete analysis tests passed")


def main():
    """Run all tests."""
    print("Running diagnostic tool tests...\n")
    
    try:
        test_basic_lean()
        test_local_existence()
        test_complete_analysis()
        
        print("\n" + "="*50)
        print("✓ All tests passed successfully!")
        print("="*50)
        return 0
    
    except AssertionError as e:
        print(f"\n✗ Test failed: {e}")
        return 1
    except Exception as e:
        print(f"\n✗ Unexpected error: {e}")
        return 1


if __name__ == "__main__":
    sys.exit(main())
