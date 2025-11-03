#!/usr/bin/env python3
"""
Quick test for extreme DNS comparison
Uses minimal resolution for fast validation
"""

import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.dirname(__file__))

from extreme_dns_comparison import ExtremeDNSComparison


def test_basic_functionality():
    """Test basic functionality with minimal resolution"""
    print("\n" + "="*80)
    print("QUICK TEST: Extreme DNS Comparison (N=16, T=1s)")
    print("="*80 + "\n")
    
    # Use minimal parameters for fast test
    comparison = ExtremeDNSComparison(N=16, ν=5e-4, T_max=1.0)
    
    # Test classical NSE
    print("Testing Classical NSE...")
    results_classical = comparison.simulate_classical(dt=1e-2)
    print(f"  Status: {'✓ PASSED' if results_classical else '✗ FAILED'}")
    
    # Test QCAL NSE
    print("\nTesting Ψ-NSE (QCAL)...")
    results_qcal = comparison.simulate_qcal(dt=1e-2)
    print(f"  Status: {'✓ PASSED' if results_qcal else '✗ FAILED'}")
    
    # Generate outputs
    print("\nGenerating outputs...")
    plot_path = comparison.generate_comparison_plots()
    report_path = comparison.generate_report(results_classical, results_qcal)
    
    print("\n" + "="*80)
    print("✓ QUICK TEST COMPLETED")
    print("="*80)
    print(f"\nReport: {report_path}")
    print(f"Plot: {plot_path}")
    
    return 0


if __name__ == '__main__':
    sys.exit(test_basic_functionality())
