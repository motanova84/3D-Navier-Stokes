#!/usr/bin/env python3
"""
Quick Start Guide for Universal Validation Framework
====================================================

This script demonstrates how to use the universal_validation_framework.py
to validate the presence of f₀ = 141.7 Hz across multiple physical systems.

Author: José Manuel Mota Burruezo (JMMB)
"""

from universal_validation_framework import (
    UniversalFrequency,
    UniversalValidator,
    DESIValidator,
    IGETSValidator,
    EEGValidator
)

def example_1_basic_usage():
    """
    Example 1: Run all validations and generate report
    """
    print("=" * 70)
    print("EXAMPLE 1: Basic Usage - Run All Validations")
    print("=" * 70)
    
    # Create validator
    validator = UniversalValidator()
    
    # Run all validations
    results = validator.run_all_validations()
    
    # Generate visualization
    validator.plot_summary(results, output_file='artifacts/example_1_summary.png')
    
    # Generate text report
    report = validator.generate_report(results)
    
    # Save report
    with open('artifacts/example_1_report.txt', 'w', encoding='utf-8') as f:
        f.write(report)
    
    print("\n✓ Example 1 complete!")
    print("  - Generated: artifacts/example_1_summary.png")
    print("  - Generated: artifacts/example_1_report.txt")


def example_2_single_system():
    """
    Example 2: Test a single system (EEG)
    """
    print("\n" + "=" * 70)
    print("EXAMPLE 2: Single System Validation (EEG)")
    print("=" * 70)
    
    # Create EEG validator
    eeg = EEGValidator()
    
    # Generate synthetic EEG data (5 minutes)
    t, eeg_data = eeg.generate_synthetic_eeg(duration_s=300)
    
    # Search for f₀ signal
    result = eeg.search_signal(t, eeg_data)
    
    # Print results
    print(f"\n✓ EEG Analysis Complete:")
    print(f"  - Frequency detected: {result['frequency_detected']:.4f} Hz")
    print(f"  - SNR: {result['snr']:.2f}")
    print(f"  - Significance: {result['significance_sigma']:.2f}σ")
    print(f"  - Confidence: {result['detection_confidence']}")


def example_3_custom_parameters():
    """
    Example 3: Using UniversalFrequency with custom parameters
    """
    print("\n" + "=" * 70)
    print("EXAMPLE 3: Custom Frequency Analysis")
    print("=" * 70)
    
    # Create frequency object
    f0 = UniversalFrequency()
    
    # Get harmonics
    harmonics = f0.harmonics(n_max=3)
    print(f"\nHarmonics of f₀:")
    for i, h in enumerate(harmonics, 1):
        print(f"  {i}×f₀ = {h:.4f} Hz")
    
    # Get subharmonics
    subharmonics = f0.subharmonics(n_max=3)
    print(f"\nSubharmonics of f₀:")
    for i, s in enumerate(subharmonics, 1):
        print(f"  f₀/{i+1} = {s:.4f} Hz")
    
    # Get tolerance band
    f_min, f_max = f0.tolerance_band(tolerance_pct=1.0)
    print(f"\nTolerance band (±1%):")
    print(f"  [{f_min:.4f}, {f_max:.4f}] Hz")


def example_4_igets_validation():
    """
    Example 4: Detailed IGETS gravimetry analysis
    """
    print("\n" + "=" * 70)
    print("EXAMPLE 4: IGETS Gravimetry Validation")
    print("=" * 70)
    
    # Create IGETS validator
    igets = IGETSValidator()
    
    # Generate synthetic gravimeter data (1 hour)
    print("\nGenerating synthetic gravimeter data...")
    t, g = igets.generate_synthetic_data(duration_hours=1)
    
    print(f"  - Duration: {(t[-1] - t[0])/3600:.2f} hours")
    print(f"  - Samples: {len(t):,}")
    print(f"  - Sampling rate: {1.0/(t[1]-t[0]):.1f} Hz")
    
    # Search for f₀ signal
    print("\nSearching for f₀ = 141.7 Hz...")
    result = igets.search_signal(t, g)
    
    print(f"\n✓ IGETS Analysis Complete:")
    print(f"  - Frequency detected: {result['frequency_detected']:.4f} Hz")
    print(f"  - Error: {result['frequency_error_hz']:.6f} Hz")
    print(f"  - SNR: {result['snr']:.2f}")
    print(f"  - Significance: {result['significance_sigma']:.2f}σ")


if __name__ == '__main__':
    print("""
╔═══════════════════════════════════════════════════════════════╗
║   UNIVERSAL VALIDATION FRAMEWORK - QUICK START GUIDE          ║
║   f₀ = 141.7 Hz Multi-System Validation                       ║
╚═══════════════════════════════════════════════════════════════╝
    """)
    
    # Run examples
    # Uncomment the examples you want to run:
    
    # example_1_basic_usage()      # Full validation across all systems
    # example_2_single_system()    # Single system (EEG) validation
    example_3_custom_parameters()  # Explore frequency parameters
    example_4_igets_validation()   # Detailed IGETS analysis
    
    print("\n" + "=" * 70)
    print("All examples complete!")
    print("=" * 70)
    print("\n✨ José Manuel Mota Burruezo (JMMB) Ψ✧ ∴ ✨\n")
