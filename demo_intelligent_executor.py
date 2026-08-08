#!/usr/bin/env python3
"""
Demo script showing how to use the intelligent executor system.
"""

import os
import sys
from pathlib import Path

def main():
    print("═" * 70)
    print("  INTELLIGENT EXECUTOR - DEMO")
    print("═" * 70)
    
    # Step 1: Create sample packages
    print("\n1️⃣  Creating sample parametric sweep packages...")
    from parametric_sweep_orchestrator import create_sample_packages
    create_sample_packages(n_packages=5, output_dir='demo_packages')
    
    # Step 2: Show intelligent selection
    print("\n2️⃣  Demonstrating intelligent package selection...")
    from intelligent_executor import get_next_package_to_run
    pkg_id, pkg_info = get_next_package_to_run(
        packages_dir='demo_packages',
        results_dir='demo_results'
    )
    
    if pkg_id is not None:
        print(f"\n   Selected package: {pkg_id}")
        print(f"   Priority: {pkg_info.get('priority', 'N/A')}")
        print(f"   Estimated time: {pkg_info['estimated_time_hours']:.2f} hours")
        print(f"   Estimated memory: {pkg_info['estimated_memory_gb']:.2f} GB")
    
    # Step 3: Execute the selected package
    print("\n3️⃣  Executing selected package...")
    from parametric_sweep_orchestrator import run_package
    if pkg_id is not None:
        result = run_package(
            pkg_id, 
            output_dir='demo_results', 
            packages_dir='demo_packages'
        )
        print(f"\n   ✅ Execution completed successfully!")
        print(f"   Status: {result['status']}")
        print(f"   Execution time: {result['execution_time']:.2f} seconds")
    
    # Step 4: Show available execution modes
    print("\n4️⃣  Available execution modes:")
    print("\n   a) Next mode (single package):")
    print("      python intelligent_executor.py --mode next")
    
    print("\n   b) Continuous mode (run until completion or time limit):")
    print("      python intelligent_executor.py --mode continuous --max-hours 2")
    
    print("\n   c) Opportunistic mode (run when CPU is idle):")
    print("      python intelligent_executor.py --mode opportunistic --cpu-threshold 70")
    
    print("\n" + "═" * 70)
    print("  Demo completed! Check 'demo_packages' and 'demo_results' directories.")
    print("═" * 70)
    
    # Cleanup note
    print("\n💡 Cleanup: To remove demo files, run:")
    print("   rm -rf demo_packages demo_results")

if __name__ == '__main__':
    main()
