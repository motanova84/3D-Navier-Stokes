#!/usr/bin/env python3
"""
Update DiagnosticReport.lean with current statistics.
This script regenerates the statistics section of DiagnosticReport.lean
based on actual file analysis.
"""

import sys
from diagnostic_tool import analyze_directory


def generate_lean_stats_code(results):
    """Generate Lean code for the psiNSEStats definition."""
    stats_entries = []
    for result in results:
        entry = f"  ⟨\"{result['file']}\", {result['total_lemmas']}, {result['sorry_count']}⟩"
        stats_entries.append(entry)
    
    lean_code = "/-- Example statistics for PsiNSE files -/\n"
    lean_code += "def psiNSEStats : List FileStats := [\n"
    lean_code += ",\n".join(stats_entries)
    lean_code += "\n]"
    
    return lean_code


def main():
    """Main function."""
    base_dir = "/home/runner/work/3D-Navier-Stokes/3D-Navier-Stokes"
    files = [
        "PsiNSE/Basic.lean",
        "PsiNSE/LocalExistence.lean",
        "PsiNSE/EnergyEstimates.lean",
        "PsiNSE/GlobalRegularity.lean",
        "PsiNSE/CouplingTensor.lean",
        "PsiNSE/FrequencyEmergence.lean"
    ]
    
    print("Analyzing files...")
    results = analyze_directory(base_dir, files)
    
    print("\nGenerating Lean code for statistics:")
    print("="*60)
    lean_code = generate_lean_stats_code(results)
    print(lean_code)
    print("="*60)
    
    # Calculate totals
    total_lemmas = sum(r['total_lemmas'] for r in results)
    total_sorry = sum(r['sorry_count'] for r in results)
    overall_completion = 100 * (total_lemmas - total_sorry) // total_lemmas if total_lemmas > 0 else 100
    
    print(f"\nSummary:")
    print(f"  Total files: {len(results)}")
    print(f"  Total lemmas: {total_lemmas}")
    print(f"  Total sorry: {total_sorry}")
    print(f"  Overall completion: {overall_completion}%")
    
    print("\n✓ Code generated successfully!")
    print("  You can copy the code above to update DiagnosticReport.lean")


if __name__ == "__main__":
    main()
