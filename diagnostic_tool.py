#!/usr/bin/env python3
"""
Diagnostic tool to analyze Lean files for sorry statements and lemmas.

This script provides automated analysis of Lean formalization completeness
by counting lemmas and sorry statements.
"""

import re
import os
from pathlib import Path
from typing import Dict, List, Tuple


class LeanFileAnalyzer:
    """Analyzer for Lean 4 files."""
    
    def __init__(self, filepath: str):
        self.filepath = filepath
        self.content = self._read_file()
    
    def _read_file(self) -> str:
        """Read the Lean file content."""
        try:
            with open(self.filepath, 'r', encoding='utf-8') as f:
                return f.read()
        except Exception as e:
            print(f"Error reading {self.filepath}: {e}")
            return ""
    
    def count_sorry(self) -> int:
        """Count sorry statements in the file."""
        # Match 'sorry' as a complete word (not in comments or strings)
        pattern = r'\bsorry\b'
        matches = re.findall(pattern, self.content)
        return len(matches)
    
    def count_lemmas(self) -> int:
        """Count lemmas and theorems in the file."""
        # Match theorem, lemma, def declarations
        pattern = r'\b(theorem|lemma|def)\s+\w+'
        matches = re.findall(pattern, self.content)
        return len(matches)
    
    def get_stats(self) -> Dict[str, int]:
        """Get comprehensive statistics."""
        return {
            'lemmas': self.count_lemmas(),
            'sorry': self.count_sorry()
        }


def analyze_directory(directory: str, file_list: List[str]) -> List[Dict]:
    """Analyze multiple Lean files in a directory."""
    results = []
    
    for filename in file_list:
        filepath = os.path.join(directory, filename)
        if os.path.exists(filepath):
            analyzer = LeanFileAnalyzer(filepath)
            stats = analyzer.get_stats()
            completion = 100 * (stats['lemmas'] - stats['sorry']) // stats['lemmas'] if stats['lemmas'] > 0 else 100
            
            results.append({
                'file': filename,
                'total_lemmas': stats['lemmas'],
                'sorry_count': stats['sorry'],
                'completion': completion
            })
        else:
            print(f"Warning: File not found: {filepath}")
    
    return results


def print_report(results: List[Dict]):
    """Print a formatted diagnostic report."""
    print("📋 ANÁLISIS DE COMPLETITUD:")
    print("━" * 42)
    print()
    
    total_lemmas = 0
    total_sorry = 0
    
    for result in results:
        print(f"📄 {result['file']}:")
        print(f"   Lemas totales: {result['total_lemmas']}")
        print(f"   Sorry pendientes: {result['sorry_count']}")
        print(f"   Completitud: {result['completion']}%")
        print()
        
        total_lemmas += result['total_lemmas']
        total_sorry += result['sorry_count']
    
    print("━" * 42)
    print("📊 RESUMEN TOTAL:")
    print(f"   Archivos analizados: {len(results)}")
    print(f"   Lemas totales: {total_lemmas}")
    print(f"   Sorry pendientes: {total_sorry}")
    overall_completion = 100 * (total_lemmas - total_sorry) // total_lemmas if total_lemmas > 0 else 100
    print(f"   Completitud general: {overall_completion}%")


def main():
    """Main entry point."""
    # Base directory
    base_dir = "/home/runner/work/3D-Navier-Stokes/3D-Navier-Stokes"
    
    # Files to analyze
    files = [
        "PsiNSE/Basic.lean",
        "PsiNSE/LocalExistence.lean",
        "PsiNSE/EnergyEstimates.lean",
        "PsiNSE/GlobalRegularity.lean",
        "PsiNSE/CouplingTensor.lean",
        "PsiNSE/FrequencyEmergence.lean"
    ]
    
    print("Analyzing Lean files...")
    print()
    
    results = analyze_directory(base_dir, files)
    print_report(results)


if __name__ == "__main__":
    main()
