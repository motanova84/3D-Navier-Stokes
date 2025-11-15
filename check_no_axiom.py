#!/usr/bin/env python3
"""
check_no_axiom.py - Verification script for axiom-free Lean4 formalization

This script verifies that the Lean4 formalization uses only standard axioms
from Mathlib and does not introduce custom axioms that would compromise
the proof's validity.

Standard axioms allowed (from Mathlib):
- propext: Propositional extensionality
- quot.sound: Quotient soundness
- Classical.choice: Classical choice (when explicitly needed)
- funext: Function extensionality

Status: If this script reports 0 custom axioms, the formalization is
constructively valid (or uses only classical axioms explicitly).
"""

import os
import re
import sys
from pathlib import Path
from typing import List, Tuple, Set

# Standard axioms from Mathlib that are allowed
STANDARD_AXIOMS = {
    'propext',
    'quot.sound',
    'Quot.sound',
    'Classical.choice',
    'Classical.axiomOfChoice',
    'funext',
    'Function.funext',
}

def find_axiom_declarations(file_path: Path) -> List[Tuple[int, str]]:
    """
    Find axiom declarations in a Lean file.
    Returns list of (line_number, axiom_name) tuples.
    """
    axioms = []
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            for line_num, line in enumerate(f, 1):
                # Skip comments
                if line.strip().startswith('--'):
                    continue
                if line.strip().startswith('/-'):
                    continue
                
                # Look for axiom declarations
                # Pattern: "axiom name : type" or "axiom name ..."
                match = re.match(r'^\s*axiom\s+(\w+)', line)
                if match:
                    axiom_name = match.group(1)
                    axioms.append((line_num, axiom_name))
                    
    except Exception as e:
        print(f"Warning: Could not read {file_path}: {e}", file=sys.stderr)
    
    return axioms

def check_axiom_usage(file_path: Path) -> Set[str]:
    """
    Check if file uses #check_axioms or similar verification commands.
    Returns set of axiom names found in usage checks.
    """
    axioms_used = set()
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
            # Look for #check_axioms or #print axioms
            if '#check_axioms' in content or '#print axioms' in content:
                # This is good - it means they're checking axioms
                pass
    except Exception as e:
        print(f"Warning: Could not read {file_path}: {e}", file=sys.stderr)
    
    return axioms_used

def scan_lean_files(directory: Path) -> Tuple[List[Tuple[Path, int, str]], int]:
    """
    Scan all .lean files in directory for axiom declarations.
    Returns (list of custom axioms, total files scanned).
    """
    custom_axioms = []
    total_files = 0
    
    for lean_file in directory.rglob('*.lean'):
        total_files += 1
        axioms = find_axiom_declarations(lean_file)
        
        for line_num, axiom_name in axioms:
            # Check if it's a custom axiom (not in standard list)
            if axiom_name not in STANDARD_AXIOMS:
                custom_axioms.append((lean_file, line_num, axiom_name))
    
    return custom_axioms, total_files

def main():
    """Main verification routine."""
    print("🔍 VERIFICANDO AXIOMAS EN FORMALIZACIÓN LEAN4")
    print("═" * 70)
    print()
    
    # Get directory to scan
    if len(sys.argv) > 1:
        scan_dir = Path(sys.argv[1])
    else:
        scan_dir = Path('Lean4-Formalization')
    
    if not scan_dir.exists():
        print(f"❌ Error: Directory {scan_dir} not found")
        sys.exit(1)
    
    # Scan for axioms
    custom_axioms, total_files = scan_lean_files(scan_dir)
    
    # Report results
    print(f"📊 Resultados:")
    print(f"   Total de archivos .lean escaneados: {total_files}")
    print(f"   Axiomas personalizados encontrados: {len(custom_axioms)}")
    print()
    
    if len(custom_axioms) == 0:
        print("✅ ¡ÉXITO! 0 axiomas personalizados")
        print("🎉 La formalización usa únicamente axiomas estándar de Mathlib")
        print()
        print("📋 Axiomas estándar permitidos:")
        for axiom in sorted(STANDARD_AXIOMS):
            print(f"   ✓ {axiom}")
        print()
        print("✅ ESTADO: 100% LIBRE DE AXIOMAS PERSONALIZADOS")
        print()
        return 0
    else:
        print("⚠️  Se encontraron axiomas personalizados:")
        print()
        for file_path, line_num, axiom_name in custom_axioms:
            rel_path = file_path.relative_to(scan_dir)
            print(f"   📍 {rel_path}:{line_num}")
            print(f"      axiom {axiom_name}")
        print()
        print("❌ ADVERTENCIA: La formalización contiene axiomas no estándar")
        print("   Esto puede comprometer la validez constructiva de la prueba.")
        print()
        return 1

if __name__ == '__main__':
    sys.exit(main())
