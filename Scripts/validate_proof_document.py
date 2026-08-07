#!/usr/bin/env python3
"""
Validation script for rigorous_proof_psi_nse.tex

This script performs structural validation of the LaTeX proof document without compiling it.
Checks include:
- Document structure (begin/end balance)
- Required theorems and lemmas
- Key equations
- Bibliography entries
- References to fundamental constants
"""

import re
import sys
from pathlib import Path


def validate_latex_structure(filepath):
    """Validate basic LaTeX document structure"""
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    print("=" * 60)
    print("LaTeX Document Validation Report")
    print("=" * 60)
    print(f"File: {filepath}")
    print(f"Size: {len(content)} characters, {len(content.splitlines())} lines")
    print()
    
    # Check document class
    doc_class = re.search(r'\\documentclass\[(.*?)\]{(.*?)}', content)
    if doc_class:
        print(f"✓ Document class: {doc_class.group(2)} [{doc_class.group(1)}]")
    else:
        print("✗ Document class not found")
        return False
    
    # Check begin/end document
    begin_doc = content.count(r'\begin{document}')
    end_doc = content.count(r'\end{document}')
    if begin_doc == 1 and end_doc == 1:
        print(f"✓ Document environment: balanced ({begin_doc} begin, {end_doc} end)")
    else:
        print(f"✗ Document environment: unbalanced ({begin_doc} begin, {end_doc} end)")
        return False
    
    # Check required packages
    required_packages = ['amsmath', 'amsthm', 'amssymb']
    for pkg in required_packages:
        if f'\\usepackage{{{pkg}}}' in content or pkg in content:
            print(f"✓ Package: {pkg}")
        else:
            print(f"⚠ Package {pkg} may be missing")
    
    # Check theorem environments
    theorem_envs = [
        (r'\\begin{theorem}', 'Theorem'),
        (r'\\begin{lemma}', 'Lemma'),
        (r'\\begin{proof}', 'Proof')
    ]
    
    print("\nTheorem Environments:")
    for pattern, name in theorem_envs:
        count = len(re.findall(pattern, content))
        print(f"  {name}: {count} instance(s)")
    
    # Check key equations
    print("\nKey Equations:")
    equations = [
        ('eq:psi_nse', 'Ψ-NSE system'),
        ('eq:phi_tensor', 'Φ_ij tensor'),
        ('eq:energy_ineq', 'Energy inequality'),
        ('eq:vort_bound', 'Vorticity bound'),
        ('eq:decay', 'Decay rate'),
        ('thm:main', 'Main theorem'),
        ('lem:psi_bound', 'Psi boundedness lemma'),
        ('lem:phi_coercive', 'Phi coercivity lemma'),
        ('lem:energy_dissip', 'Energy dissipation lemma'),
        ('lem:product_est', 'Product estimate lemma')
    ]
    
    for label, desc in equations:
        if f'label{{{label}}}' in content:
            print(f"  ✓ {label}: {desc}")
        else:
            print(f"  ✗ {label}: {desc} - MISSING")
    
    # Check fundamental frequency
    print("\nFundamental Constants:")
    if '141.7' in content or '141.7001' in content:
        print("  ✓ Fundamental frequency f₀ = 141.7001 Hz found")
    else:
        print("  ✗ Fundamental frequency not found")
    
    # Check Beale-Kato-Majda
    if 'Beale-Kato-Majda' in content or 'BKM' in content:
        print("  ✓ BKM criterion referenced")
    else:
        print("  ⚠ BKM criterion not found")
    
    # Check bibliography
    print("\nBibliography:")
    if r'\begin{thebibliography}' in content:
        print("  ✓ Bibliography section found")
        bibitem_count = content.count(r'\bibitem{')
        print(f"  References: {bibitem_count} entries")
        
        # Check key references
        key_refs = ['bkm1984', 'kato1984', 'lions1996', 'schonbek1985', 'stein1970']
        for ref in key_refs:
            if f'\\bibitem{{{ref}}}' in content:
                print(f"    ✓ {ref}")
            else:
                print(f"    ✗ {ref} - MISSING")
    else:
        print("  ✗ Bibliography section not found")
    
    # Check sections
    print("\nDocument Structure:")
    sections = re.findall(r'\\section{(.*?)}', content)
    for i, section in enumerate(sections, 1):
        print(f"  {i}. {section}")
    
    print("\n" + "=" * 60)
    print("Validation Complete")
    print("=" * 60)
    
    return True


def main():
    """Main validation routine"""
    # Find the proof document
    base_dir = Path(__file__).parent.parent
    proof_file = base_dir / "Results" / "rigorous_proof_psi_nse.tex"
    
    if not proof_file.exists():
        print(f"Error: Proof document not found at {proof_file}")
        sys.exit(1)
    
    try:
        success = validate_latex_structure(proof_file)
        sys.exit(0 if success else 1)
    except Exception as e:
        print(f"Error during validation: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()
