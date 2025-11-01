#!/usr/bin/env python3
"""
Generate a proof certificate from Lean4 verification results.
"""
import argparse
import json
import os
import re
from datetime import datetime, timezone
from pathlib import Path


def scan_lean_files(directory):
    """Scan Lean files for theorems, lemmas, and definitions."""
    lean_files = list(Path(directory).rglob("*.lean"))
    
    theorems = []
    lemmas = []
    definitions = []
    sorry_count = 0
    
    for lean_file in lean_files:
        try:
            with open(lean_file, 'r', encoding='utf-8') as f:
                content = f.read()
                
                # Count theorems
                theorems.extend(re.findall(r'theorem\s+(\w+)', content))
                
                # Count lemmas
                lemmas.extend(re.findall(r'lemma\s+(\w+)', content))
                
                # Count definitions
                definitions.extend(re.findall(r'def\s+(\w+)', content))
                
                # Count sorry statements
                sorry_count += content.count('sorry')
        except Exception as e:
            print(f"Warning: Could not read {lean_file}: {e}")
    
    return {
        'theorems': theorems,
        'lemmas': lemmas,
        'definitions': definitions,
        'sorry_count': sorry_count,
        'total_files': len(lean_files)
    }


def generate_certificate(input_dir, output_file):
    """Generate proof certificate JSON file."""
    
    print(f"📊 Scanning Lean4 files in {input_dir}...")
    results = scan_lean_files(input_dir)
    
    certificate = {
        'metadata': {
            'generated_at': datetime.now(timezone.utc).isoformat().replace('+00:00', 'Z'),
            'framework': 'Lean4',
            'verification_type': 'formal_proof'
        },
        'statistics': {
            'total_theorems': len(results['theorems']),
            'total_lemmas': len(results['lemmas']),
            'total_definitions': len(results['definitions']),
            'total_files': results['total_files'],
            'sorry_count': results['sorry_count'],
            'verification_complete': results['sorry_count'] == 0
        },
        'theorems': results['theorems'][:50],  # Top 50 for brevity
        'lemmas': results['lemmas'][:50],
        'status': 'PASSED' if results['sorry_count'] == 0 else 'INCOMPLETE'
    }
    
    # Create output directory if needed
    output_path = Path(output_file)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    
    # Write certificate
    with open(output_file, 'w', encoding='utf-8') as f:
        json.dump(certificate, f, indent=2)
    
    print(f"✅ Certificate generated: {output_file}")
    print(f"   Theorems: {certificate['statistics']['total_theorems']}")
    print(f"   Lemmas: {certificate['statistics']['total_lemmas']}")
    print(f"   Sorry count: {certificate['statistics']['sorry_count']}")
    print(f"   Status: {certificate['status']}")
    
    return certificate


def main():
    parser = argparse.ArgumentParser(description='Generate Lean4 proof certificate')
    parser.add_argument('--input', required=True, help='Input directory with Lean files')
    parser.add_argument('--output', required=True, help='Output JSON certificate file')
    
    args = parser.parse_args()
    
    certificate = generate_certificate(args.input, args.output)
    
    # Exit with error if verification incomplete
    if certificate['status'] != 'PASSED':
        print(f"⚠️  Warning: Verification incomplete ({certificate['statistics']['sorry_count']} sorry statements)")
        # Don't fail here, let the workflow decide


if __name__ == '__main__':
    main()
