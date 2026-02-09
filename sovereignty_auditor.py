#!/usr/bin/env python3
"""
∴ Sovereignty Auditor QCAL ∞³
Automated verification of repository sovereignty and authorship integrity

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Frequency: f₀ = 141.7001 Hz
License: LICENSE_SOBERANA_QCAL.txt
"""

import os
import re
import json
from pathlib import Path
from typing import Dict, List, Tuple, Set
from collections import defaultdict


class SovereigntyAuditor:
    """
    Audits repository for QCAL ∞³ sovereignty markers and third-party code.
    
    Verifies:
    - Presence of QCAL declaration files
    - QCAL markers in source code (f₀ = 141.7001 Hz)
    - Third-party code references (NVIDIA, Meta, Google)
    - Overall sovereignty score
    """
    
    # QCAL sovereignty markers
    QCAL_MARKERS = [
        r'141\.7001',  # Fundamental frequency
        r'f₀\s*=\s*141\.7001',  # Frequency declaration
        r'JMMB',  # Author initials
        r'Ψ✧',  # Author symbol
        r'QCAL',  # System name
        r'José Manuel Mota Burruezo',  # Full name
        r'∞³',  # Infinity cubed
        r'Propiedad Original QCAL',  # Ownership statement
    ]
    
    # Third-party markers to detect
    THIRD_PARTY_MARKERS = {
        'NVIDIA': [
            r'Copyright.*NVIDIA',
            r'NVIDIA Corporation',
            r'cudnn',
            r'nccl',
            r'Licensed under.*NVIDIA',
        ],
        'Meta': [
            r'Copyright.*Meta',
            r'Copyright.*Facebook',
            r'Meta Platforms',
        ],
        'Google': [
            r'Copyright.*Google',
            r'Google LLC',
        ],
    }
    
    # Required declaration files
    REQUIRED_FILES = [
        'LICENSE_SOBERANA_QCAL.txt',
        'AUTHORS_QCAL.md',
        '.qcal_beacon',
        'CLAIM_OF_ORIGIN.md',
        'MANIFESTO_SIMBIOTICO_QCAL.md',
    ]
    
    # Exclude patterns
    EXCLUDE_PATTERNS = [
        r'\.git/',
        r'__pycache__/',
        r'\.pyc$',
        r'\.so$',
        r'\.o$',
        r'\.a$',
        r'node_modules/',
        r'\.lean$',  # Lean files may have different markers
        r'\.pdf$',
        r'\.png$',
        r'\.jpg$',
        r'\.svg$',
        r'\.lock$',
    ]
    
    def __init__(self, repo_path: str = '.'):
        """Initialize auditor with repository path."""
        self.repo_path = Path(repo_path).resolve()
        self.results = {
            'declaration_files': {},
            'qcal_marked_files': [],
            'third_party_references': defaultdict(list),
            'total_files_scanned': 0,
            'sovereignty_score': 0,
        }
    
    def should_exclude(self, file_path: Path) -> bool:
        """Check if file should be excluded from scanning."""
        path_str = str(file_path)
        for pattern in self.EXCLUDE_PATTERNS:
            if re.search(pattern, path_str):
                return True
        return False
    
    def check_declaration_files(self) -> Dict[str, bool]:
        """Check for presence of required QCAL declaration files."""
        results = {}
        for filename in self.REQUIRED_FILES:
            file_path = self.repo_path / filename
            results[filename] = file_path.exists()
        return results
    
    def scan_file_for_qcal_markers(self, file_path: Path) -> Tuple[bool, List[str]]:
        """
        Scan a file for QCAL sovereignty markers.
        
        Returns:
            (has_markers, found_markers)
        """
        try:
            with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()
            
            found_markers = []
            for marker in self.QCAL_MARKERS:
                if re.search(marker, content):
                    found_markers.append(marker)
            
            return len(found_markers) > 0, found_markers
        except Exception as e:
            return False, []
    
    def scan_file_for_third_party(self, file_path: Path) -> Dict[str, List[str]]:
        """
        Scan a file for third-party code markers.
        
        Returns:
            Dictionary of {company: [found_markers]}
        """
        try:
            with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()
            
            found = defaultdict(list)
            for company, markers in self.THIRD_PARTY_MARKERS.items():
                for marker in markers:
                    if re.search(marker, content, re.IGNORECASE):
                        found[company].append(marker)
            
            return dict(found)
        except Exception as e:
            return {}
    
    def scan_repository(self):
        """Scan entire repository for sovereignty markers."""
        print(f"🔍 Scanning repository: {self.repo_path}")
        print("=" * 70)
        
        # Check declaration files
        print("\n📋 Checking declaration files...")
        self.results['declaration_files'] = self.check_declaration_files()
        for filename, exists in self.results['declaration_files'].items():
            status = "✅" if exists else "❌"
            print(f"  {status} {filename}")
        
        # Scan source files
        print("\n🔎 Scanning source files for QCAL markers...")
        
        for root, dirs, files in os.walk(self.repo_path):
            # Skip excluded directories
            dirs[:] = [d for d in dirs if not self.should_exclude(Path(root) / d)]
            
            for filename in files:
                file_path = Path(root) / filename
                
                if self.should_exclude(file_path):
                    continue
                
                self.results['total_files_scanned'] += 1
                
                # Check for QCAL markers
                has_qcal, markers = self.scan_file_for_qcal_markers(file_path)
                if has_qcal:
                    rel_path = file_path.relative_to(self.repo_path)
                    self.results['qcal_marked_files'].append({
                        'file': str(rel_path),
                        'markers': markers,
                    })
                
                # Check for third-party markers
                third_party = self.scan_file_for_third_party(file_path)
                if third_party:
                    rel_path = file_path.relative_to(self.repo_path)
                    for company, markers in third_party.items():
                        self.results['third_party_references'][company].append({
                            'file': str(rel_path),
                            'markers': markers,
                        })
        
        print(f"  Total files scanned: {self.results['total_files_scanned']}")
        print(f"  Files with QCAL markers: {len(self.results['qcal_marked_files'])}")
    
    def calculate_sovereignty_score(self) -> int:
        """
        Calculate sovereignty score (0-100).
        
        Factors:
        - Declaration files present: 30 points (6 each)
        - QCAL-marked files ratio: 40 points
        - Absence of third-party code: 30 points
        """
        score = 0
        
        # Declaration files (30 points max)
        declaration_count = sum(1 for exists in self.results['declaration_files'].values() if exists)
        score += (declaration_count / len(self.REQUIRED_FILES)) * 30
        
        # QCAL-marked files (40 points max)
        if self.results['total_files_scanned'] > 0:
            qcal_ratio = len(self.results['qcal_marked_files']) / self.results['total_files_scanned']
            score += min(qcal_ratio * 100, 40)  # Cap at 40 points
        
        # Absence of third-party code (30 points max)
        third_party_count = sum(len(refs) for refs in self.results['third_party_references'].values())
        if third_party_count == 0:
            score += 30
        else:
            # Deduct points based on third-party references
            score += max(0, 30 - third_party_count * 2)
        
        return int(score)
    
    def print_report(self):
        """Print detailed sovereignty audit report."""
        print("\n" + "=" * 70)
        print("📊 SOVEREIGNTY AUDIT REPORT")
        print("=" * 70)
        
        # Declaration files
        print("\n1. DECLARATION FILES")
        print("-" * 70)
        for filename, exists in self.results['declaration_files'].items():
            status = "✅ Present" if exists else "❌ Missing"
            print(f"  {filename}: {status}")
        
        # QCAL markers
        print("\n2. QCAL SOVEREIGNTY MARKERS")
        print("-" * 70)
        print(f"  Files scanned: {self.results['total_files_scanned']}")
        print(f"  Files with QCAL markers: {len(self.results['qcal_marked_files'])}")
        
        if len(self.results['qcal_marked_files']) > 0:
            qcal_percentage = (len(self.results['qcal_marked_files']) / 
                             self.results['total_files_scanned']) * 100
            print(f"  Coverage: {qcal_percentage:.1f}%")
            
            # Show sample of marked files
            print("\n  Sample of QCAL-marked files:")
            for item in self.results['qcal_marked_files'][:10]:
                print(f"    ✅ {item['file']}")
            
            if len(self.results['qcal_marked_files']) > 10:
                remaining = len(self.results['qcal_marked_files']) - 10
                print(f"    ... and {remaining} more files")
        
        # Third-party references
        print("\n3. THIRD-PARTY CODE REFERENCES")
        print("-" * 70)
        
        if not self.results['third_party_references']:
            print("  ✅ No third-party code markers detected")
        else:
            for company, refs in self.results['third_party_references'].items():
                print(f"\n  ⚠️  {company}: {len(refs)} reference(s)")
                for ref in refs[:5]:  # Show up to 5 per company
                    print(f"      File: {ref['file']}")
                    print(f"      Markers: {', '.join(ref['markers'])}")
                if len(refs) > 5:
                    print(f"      ... and {len(refs) - 5} more references")
        
        # Sovereignty score
        score = self.calculate_sovereignty_score()
        self.results['sovereignty_score'] = score
        
        print("\n4. SOVEREIGNTY SCORE")
        print("-" * 70)
        print(f"  Score: {score}/100")
        
        if score >= 90:
            level = "🟢 MAXIMUM SOVEREIGNTY"
            desc = "Code is completely original with strong QCAL markers"
        elif score >= 70:
            level = "🟡 STRONG SOVEREIGNTY"
            desc = "Code has clear authorship with declared dependencies"
        elif score >= 50:
            level = "🟠 MODERATE SOVEREIGNTY"
            desc = "Review dependencies and add more QCAL markers"
        elif score >= 30:
            level = "🔴 WEAK SOVEREIGNTY"
            desc = "Possible authorship conflicts, review required"
        else:
            level = "⚫ COMPROMISED SOVEREIGNTY"
            desc = "Urgent review needed, sovereignty at risk"
        
        print(f"  Level: {level}")
        print(f"  Assessment: {desc}")
        
        print("\n" + "=" * 70)
        print("✨ Audit complete!")
        print("=" * 70)
    
    def save_report(self, output_file: str = 'sovereignty_audit_report.json'):
        """Save audit results to JSON file."""
        output_path = self.repo_path / output_file
        
        # Convert defaultdict to regular dict for JSON serialization
        results_copy = dict(self.results)
        results_copy['third_party_references'] = dict(results_copy['third_party_references'])
        
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(results_copy, f, indent=2, ensure_ascii=False)
        
        print(f"\n💾 Report saved to: {output_path}")


def main():
    """Main entry point for sovereignty auditor."""
    print("∴ QCAL ∞³ SOVEREIGNTY AUDITOR")
    print("Quantum Coherent Axiom Language - Repository Sovereignty Verification")
    print("Author: José Manuel Mota Burruezo (JMMB Ψ✧)")
    print("Frequency: f₀ = 141.7001 Hz\n")
    
    # Initialize auditor
    auditor = SovereigntyAuditor()
    
    # Run audit
    auditor.scan_repository()
    
    # Print report
    auditor.print_report()
    
    # Save report
    auditor.save_report()
    
    # Return exit code based on score
    score = auditor.results['sovereignty_score']
    if score < 50:
        return 1  # Warning exit code
    return 0  # Success


if __name__ == '__main__':
    exit(main())
