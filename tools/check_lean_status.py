#!/usr/bin/env python3
"""
Check the status of the Lean formalization and report progress.

This script analyzes Lean files to count theorems, axioms, and sorry placeholders,
providing a quick overview of the formalization status.
"""

import os
import re
from pathlib import Path
from typing import Dict, List, Tuple


class LeanStatusChecker:
    """Checks the status of Lean formalization."""
    
    def __init__(self, base_path: str):
        self.base_path = Path(base_path)
        self.stats = {
            'files': 0,
            'theorems': 0,
            'lemmas': 0,
            'axioms': 0,
            'sorry_count': 0,
            'definitions': 0,
            'structures': 0,
            'lines': 0
        }
        self.file_details = []
        
    def analyze(self):
        """Analyze all Lean files."""
        lean_files = list(self.base_path.rglob('*.lean'))
        
        for lean_file in lean_files:
            if lean_file.name == 'lakefile.lean':
                continue
            
            self.stats['files'] += 1
            details = self._analyze_file(lean_file)
            self.file_details.append(details)
            
            # Update global stats
            self.stats['theorems'] += details['theorems']
            self.stats['lemmas'] += details['lemmas']
            self.stats['axioms'] += details['axioms']
            self.stats['sorry_count'] += details['sorry']
            self.stats['definitions'] += details['definitions']
            self.stats['structures'] += details['structures']
            self.stats['lines'] += details['lines']
    
    def _analyze_file(self, file_path: Path) -> Dict:
        """Analyze a single Lean file."""
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        details = {
            'path': str(file_path.relative_to(self.base_path)),
            'name': file_path.stem,
            'theorems': len(re.findall(r'theorem\s+\w+', content)),
            'lemmas': len(re.findall(r'lemma\s+\w+', content)),
            'axioms': len(re.findall(r'axiom\s+\w+', content)),
            'sorry': len(re.findall(r'\bsorry\b', content)),
            'definitions': len(re.findall(r'def\s+\w+', content)),
            'structures': len(re.findall(r'structure\s+\w+', content)),
            'lines': len(content.splitlines())
        }
        
        return details
    
    def generate_report(self) -> str:
        """Generate status report."""
        lines = []
        lines.append("=" * 70)
        lines.append("LEAN FORMALIZATION STATUS REPORT")
        lines.append("=" * 70)
        lines.append("")
        
        # Overall statistics
        lines.append("## Overall Statistics")
        lines.append("")
        lines.append(f"Total Files:        {self.stats['files']}")
        lines.append(f"Total Lines:        {self.stats['lines']}")
        lines.append("")
        lines.append(f"Theorems:           {self.stats['theorems']}")
        lines.append(f"Lemmas:             {self.stats['lemmas']}")
        lines.append(f"Definitions:        {self.stats['definitions']}")
        lines.append(f"Structures:         {self.stats['structures']}")
        lines.append("")
        lines.append(f"⚠️  Axioms (need proof): {self.stats['axioms']}")
        
        if self.stats['sorry_count'] > 0:
            lines.append(f"❌ Sorry placeholders:   {self.stats['sorry_count']} (MUST BE FIXED!)")
        else:
            lines.append(f"✅ Sorry placeholders:   0 (Good!)")
        
        lines.append("")
        
        # Completion percentage
        proven = self.stats['theorems'] + self.stats['lemmas']
        total = proven + self.stats['axioms']
        if total > 0:
            completion = (proven / total) * 100
            lines.append(f"Completion:         {completion:.1f}% ({proven}/{total} proven)")
        lines.append("")
        
        # Files with issues
        issues = [f for f in self.file_details if f['axioms'] > 0 or f['sorry'] > 0]
        if issues:
            lines.append("## Files Requiring Attention")
            lines.append("")
            
            # Sort by number of axioms + sorry (most issues first)
            issues.sort(key=lambda x: x['axioms'] + x['sorry'], reverse=True)
            
            lines.append(f"{'File':<40} {'Axioms':<8} {'Sorry':<8} {'Priority'}")
            lines.append("-" * 70)
            
            for f in issues:
                priority = "HIGH" if f['sorry'] > 0 else "MEDIUM"
                if f['axioms'] > 5:
                    priority = "HIGH"
                
                lines.append(f"{f['name']:<40} {f['axioms']:<8} {f['sorry']:<8} {priority}")
        
        lines.append("")
        
        # Status by category
        lines.append("## Status by Category")
        lines.append("")
        
        categories = {
            'Foundation': ['BasicDefinitions', 'UniformConstants', 'FunctionalSpaces'],
            'Core Theory': ['CalderonZygmundBesov', 'BesovEmbedding', 'DyadicRiccati', 'ParabolicCoercivity'],
            'Analysis': ['EnergyEstimates', 'VorticityControl', 'MisalignmentDefect'],
            'Closure': ['GlobalRiccati', 'RiccatiBesov', 'BKMClosure', 'BKMCriterion', 'UnifiedBKM'],
            'Main Results': ['MainTheorem', 'Theorem13_7', 'SerrinEndpoint']
        }
        
        for category, modules in categories.items():
            cat_theorems = 0
            cat_axioms = 0
            cat_sorry = 0
            
            for module in modules:
                for f in self.file_details:
                    if f['name'] == module:
                        cat_theorems += f['theorems'] + f['lemmas']
                        cat_axioms += f['axioms']
                        cat_sorry += f['sorry']
            
            total_cat = cat_theorems + cat_axioms
            if total_cat > 0:
                cat_completion = (cat_theorems / total_cat) * 100
                status = "✅" if cat_completion >= 90 else "🟡" if cat_completion >= 50 else "⚠️"
                lines.append(f"{status} {category:<15} {cat_completion:>5.1f}% complete ({cat_axioms} axioms, {cat_sorry} sorry)")
        
        lines.append("")
        lines.append("=" * 70)
        lines.append("")
        
        # Recommendations
        lines.append("## Next Steps")
        lines.append("")
        
        if self.stats['sorry_count'] > 0:
            lines.append("1. 🚨 URGENT: Remove all 'sorry' placeholders")
        
        # Find most critical axioms
        critical_files = [f for f in issues if f['name'] in ['CalderonZygmundBesov', 'DyadicRiccati', 'GlobalRiccati']]
        if critical_files:
            lines.append("2. 🎯 Focus on critical path modules:")
            for f in critical_files:
                lines.append(f"   - {f['name']} ({f['axioms']} axioms)")
        
        lines.append("3. 📚 Review FORMAL_PROOF_ROADMAP.md for detailed priorities")
        lines.append("4. 🔄 Run this script after each proof completion to track progress")
        
        lines.append("")
        lines.append("=" * 70)
        
        return '\n'.join(lines)
    
    def generate_json(self) -> str:
        """Generate JSON report for automated processing."""
        import json
        return json.dumps({
            'summary': self.stats,
            'files': self.file_details
        }, indent=2)


def main():
    """Main entry point."""
    import argparse
    
    parser = argparse.ArgumentParser(
        description='Check status of Lean formalization'
    )
    parser.add_argument(
        '--base-path',
        default='/home/runner/work/3D-Navier-Stokes/3D-Navier-Stokes/Lean4-Formalization',
        help='Base path for Lean files'
    )
    parser.add_argument(
        '--format',
        choices=['text', 'json'],
        default='text',
        help='Output format'
    )
    parser.add_argument(
        '--output',
        help='Output file (default: stdout)'
    )
    
    args = parser.parse_args()
    
    checker = LeanStatusChecker(args.base_path)
    checker.analyze()
    
    if args.format == 'text':
        report = checker.generate_report()
    else:
        report = checker.generate_json()
    
    if args.output:
        with open(args.output, 'w') as f:
            f.write(report)
        print(f"Report saved to {args.output}")
    else:
        print(report)


if __name__ == '__main__':
    main()
