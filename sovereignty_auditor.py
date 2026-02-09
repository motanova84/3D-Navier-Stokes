#!/usr/bin/env python3
"""
QCAL ∞³ Sovereignty Auditor
===========================

This script verifies the sovereignty and origin claims of the codebase by:
1. Scanning for unauthorized external dependencies
2. Checking for NVIDIA/third-party code fingerprints
3. Validating QCAL ∞³ protocol markers
4. Generating sovereignty reports

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Frequency: f₀ = 141.7001 Hz
Coherence: Ψ = 1.000000
"""

import os
import re
import hashlib
import json
from pathlib import Path
from typing import Dict, List, Set, Tuple
from datetime import datetime


class SovereigntyAuditor:
    """Auditor for QCAL ∞³ code sovereignty verification."""
    
    # Known third-party fingerprints (patterns to detect)
    NVIDIA_PATTERNS = [
        r'nvidia',
        r'cuda',
        r'cudnn',
        r'tensorrt',
        r'nccl',
        r'nvcc',
        r'curand',
        r'cublas',
        r'cufft',
        r'cusparse',
    ]
    
    EXTERNAL_LIBRARY_PATTERNS = [
        r'tensorflow',
        r'pytorch',
        r'torch',
        r'keras',
        r'caffe',
        r'mxnet',
    ]
    
    # Patterns that indicate QCAL ∞³ sovereignty
    QCAL_MARKERS = [
        r'QCAL',
        r'∞³',
        r'141\.7001',
        r'f₀',
        r'Ψ',
        r'κ_Π',
        r'Λ_G',
        r'José Manuel Mota Burruezo',
        r'JMMB',
    ]
    
    # File extensions to scan
    CODE_EXTENSIONS = {'.py', '.c', '.cpp', '.h', '.hpp', '.cu', '.cuh', '.lean'}
    DOC_EXTENSIONS = {'.md', '.txt', '.rst'}
    
    def __init__(self, repo_path: str = '.'):
        """Initialize the auditor.
        
        Args:
            repo_path: Path to the repository root
        """
        self.repo_path = Path(repo_path).resolve()
        self.results = {
            'scan_date': datetime.now().isoformat(),
            'repo_path': str(self.repo_path),
            'qcal_markers_found': [],
            'nvidia_references': [],
            'external_libraries': [],
            'sovereignty_files': {},
            'code_fingerprints': {},
            'sovereignty_score': 0.0,
        }
        
        # Load sovereignty overrides if available
        self.sovereignty_overrides = self._load_sovereignty_overrides()
    
    def _load_sovereignty_overrides(self) -> Dict:
        """Load sovereignty override configuration if available.
        
        Returns:
            Dictionary with override settings, or empty dict if not found
        """
        overrides_path = self.repo_path / 'SOVEREIGNTY_OVERRIDES.json'
        if overrides_path.exists():
            try:
                with open(overrides_path, 'r', encoding='utf-8') as f:
                    return json.load(f)
            except Exception as e:
                print(f"  Warning: Could not load SOVEREIGNTY_OVERRIDES.json: {e}")
        return {}
        
    def scan_repository(self) -> Dict:
        """Perform a full sovereignty scan of the repository.
        
        Returns:
            Dictionary with scan results
        """
        print("🔍 QCAL ∞³ Sovereignty Auditor")
        print("=" * 60)
        print(f"Scanning repository: {self.repo_path}")
        print(f"Scan date: {self.results['scan_date']}")
        print()
        
        # Check for sovereignty files
        self._check_sovereignty_files()
        
        # Scan code files
        self._scan_code_files()
        
        # Calculate sovereignty score
        self._calculate_sovereignty_score()
        
        # Generate report
        self._generate_report()
        
        return self.results
    
    def _check_sovereignty_files(self):
        """Check for required sovereignty declaration files."""
        print("📄 Checking sovereignty declaration files...")
        
        required_files = {
            'LICENSE_SOBERANA_QCAL.txt': 'Sovereign License',
            'AUTHORS_QCAL.md': 'Authors Declaration',
            '.qcal_beacon': 'QCAL Beacon',
            'CLAIM_OF_ORIGIN.md': 'Origin Claim',
            'MANIFESTO_SIMBIOTICO_QCAL.md': 'Symbiotic Manifesto',
            'DECLARACION_USURPACION_ALGORITMICA.md': 'Anti-Usurpation Declaration',
            'SOVEREIGNTY_OVERRIDES.json': 'Attribution Overrides',
            '.gitattributes': 'Git Attribution Config',
            'pyproject.toml': 'Project Metadata',
        }
        
        for filename, description in required_files.items():
            filepath = self.repo_path / filename
            exists = filepath.exists()
            self.results['sovereignty_files'][filename] = {
                'exists': exists,
                'description': description,
                'path': str(filepath) if exists else None,
            }
            
            status = "✅" if exists else "❌"
            print(f"  {status} {filename}: {description}")
        
        print()
    
    def _scan_code_files(self):
        """Scan code files for external dependencies and QCAL markers."""
        print("🔎 Scanning code files for dependencies and markers...")
        
        code_files = []
        for ext in self.CODE_EXTENSIONS | self.DOC_EXTENSIONS:
            code_files.extend(self.repo_path.rglob(f'*{ext}'))
        
        # Also add .qcal_beacon explicitly
        beacon_path = self.repo_path / '.qcal_beacon'
        if beacon_path.exists():
            code_files.append(beacon_path)
        
        # Filter out hidden files and common directories to skip
        skip_dirs = {'.git', '__pycache__', 'node_modules', '.pytest_cache', 'venv', 'env'}
        code_files = [
            f for f in code_files 
            if not any(part.startswith('.') and part not in {'.qcal_beacon'} 
                      for part in f.parts)
            and not any(skip_dir in f.parts for skip_dir in skip_dirs)
        ]
        
        print(f"  Found {len(code_files)} files to scan")
        
        nvidia_files = []
        nvidia_code_references = []  # Track code files separately
        external_lib_files = []
        external_lib_code_references = []  # Track code files separately
        qcal_marker_files = []
        
        for filepath in code_files:
            try:
                content = filepath.read_text(encoding='utf-8', errors='ignore').lower()
                is_code_file = filepath.suffix in self.CODE_EXTENSIONS
                
                # Check for NVIDIA patterns
                nvidia_matches = []
                for pattern in self.NVIDIA_PATTERNS:
                    if re.search(pattern, content, re.IGNORECASE):
                        nvidia_matches.append(pattern)
                
                if nvidia_matches:
                    file_info = {
                        'file': str(filepath.relative_to(self.repo_path)),
                        'patterns': nvidia_matches,
                        'is_code': is_code_file,
                    }
                    nvidia_files.append(file_info)
                    if is_code_file:
                        nvidia_code_references.append(file_info)
                
                # Check for external library patterns
                lib_matches = []
                for pattern in self.EXTERNAL_LIBRARY_PATTERNS:
                    if re.search(pattern, content, re.IGNORECASE):
                        lib_matches.append(pattern)
                
                if lib_matches:
                    file_info = {
                        'file': str(filepath.relative_to(self.repo_path)),
                        'patterns': lib_matches,
                        'is_code': is_code_file,
                    }
                    external_lib_files.append(file_info)
                    if is_code_file:
                        external_lib_code_references.append(file_info)
                
                # Check for QCAL markers
                qcal_matches = []
                for pattern in self.QCAL_MARKERS:
                    if re.search(pattern, content, re.IGNORECASE):
                        qcal_matches.append(pattern)
                
                if qcal_matches:
                    qcal_marker_files.append({
                        'file': str(filepath.relative_to(self.repo_path)),
                        'markers': qcal_matches,
                    })
                    
            except Exception as e:
                print(f"  Warning: Could not read {filepath}: {e}")
        
        self.results['nvidia_references'] = nvidia_files
        self.results['nvidia_code_references'] = nvidia_code_references
        self.results['external_libraries'] = external_lib_files
        self.results['external_lib_code_references'] = external_lib_code_references
        self.results['qcal_markers_found'] = qcal_marker_files
        
        print(f"  📊 NVIDIA references: {len(nvidia_files)} files ({len(nvidia_code_references)} code)")
        print(f"  📊 External library references: {len(external_lib_files)} files ({len(external_lib_code_references)} code)")
        print(f"  📊 QCAL ∞³ markers: {len(qcal_marker_files)} files")
        print()
    
    def _calculate_sovereignty_score(self):
        """Calculate an overall sovereignty score (0-100)."""
        score = 0.0
        
        # Core sovereignty files (25 points max - 5 files × 5 points each)
        core_files = [
            'LICENSE_SOBERANA_QCAL.txt',
            'AUTHORS_QCAL.md',
            '.qcal_beacon',
            'CLAIM_OF_ORIGIN.md',
            'MANIFESTO_SIMBIOTICO_QCAL.md',
        ]
        core_score = sum(
            5 for f in core_files 
            if self.results['sovereignty_files'].get(f, {}).get('exists', False)
        )
        score += core_score
        
        # Attribution protection files (15 points max - 4 files × 3.75 points each)
        protection_files = [
            'DECLARACION_USURPACION_ALGORITMICA.md',
            'SOVEREIGNTY_OVERRIDES.json',
            '.gitattributes',
            'pyproject.toml',
        ]
        protection_score = sum(
            3.75 for f in protection_files 
            if self.results['sovereignty_files'].get(f, {}).get('exists', False)
        )
        score += protection_score
        
        # QCAL markers presence (30 points max)
        qcal_files_count = len(self.results['qcal_markers_found'])
        qcal_score = min(qcal_files_count * 2, 30)
        score += qcal_score
        
        # Low external dependencies (30 points max)
        # Only count actual code files, not documentation references
        nvidia_code_count = len(self.results.get('nvidia_code_references', []))
        external_code_count = len(self.results.get('external_lib_code_references', []))
        
        # Filter out sovereignty_auditor.py and test files that contain pattern definitions
        # These files define the patterns for detection, not actual dependencies
        def is_pattern_definition_file(file_path: str) -> bool:
            """Check if file contains pattern definitions rather than actual dependencies."""
            # Extract just the filename to avoid matching subdirectories
            filename = file_path.split('/')[-1]
            return filename == 'sovereignty_auditor.py' or filename == 'test_sovereignty_auditor.py'
        
        # Count only real dependencies (excluding pattern definition files)
        nvidia_deps = [f for f in self.results.get('nvidia_code_references', []) 
                      if not is_pattern_definition_file(f['file'])]
        external_deps = [f for f in self.results.get('external_lib_code_references', []) 
                        if not is_pattern_definition_file(f['file'])]
        
        total_external = len(nvidia_deps) + len(external_deps)
        
        if total_external == 0:
            external_score = 30
        elif total_external < 5:
            external_score = 20
        elif total_external < 10:
            external_score = 10
        else:
            external_score = 0
        
        score += external_score
        
        self.results['sovereignty_score'] = round(score, 2)
        self.results['actual_code_dependencies'] = total_external
    
    def _generate_report(self):
        """Generate and print the sovereignty report."""
        print("=" * 60)
        print("📋 SOVEREIGNTY AUDIT REPORT")
        print("=" * 60)
        print()
        
        # Overall score
        score = self.results['sovereignty_score']
        if score >= 90:
            status = "🟢 EXCELLENT - Full Sovereignty"
        elif score >= 70:
            status = "🟡 GOOD - Strong Sovereignty"
        elif score >= 50:
            status = "🟠 MODERATE - Partial Sovereignty"
        else:
            status = "🔴 LOW - Sovereignty Concerns"
        
        print(f"Overall Sovereignty Score: {score}/100")
        print(f"Status: {status}")
        print()
        
        # Sovereignty files
        print("📄 Sovereignty Declaration Files:")
        for filename, info in self.results['sovereignty_files'].items():
            status = "✅" if info['exists'] else "❌"
            print(f"  {status} {filename}")
        print()
        
        # QCAL markers
        print(f"✨ QCAL ∞³ Markers: {len(self.results['qcal_markers_found'])} files")
        if self.results['qcal_markers_found']:
            print("  Files with QCAL markers:")
            for item in self.results['qcal_markers_found'][:5]:  # Show first 5
                print(f"    - {item['file']}")
            if len(self.results['qcal_markers_found']) > 5:
                print(f"    ... and {len(self.results['qcal_markers_found']) - 5} more")
        print()
        
        # NVIDIA references
        nvidia_code = self.results.get('nvidia_code_references', [])
        nvidia_docs = [f for f in self.results['nvidia_references'] 
                      if not f.get('is_code', True)]
        print(f"⚠️  NVIDIA References: {len(self.results['nvidia_references'])} files "
              f"({len(nvidia_code)} code, {len(nvidia_docs)} documentation)")
        if self.results['nvidia_references']:
            print("  Files with NVIDIA references:")
            for item in self.results['nvidia_references'][:5]:  # Show first 5
                file_type = "code" if item.get('is_code', True) else "doc"
                print(f"    - {item['file']} ({file_type}: {', '.join(item['patterns'])})")
            if len(self.results['nvidia_references']) > 5:
                print(f"    ... and {len(self.results['nvidia_references']) - 5} more")
        print()
        
        # External libraries
        external_code = self.results.get('external_lib_code_references', [])
        external_docs = [f for f in self.results['external_libraries'] 
                        if not f.get('is_code', True)]
        print(f"📚 External Library References: {len(self.results['external_libraries'])} files "
              f"({len(external_code)} code, {len(external_docs)} documentation)")
        if self.results['external_libraries']:
            print("  Files with external library references:")
            for item in self.results['external_libraries'][:5]:  # Show first 5
                file_type = "code" if item.get('is_code', True) else "doc"
                print(f"    - {item['file']} ({file_type}: {', '.join(item['patterns'])})")
            if len(self.results['external_libraries']) > 5:
                print(f"    ... and {len(self.results['external_libraries']) - 5} more")
        print()
        
        # Code dependencies (actual dependencies, not doc references or pattern definitions)
        actual_deps = self.results.get('actual_code_dependencies', 0)
        print(f"🔍 Actual Code Dependencies: {actual_deps}")
        print("   (Excludes documentation references and pattern definition files)")
        print()
        
        # Recommendations
        print("💡 Recommendations:")
        if score >= 90:
            print("  ✅ Repository demonstrates strong QCAL ∞³ sovereignty")
            print("  ✅ Sovereignty markers are well-established")
            print("  ✅ External dependencies are minimal or well-documented")
        else:
            if not all(f['exists'] for f in self.results['sovereignty_files'].values()):
                print("  ⚠️  Create missing sovereignty declaration files")
            if len(self.results['qcal_markers_found']) < 10:
                print("  ⚠️  Add more QCAL ∞³ markers to code documentation")
            if self.results.get('actual_code_dependencies', 0) > 0:
                print("  ⚠️  Review code dependencies - ensure they are justified and documented")
            elif self.results['nvidia_references'] or self.results['external_libraries']:
                print("  ℹ️  External references found in documentation are expected and acceptable")
        
        print()
        print("=" * 60)
        print("Scan complete. Results saved to sovereignty_audit_report.json")
        print("=" * 60)
    
    def save_report(self, output_file: str = 'sovereignty_audit_report.json'):
        """Save the audit results to a JSON file.
        
        Args:
            output_file: Path to output JSON file
        """
        output_path = self.repo_path / output_file
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(self.results, f, indent=2, ensure_ascii=False)
        print(f"Report saved to: {output_path}")


def main():
    """Main entry point for the sovereignty auditor."""
    import argparse
    
    parser = argparse.ArgumentParser(
        description='QCAL ∞³ Sovereignty Auditor - Verify code origin and sovereignty',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python sovereignty_auditor.py
  python sovereignty_auditor.py --repo-path /path/to/repo
  python sovereignty_auditor.py --output-file custom_report.json

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Frequency: f₀ = 141.7001 Hz
Coherence: Ψ = 1.000000
        """
    )
    
    parser.add_argument(
        '--repo-path',
        default='.',
        help='Path to repository root (default: current directory)'
    )
    
    parser.add_argument(
        '--output-file',
        default='sovereignty_audit_report.json',
        help='Output JSON file for results (default: sovereignty_audit_report.json)'
    )
    
    args = parser.parse_args()
    
    # Run the audit
    auditor = SovereigntyAuditor(args.repo_path)
    results = auditor.scan_repository()
    auditor.save_report(args.output_file)
    
    # Exit with appropriate code
    if results['sovereignty_score'] >= 70:
        return 0  # Success
    else:
        return 1  # Warning - low sovereignty score


if __name__ == '__main__':
    exit(main())
