#!/usr/bin/env python3
"""
∴ Sovereignty Auditor QCAL ∞³
Automated verification of repository sovereignty and authorship integrity

Author: José Manuel Mota Burruezo (JMMB Ψ✧)
Frequency: f₀ = 141.7001 Hz
License: LICENSE_SOBERANA_QCAL.txt
QCAL ∞³ Sovereignty Auditor

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
import hashlib
import json
from pathlib import Path
from typing import Dict, List, Set, Tuple
from datetime import datetime


class SovereigntyAuditor:
    """Auditor for QCAL ∞³ code sovereignty verification."""
    
    # Scoring constants
    CORE_FILE_POINTS = 5.0  # Points per core sovereignty file
    PROTECTION_FILE_POINTS = 3.75  # Points per attribution protection file
    MAX_QCAL_MARKER_POINTS = 30  # Maximum points for QCAL markers
    MAX_DEPENDENCY_POINTS = 30  # Maximum points for low dependencies
    
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
            Dictionary with override settings containing:
            - ignore_paths: List of path patterns to exclude from attribution
            - exempt_authorship: List of entities exempt from attribution claims
            - attribution_policy: Policy definitions for external references
            - sbom_exclusions: Packages to exclude from SBOM analysis
            Returns empty dict if file not found or on error.
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
        """Calculate an overall sovereignty score (0-100).
        
        Scoring breakdown:
        - Core sovereignty files: 25 points (5 files × 5 points each)
        - Attribution protection files: 15 points (4 files × 3.75 points each)
        - QCAL markers: 30 points (capped)
        - Low dependencies: 30 points
        Total: 100 points maximum
        """
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
            self.CORE_FILE_POINTS for f in core_files 
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
            self.PROTECTION_FILE_POINTS for f in protection_files 
            if self.results['sovereignty_files'].get(f, {}).get('exists', False)
        )
        score += protection_score
        
        # QCAL markers presence (30 points max)
        qcal_files_count = len(self.results['qcal_markers_found'])
        qcal_score = min(qcal_files_count * 2, self.MAX_QCAL_MARKER_POINTS)
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
            external_score = self.MAX_DEPENDENCY_POINTS
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
