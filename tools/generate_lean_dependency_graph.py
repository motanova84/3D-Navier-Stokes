#!/usr/bin/env python3
"""
Generate dependency graphs for Lean formalization files.

This script analyzes Lean 4 files to extract import dependencies and generates
visual dependency graphs in multiple formats (Mermaid, DOT/Graphviz, ASCII).
"""

import os
import re
from pathlib import Path
from collections import defaultdict, deque
from typing import Dict, List, Set, Tuple


class LeanDependencyAnalyzer:
    """Analyzes dependencies between Lean files."""
    
    def __init__(self, base_path: str):
        self.base_path = Path(base_path)
        self.files: Dict[str, Path] = {}
        self.imports: Dict[str, List[str]] = {}
        self.reverse_deps: Dict[str, List[str]] = defaultdict(list)
        
    def scan_files(self):
        """Scan directory for Lean files."""
        for lean_file in self.base_path.rglob('*.lean'):
            if lean_file.name == 'lakefile.lean':
                continue
            name = self._get_module_name(lean_file)
            self.files[name] = lean_file
            self.imports[name] = self._extract_imports(lean_file)
        
        # Build reverse dependency map
        for module, deps in self.imports.items():
            for dep in deps:
                self.reverse_deps[dep].append(module)
    
    def _get_module_name(self, file_path: Path) -> str:
        """Get module name from file path."""
        rel_path = file_path.relative_to(self.base_path)
        if str(rel_path).startswith('NavierStokes/'):
            return file_path.stem
        return str(rel_path).replace('.lean', '').replace('/', '_')
    
    def _extract_imports(self, file_path: Path) -> List[str]:
        """Extract NavierStokes imports from a Lean file."""
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        pattern = r'import\s+NavierStokes\.([\w\.]+)'
        imports = re.findall(pattern, content)
        return imports
    
    def get_dependency_levels(self) -> Dict[str, int]:
        """Calculate dependency level for each module (0 = no deps)."""
        levels = {}
        
        def calculate_level(module: str, visited: Set[str]) -> int:
            if module in levels:
                return levels[module]
            if module in visited:
                return 0  # Circular dependency, treat as base
            
            visited.add(module)
            deps = self.imports.get(module, [])
            if not deps:
                levels[module] = 0
                return 0
            
            max_level = 0
            for dep in deps:
                dep_level = calculate_level(dep, visited.copy())
                max_level = max(max_level, dep_level + 1)
            
            levels[module] = max_level
            return max_level
        
        for module in self.files.keys():
            calculate_level(module, set())
        
        return levels
    
    def classify_module(self, name: str) -> str:
        """Classify module by type."""
        if name in ['MainTheorem', 'Theorem13_7', 'SerrinEndpoint']:
            return 'main'
        elif 'BKM' in name or 'Closure' in name or 'Unified' in name:
            return 'closure'
        elif 'Riccati' in name:
            return 'riccati'
        elif name in ['BasicDefinitions', 'UniformConstants', 'FunctionalSpaces']:
            return 'foundation'
        else:
            return 'core'
    
    def generate_mermaid(self, output_file: str = None) -> str:
        """Generate Mermaid diagram."""
        lines = ["```mermaid", "graph TD"]
        
        # Add nodes with styling
        for name in sorted(self.files.keys()):
            module_type = self.classify_module(name)
            if module_type == 'main':
                lines.append(f"    {name}[{name}]:::mainTheorem")
            elif module_type == 'closure':
                lines.append(f"    {name}[{name}]:::closure")
            elif module_type == 'riccati':
                lines.append(f"    {name}[{name}]:::riccati")
            elif module_type == 'foundation':
                lines.append(f"    {name}[{name}]:::foundation")
            else:
                lines.append(f"    {name}[{name}]")
        
        # Add edges
        for name, deps in sorted(self.imports.items()):
            for dep in deps:
                lines.append(f"    {dep} --> {name}")
        
        # Add styling
        lines.append("")
        lines.append("    classDef mainTheorem fill:#ff6b6b,stroke:#c92a2a,stroke-width:3px,color:#fff")
        lines.append("    classDef closure fill:#4dabf7,stroke:#1971c2,stroke-width:2px,color:#fff")
        lines.append("    classDef riccati fill:#51cf66,stroke:#2b8a3e,stroke-width:2px,color:#fff")
        lines.append("    classDef foundation fill:#ffd43b,stroke:#f59f00,stroke-width:2px,color:#000")
        lines.append("```")
        
        result = '\n'.join(lines)
        
        if output_file:
            with open(output_file, 'w') as f:
                f.write(result)
        
        return result
    
    def generate_dot(self, output_file: str = None) -> str:
        """Generate GraphViz DOT format."""
        lines = ["digraph LeanDependencies {"]
        lines.append("    rankdir=BT;")
        lines.append("    node [shape=box, style=filled];")
        lines.append("")
        
        # Add nodes with colors
        for name in sorted(self.files.keys()):
            module_type = self.classify_module(name)
            colors = {
                'main': 'fillcolor="#ff6b6b", fontcolor=white',
                'closure': 'fillcolor="#4dabf7", fontcolor=white',
                'riccati': 'fillcolor="#51cf66", fontcolor=white',
                'foundation': 'fillcolor="#ffd43b", fontcolor=black',
                'core': 'fillcolor="#e9ecef"'
            }
            color = colors.get(module_type, colors['core'])
            lines.append(f'    "{name}" [{color}];')
        
        lines.append("")
        
        # Add edges
        for name, deps in sorted(self.imports.items()):
            for dep in deps:
                lines.append(f'    "{dep}" -> "{name}";')
        
        lines.append("}")
        
        result = '\n'.join(lines)
        
        if output_file:
            with open(output_file, 'w') as f:
                f.write(result)
        
        return result
    
    def generate_ascii_tree(self, root_module: str = None) -> str:
        """Generate ASCII dependency tree."""
        if root_module is None:
            # Find main theorems
            main_modules = [m for m in self.files.keys() 
                          if self.classify_module(m) == 'main']
            if not main_modules:
                return "No main theorem modules found."
            root_module = main_modules[0]
        
        lines = [f"Dependency tree for {root_module}:"]
        lines.append("")
        
        def print_tree(module: str, prefix: str = "", visited: Set[str] = None):
            if visited is None:
                visited = set()
            
            if module in visited:
                lines.append(f"{prefix}├─ {module} (circular)")
                return
            
            visited.add(module)
            deps = self.imports.get(module, [])
            
            for i, dep in enumerate(sorted(deps)):
                is_last = (i == len(deps) - 1)
                connector = "└─" if is_last else "├─"
                lines.append(f"{prefix}{connector} {dep}")
                
                extension = "   " if is_last else "│  "
                print_tree(dep, prefix + extension, visited.copy())
        
        print_tree(root_module)
        return '\n'.join(lines)
    
    def generate_statistics(self) -> str:
        """Generate dependency statistics."""
        lines = ["# Lean Formalization Statistics"]
        lines.append("")
        lines.append(f"**Total Modules**: {len(self.files)}")
        lines.append("")
        
        # Modules by type
        types = defaultdict(list)
        for name in self.files.keys():
            types[self.classify_module(name)].append(name)
        
        lines.append("## Modules by Type")
        lines.append("")
        for module_type in ['foundation', 'core', 'riccati', 'closure', 'main']:
            if module_type in types:
                count = len(types[module_type])
                lines.append(f"- **{module_type.title()}**: {count} modules")
        lines.append("")
        
        # Dependency levels
        levels = self.get_dependency_levels()
        max_level = max(levels.values()) if levels else 0
        
        lines.append("## Dependency Depth")
        lines.append("")
        lines.append(f"**Maximum dependency depth**: {max_level}")
        lines.append("")
        
        for level in range(max_level + 1):
            modules_at_level = [m for m, l in levels.items() if l == level]
            if modules_at_level:
                lines.append(f"**Level {level}** ({len(modules_at_level)} modules): {', '.join(sorted(modules_at_level))}")
        lines.append("")
        
        # Most depended upon
        dep_counts = [(m, len(deps)) for m, deps in self.reverse_deps.items()]
        dep_counts.sort(key=lambda x: x[1], reverse=True)
        
        lines.append("## Most Depended Upon Modules")
        lines.append("")
        for module, count in dep_counts[:10]:
            lines.append(f"- **{module}**: used by {count} modules")
        lines.append("")
        
        # Most dependencies
        import_counts = [(m, len(deps)) for m, deps in self.imports.items() if deps]
        import_counts.sort(key=lambda x: x[1], reverse=True)
        
        lines.append("## Modules with Most Dependencies")
        lines.append("")
        for module, count in import_counts[:10]:
            lines.append(f"- **{module}**: imports {count} modules")
        
        return '\n'.join(lines)


def main():
    """Main entry point."""
    import argparse
    
    parser = argparse.ArgumentParser(
        description='Generate dependency graphs for Lean formalization'
    )
    parser.add_argument(
        '--base-path',
        default='/home/runner/work/3D-Navier-Stokes/3D-Navier-Stokes/Lean4-Formalization',
        help='Base path for Lean files'
    )
    parser.add_argument(
        '--format',
        choices=['mermaid', 'dot', 'ascii', 'stats', 'all'],
        default='all',
        help='Output format'
    )
    parser.add_argument(
        '--output-dir',
        default='.',
        help='Output directory for generated files'
    )
    parser.add_argument(
        '--root-module',
        help='Root module for ASCII tree (default: auto-detect main theorem)'
    )
    
    args = parser.parse_args()
    
    analyzer = LeanDependencyAnalyzer(args.base_path)
    analyzer.scan_files()
    
    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    
    if args.format in ['mermaid', 'all']:
        print("Generating Mermaid diagram...")
        output_file = output_dir / 'lean_dependencies.mmd'
        analyzer.generate_mermaid(str(output_file))
        print(f"  Saved to {output_file}")
    
    if args.format in ['dot', 'all']:
        print("Generating DOT/Graphviz diagram...")
        output_file = output_dir / 'lean_dependencies.dot'
        analyzer.generate_dot(str(output_file))
        print(f"  Saved to {output_file}")
        print("  To generate PNG: dot -Tpng lean_dependencies.dot -o lean_dependencies.png")
    
    if args.format in ['ascii', 'all']:
        print("Generating ASCII dependency trees...")
        for module in ['MainTheorem', 'Theorem13_7', 'SerrinEndpoint']:
            if module in analyzer.files:
                output_file = output_dir / f'dependencies_{module}.txt'
                tree = analyzer.generate_ascii_tree(module)
                with open(output_file, 'w') as f:
                    f.write(tree)
                print(f"  Saved tree for {module} to {output_file}")
    
    if args.format in ['stats', 'all']:
        print("Generating statistics...")
        output_file = output_dir / 'lean_statistics.md'
        stats = analyzer.generate_statistics()
        with open(output_file, 'w') as f:
            f.write(stats)
        print(f"  Saved to {output_file}")
    
    print("\nDone!")


if __name__ == '__main__':
    main()
