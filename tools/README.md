# Tools for Lean Formalization Analysis

This directory contains utilities for analyzing and visualizing the Lean 4 formalization.

## Available Tools

### 1. check_lean_status.py

**Purpose**: Check the status of the Lean formalization and generate progress reports.

**Usage**:
```bash
# Generate text report (default)
python3 tools/check_lean_status.py

# Generate JSON report for automated processing
python3 tools/check_lean_status.py --format json

# Save report to file
python3 tools/check_lean_status.py --output status_report.txt
```

**Output includes**:
- Overall statistics (files, theorems, axioms, sorry count)
- Completion percentage
- Files requiring attention (sorted by priority)
- Status by category (Foundation, Core Theory, Analysis, Closure, Main Results)
- Next steps and recommendations

**Example Output**:
```
======================================================================
LEAN FORMALIZATION STATUS REPORT
======================================================================

## Overall Statistics

Total Files:        18
Total Lines:        810
Theorems:           27
Axioms:             33
Completion:         45.0% (27/60 proven)
```

### 2. generate_lean_dependency_graph.py

**Purpose**: Generate dependency graphs and visualizations for Lean modules.

**Usage**:
```bash
# Generate all formats (default)
python3 tools/generate_lean_dependency_graph.py --output-dir Documentation/diagrams

# Generate specific format
python3 tools/generate_lean_dependency_graph.py --format mermaid --output-dir Documentation/diagrams

# Generate dependency tree for specific module
python3 tools/generate_lean_dependency_graph.py --format ascii --root-module Theorem13_7
```

**Formats**:
- `mermaid` - Mermaid diagram (renders on GitHub)
- `dot` - GraphViz DOT format (can be converted to PNG/SVG)
- `ascii` - ASCII dependency trees
- `stats` - Statistics about modules and dependencies
- `all` - All of the above

**Output files**:
- `lean_dependencies.mmd` - Mermaid graph
- `lean_dependencies.dot` - DOT graph
- `dependencies_*.txt` - ASCII trees for each main theorem
- `lean_statistics.md` - Dependency statistics

**Converting DOT to images**:
```bash
# Install graphviz
sudo apt-get install graphviz  # Ubuntu/Debian
brew install graphviz          # macOS

# Generate PNG
dot -Tpng Documentation/diagrams/lean_dependencies.dot -o lean_deps.png

# Generate SVG (scalable)
dot -Tsvg Documentation/diagrams/lean_dependencies.dot -o lean_deps.svg
```

### 3. ns_validate.py

**Purpose**: Validate Navier-Stokes computational framework (existing tool).

See the script for detailed usage.

## Integration with Development Workflow

### After Modifying Lean Files

```bash
# 1. Check formalization status
python3 tools/check_lean_status.py

# 2. Regenerate dependency graphs
python3 tools/generate_lean_dependency_graph.py --output-dir Documentation/diagrams

# 3. Review changes in Documentation/FORMAL_PROOF_ROADMAP.md
```

### Continuous Integration

These tools can be integrated into CI/CD pipelines:

```yaml
# Example GitHub Actions workflow
- name: Check Lean status
  run: python3 tools/check_lean_status.py --format json --output status.json
  
- name: Regenerate graphs
  run: python3 tools/generate_lean_dependency_graph.py --output-dir Documentation/diagrams
  
- name: Commit changes
  run: |
    git add Documentation/diagrams/
    git commit -m "Update dependency graphs"
```

## Requirements

- Python 3.7+
- No external dependencies (uses standard library only)

## Contributing

When adding new tools:
1. Follow the same command-line interface pattern (argparse)
2. Provide `--help` documentation
3. Update this README
4. Add usage examples
5. Make scripts executable (`chmod +x`)

## See Also

- [FORMAL_PROOF_ROADMAP.md](../Documentation/FORMAL_PROOF_ROADMAP.md) - Main formalization documentation
- [diagrams/README.md](../Documentation/diagrams/README.md) - Visualization documentation
- [QUICKSTART_FORMAL_PROOF.md](../Documentation/QUICKSTART_FORMAL_PROOF.md) - Quick start guide

---

**Last Updated**: 2024-10-30
