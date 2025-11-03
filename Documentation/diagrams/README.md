# Lean Dependency Diagrams

This directory contains automatically generated dependency diagrams and statistics for the Lean 4 formalization.

## Files

### Dependency Graphs

- **`lean_dependencies.mmd`** - Mermaid diagram format (renders on GitHub)
- **`lean_dependencies.dot`** - GraphViz DOT format (can be converted to PNG/SVG)

### Dependency Trees

Individual dependency trees for main theorems:
- **`dependencies_MainTheorem.txt`** - Dependencies for conditional global regularity
- **`dependencies_Theorem13_7.txt`** - Dependencies for unconditional global regularity
- **`dependencies_SerrinEndpoint.txt`** - Dependencies for Serrin endpoint proof

### Statistics

- **`lean_statistics.md`** - Comprehensive statistics about module organization and dependencies

## Viewing the Diagrams

### Mermaid Diagram

The `.mmd` file can be viewed:
1. Directly on GitHub (it will render automatically in Markdown)
2. Using the [Mermaid Live Editor](https://mermaid.live/)
3. In VS Code with the Mermaid extension

### GraphViz Diagram

To generate a PNG from the DOT file:

```bash
# Install graphviz if needed
sudo apt-get install graphviz  # Ubuntu/Debian
brew install graphviz          # macOS

# Generate PNG
dot -Tpng lean_dependencies.dot -o lean_dependencies.png

# Or generate SVG (scalable)
dot -Tsvg lean_dependencies.dot -o lean_dependencies.svg
```

## Regenerating Diagrams

To regenerate all diagrams after modifying Lean files:

```bash
cd /path/to/3D-Navier-Stokes
python3 tools/generate_lean_dependency_graph.py --output-dir Documentation/diagrams
```

Options:
- `--format mermaid|dot|ascii|stats|all` - Choose specific format(s)
- `--base-path PATH` - Specify Lean files location
- `--output-dir DIR` - Specify output directory

## Color Coding

The dependency graphs use color coding to identify module types:

- 🔴 **Red** - Main theorem modules (MainTheorem, Theorem13_7, SerrinEndpoint)
- 🔵 **Blue** - BKM closure framework modules
- 🟢 **Green** - Riccati analysis modules
- 🟡 **Yellow** - Foundation modules (BasicDefinitions, UniformConstants, FunctionalSpaces)
- ⚪ **White/Gray** - Core theory modules

## Interpretation

### Reading the Graphs

- **Arrows point from dependencies to dependents**: If A → B, then B imports/depends on A
- **Levels indicate depth**: Modules at level 0 have no internal dependencies
- **Clusters indicate related functionality**: Modules that import each other form logical groups

### Key Insights

1. **Foundation Layer** (Level 0): BasicDefinitions, UniformConstants, FunctionalSpaces provide the base
2. **Core Theory** (Levels 1-2): Dyadic analysis, Besov embeddings, coercivity estimates
3. **Analysis Layer** (Level 3): Global Riccati, energy estimates, vorticity control
4. **Closure** (Level 4): BKM closure framework integration
5. **Main Results** (Level 5): Theorem13_7 (unconditional regularity), SerrinEndpoint

### Critical Path

The critical path to the main result `global_regularity_unconditional` follows:

```
BasicDefinitions → UniformConstants → DyadicRiccati → ParabolicCoercivity → GlobalRiccati → BKMClosure → Theorem13_7
```

## Maintenance

These diagrams are automatically generated and should be regenerated:
- After adding new Lean modules
- After modifying import structure
- Before major releases or submissions
- When updating documentation

**Last Generated**: 2024-10-30
