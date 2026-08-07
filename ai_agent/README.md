# Navier-Stokes AI Agent

An intelligent assistant for analyzing mathematical documents, extracting equations, and generating helper scripts for the 3D Navier-Stokes verification framework.

## Overview

This AI agent helps researchers and developers work with the complex mathematical framework of the Navier-Stokes equations by:

1. **Parsing PDF Documents**: Extracts mathematical equations and formulas from PDF files
2. **Mathematical Memory**: Builds and maintains a knowledge base of equations, constants, and theorems
3. **Visualization**: Creates visual representations of equations, relationships, and proof structures
4. **Script Generation**: Automatically generates Python scripts for verification, simulation, and analysis

## Features

### 📄 Document Processing
- Extracts equations from PDF documents using PyPDF2
- Parses Markdown documentation files
- Categorizes equations by type (Navier-Stokes, vorticity, BKM criterion, etc.)
- Identifies mathematical operators, norms, constants, and function spaces

### 🧠 Mathematical Memory
- Stores equations, constants, theorems, and their relationships
- Supports searching and querying the knowledge base
- Exports to JSON and Markdown formats
- Maintains context about the QCAL framework and global regularity proof

### 📊 Visualization
- Generates equation network graphs showing relationships
- Creates category distribution charts
- Visualizes proof structure flow
- Produces comprehensive summary reports

### 🔧 Script Generation
- **Verification Scripts**: Test mathematical properties and inequalities
- **Simulation Scripts**: 3D Navier-Stokes DNS solver templates
- **Analysis Scripts**: Post-process and analyze simulation results
- **Visualization Scripts**: Plot velocity fields, vorticity, and energy spectra

## Installation

### Prerequisites
```bash
# Python 3.9 or higher required
python --version
```

### Install Dependencies
```bash
pip install -r requirements.txt
```

Required packages:
- `numpy>=1.21.0` - Numerical computations
- `scipy>=1.7.0` - Scientific computing
- `matplotlib>=3.5.0` - Visualization
- `PyPDF2>=3.0.0` - PDF parsing

## Quick Start

### Basic Usage

```python
from ai_agent import NavierStokesAIAgent

# Initialize the agent
agent = NavierStokesAIAgent(workspace_dir="my_workspace")

# Process documentation
agent.process_documentation("Documentation")

# Search for specific topics
agent.search_knowledge("BKM")
agent.search_knowledge("Riccati")

# Generate visualizations
agent.visualize_knowledge()

# Generate helper scripts
agent.generate_scripts()

# Export knowledge base
agent.export_knowledge_base('markdown')
```

### Command Line Usage

Run the example script:
```bash
# Run basic examples
python run_ai_agent.py

# Run full pipeline with all documents
python run_ai_agent.py --full
```

## Module Architecture

```
ai_agent/
├── __init__.py              # Package initialization
├── agent.py                 # Main AI agent interface
├── equation_parser.py       # PDF and text parsing
├── math_memory.py           # Knowledge base management
├── script_generator.py      # Script template generation
└── visualizer.py           # Visualization tools
```

### Core Components

#### 1. EquationParser
Extracts and categorizes mathematical content:

```python
from ai_agent import EquationParser

parser = EquationParser()

# Parse PDF document
results = parser.parse_pdf("path/to/paper.pdf")

# Parse text content
with open("document.md", 'r') as f:
    content = f.read()
results = parser.parse_text(content)

# Search equations
equations = parser.search_equations("vorticity")

# Get summary
summary = parser.get_summary()
```

Categories detected:
- `navier_stokes` - Navier-Stokes equations
- `vorticity` - Vorticity-related equations
- `besov_spaces` - Besov space embeddings
- `riccati` - Riccati inequalities
- `bkm_criterion` - BKM criterion
- `energy_estimates` - Energy estimates
- `constants` - Mathematical constants
- `inequalities` - General inequalities

#### 2. MathematicalMemory
Stores and organizes mathematical knowledge:

```python
from ai_agent import MathematicalMemory

memory = MathematicalMemory(memory_file="knowledge.json")

# Add equation
memory.add_equation(
    name="BKM Criterion",
    formula="∫₀^T ‖ω(t)‖_{L∞} dt < ∞ ⇒ no blow-up",
    description="Beale-Kato-Majda criterion",
    category="criterion"
)

# Add constant
memory.add_constant(
    name="ν",
    description="Kinematic viscosity",
    typical_value="1e-3",
    category="physical"
)

# Search
results = memory.search("BKM")

# Get summary
summary = memory.get_summary()

# Export
memory.export_markdown("knowledge_base.md")
```

#### 3. ScriptGenerator
Generates Python scripts from templates:

```python
from ai_agent import ScriptGenerator

generator = ScriptGenerator(output_dir="scripts")

# Generate verification script
generator.generate_verification_script(equations)

# Generate simulation script
generator.generate_simulation_script(constants)

# Generate analysis script
generator.generate_analysis_script(memory)

# Generate visualization script
generator.generate_visualization_script(memory)
```

#### 4. EquationVisualizer
Creates visual representations:

```python
from ai_agent import EquationVisualizer

visualizer = EquationVisualizer(output_dir="figures")

# Visualize equation network
visualizer.visualize_equation_network(memory)

# Visualize category distribution
visualizer.visualize_category_distribution(memory)

# Visualize proof structure
visualizer.visualize_proof_structure(memory)

# Create summary report
visualizer.create_summary_report(memory)
```

## Pre-loaded Knowledge

The agent comes with pre-initialized knowledge about the Navier-Stokes framework:

### Constants
- **ν** (nu): Kinematic viscosity
- **C_BKM**: Calderón-Zygmund/Besov constant (2.0)
- **c_d**: Bernstein constant for d=3 (0.5)
- **δ*** (delta star): Misalignment defect parameter
- **c⋆** (c star): Parabolic coercivity coefficient (1/16)
- **C_str**: Vorticity stretching constant (32)
- **C_CZ**: Optimized Calderón-Zygmund constant (1.5)

### Key Equations
- **Navier-Stokes**: ∂u/∂t + (u·∇)u = -∇p + ν∆u + f
- **Vorticity**: ω = ∇ × u
- **BKM Criterion**: ∫₀^T ‖ω(t)‖_{L∞} dt < ∞ ⇒ no blow-up
- **Riccati Inequality**: d/dt X(t) ≤ A - B X(t) log(e + βX(t))
- **CZ-Besov Estimate**: ‖∇u‖_{L∞} ≤ C_CZ‖ω‖_{B⁰_{∞,1}}

## Output Examples

### Generated Scripts

1. **verify_equations.py**: Verification framework
   - Checks mathematical properties
   - Validates inequalities
   - Reports pass/fail status

2. **simulate_ns.py**: DNS simulator
   - Pseudo-spectral solver
   - Taylor-Green vortex initialization
   - Energy and vorticity tracking

3. **analyze_results.py**: Analysis tools
   - Statistical analysis
   - BKM criterion verification
   - Energy cascade analysis

4. **visualize_data.py**: Visualization tools
   - Velocity field plots
   - Vorticity field plots
   - Energy spectrum analysis

### Visualizations

- **equation_network.png**: Graph showing equation relationships
- **category_distribution.png**: Bar charts of equation categories
- **proof_structure.png**: Flow diagram of the proof strategy
- **summary_report.png**: Comprehensive visual summary

### Exports

- **knowledge_base.json**: Machine-readable knowledge base
- **knowledge_base.md**: Human-readable documentation

## Advanced Usage

### Custom Workflows

```python
from ai_agent import NavierStokesAIAgent

agent = NavierStokesAIAgent()

# Process specific PDFs
pdf_files = [
    "Navier-Stokes Conjetura_ QCAL Coherencia Cuántica.pdf",
    "ENGLISH_Navier-Stokes Conjetura_ QCAL Coherencia Cuántica (1).pdf"
]

for pdf in pdf_files:
    agent.process_pdf_document(pdf)

# Add custom equations
agent.memory.add_equation(
    name="Custom Estimate",
    formula="‖u‖_{L³} ≤ C‖ω‖_{B⁰_{∞,1}}",
    description="L³ control via Besov",
    category="estimate"
)

# Generate custom script
from ai_agent import ScriptGenerator

generator = ScriptGenerator()
equations = list(agent.memory.knowledge_base['equations'].values())
generator.generate_verification_script(
    equations,
    output_file="custom_verification.py"
)
```

### Batch Processing

```python
from pathlib import Path
from ai_agent import NavierStokesAIAgent

agent = NavierStokesAIAgent()

# Process all PDFs in a directory
pdf_dir = Path(".")
for pdf_file in pdf_dir.glob("*.pdf"):
    print(f"Processing {pdf_file.name}...")
    agent.process_pdf_document(str(pdf_file))

# Process all documentation
for doc_dir in ["Documentation", "Lean4-Formalization", "DNS-Verification"]:
    if Path(doc_dir).exists():
        agent.process_documentation(doc_dir)

# Generate all outputs
agent.visualize_knowledge()
agent.generate_scripts()
agent.export_knowledge_base('markdown')
agent.export_knowledge_base('json')
```

## Integration with Existing Framework

The AI agent integrates seamlessly with the existing Navier-Stokes verification framework:

```python
from ai_agent import NavierStokesAIAgent
from verification_framework import FinalProof

# Use agent to extract equations
agent = NavierStokesAIAgent()
agent.process_documentation("Documentation")

# Get constants from agent memory
nu = float(agent.memory.get_constant("ν")['typical_value'].split()[0])

# Use in verification framework
proof = FinalProof(ν=nu)
results = proof.prove_global_regularity(T_max=100.0, X0=10.0, u0_L3_norm=1.0)

print(f"Global regularity: {results['global_regularity']}")
```

## Troubleshooting

### PDF Parsing Issues

If PDF parsing fails:
```python
# The agent automatically falls back to documentation files
# Or manually process text content:
with open("document.txt", 'r') as f:
    content = f.read()
results = agent.parser.parse_text(content, source="document.txt")
```

### Missing Dependencies

```bash
# Install all dependencies
pip install numpy scipy matplotlib PyPDF2

# Or install from requirements
pip install -r requirements.txt
```

### Visualization Errors

If matplotlib is not available:
```python
# Skip visualization step
agent.process_documentation("Documentation")
agent.generate_scripts()
# agent.visualize_knowledge()  # Skip this
agent.export_knowledge_base('markdown')
```

## Contributing

The AI agent is designed to be extensible:

1. **Add new categories**: Modify `equation_parser.py` categories
2. **Add new templates**: Extend `script_generator.py` templates
3. **Add new visualizations**: Add methods to `visualizer.py`
4. **Enhance parsing**: Improve regex patterns in `equation_parser.py`

## License

MIT License - See repository root for details

## References

This agent is designed to work with the mathematical framework described in:
- BKM Criterion (Beale-Kato-Majda, 1984)
- QCAL Framework for 3D Navier-Stokes
- Unified BKM-CZ-Besov verification approach
- Clay Millennium Problem documentation

## Contact

For issues, questions, or contributions, please use the GitHub repository issue tracker.
