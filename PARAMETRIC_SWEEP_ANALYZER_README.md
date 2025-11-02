# Parametric Sweep Analyzer - Usage Guide

## Overview

The `parametric_sweep_analyzer.py` module provides comprehensive analysis tools for Ψ-NSE (Psi-NSE) parametric sweep simulations. It extracts scientific insights from the explored parameter space and generates publication-quality visualizations.

## Features

### 1. Data Loading & Consolidation
- Loads simulation results from JSON files
- Consolidates data into pandas DataFrame
- Handles missing or incomplete data gracefully
- Provides summary statistics

### 2. Stability Map Visualization
- Heat maps showing stability in (f₀, Re) parameter space
- Blow-up detection and timing analysis
- BKM integral visualization
- Predicted frequency marker (f₀ = 141.7 Hz)

### 3. Frequency Emergence Validation
- Validates spontaneous emergence of predicted frequency
- Statistical analysis of frequency errors
- Correlation analysis with distance from predicted value
- Convergence visualization

### 4. Classical vs Ψ-NSE Comparison
- Stability rate vs Reynolds number
- Vorticity behavior comparison
- Energy conservation analysis
- Computational cost assessment

## Installation

Required dependencies (automatically installed with requirements.txt):
```bash
pip install -r requirements.txt
```

Dependencies include:
- numpy >= 1.21.0
- scipy >= 1.7.0
- matplotlib >= 3.5.0
- pandas >= 1.3.0
- seaborn >= 0.11.0

## Usage

### Command Line Interface

Basic usage:
```bash
python3 parametric_sweep_analyzer.py
```

With custom directories:
```bash
python3 parametric_sweep_analyzer.py \
    --results-dir path/to/results \
    --output-dir path/to/output
```

Options:
- `--results-dir`: Directory containing JSON result files (default: `parametric_sweep_results`)
- `--output-dir`: Directory for output plots (default: `artifacts`)

### Python API

```python
import parametric_sweep_analyzer as psa
import pandas as pd

# Load simulation results
df = psa.load_all_simulation_results('path/to/results')

# Generate visualizations
psa.plot_stability_map(df, 'output/stability_map.png')
psa.plot_frequency_emergence_validation(df, 'output/frequency_validation.png')
psa.plot_classical_vs_psi_comparison(df, 'output/comparison.png')
```

## Input Data Format

The analyzer expects JSON files with the following structure:

```json
{
  "package_id": "unique_identifier",
  "results": [
    {
      "status": "success",
      "params": {
        "f0": 141.7,
        "Re": 1000.0,
        "nu": 0.001,
        "N": 32,
        "T_max": 10.0,
        "L": 6.283185307179586
      },
      "results": {
        "blowup_detected": false,
        "blowup_time": null,
        "max_vorticity": 15.3,
        "energy_final": 0.95,
        "energy_variation": 0.02,
        "dominant_frequency": 142.1,
        "frequency_error": 0.003,
        "bkm_integral": 45.6,
        "bkm_converged": true,
        "simulation_time": 120.5
      },
      "completed_at": "2025-01-01T12:00:00"
    }
  ]
}
```

## Output

The analyzer generates three main visualization files:

1. **stability_map.png** (3 panels)
   - Stability map in (f₀, Re) space
   - Blow-up time distribution (if applicable)
   - BKM integral distribution

2. **frequency_emergence_validation.png** (5 panels)
   - Detected vs imposed frequency
   - Error vs Reynolds number
   - Error distribution near predicted f₀
   - Error correlation with distance to f₀
   - Spectral power convergence

3. **classical_vs_psi_comparison.png** (4 panels)
   - Success rate vs Reynolds
   - Maximum vorticity comparison
   - Energy conservation
   - Computational cost

## Testing

Run the test suite:
```bash
python3 -m unittest test_parametric_sweep_analyzer
```

Run specific test:
```bash
python3 -m unittest test_parametric_sweep_analyzer.TestParametricSweepAnalyzer.test_load_all_simulation_results
```

## Error Handling

The analyzer gracefully handles:
- Empty result directories
- Insufficient data points for interpolation
- Failed simulations (marked as status != "success")
- Missing data fields (filled with NaN)
- Coplanar data that cannot be interpolated

## Performance Considerations

- For large datasets (>1000 simulations), processing may take several minutes
- Interpolation is skipped when data points < 4 or all values are identical
- Memory usage scales with number of simulations and grid resolution

## Scientific Background

This analyzer is designed for the Ψ-NSE framework which addresses the Clay Millennium Prize problem for 3D Navier-Stokes equations. Key concepts:

- **f₀ = 141.7 Hz**: Predicted natural frequency emerging from geometric regularization
- **BKM Criterion**: Beale-Kato-Majda criterion for regularity
- **Reynolds Number (Re)**: Ratio of inertial to viscous forces
- **Blow-up Detection**: Identification of finite-time singularities

## Contributing

When adding new analysis functions:
1. Follow the existing function signature patterns
2. Add comprehensive docstrings
3. Include error handling for edge cases
4. Add corresponding unit tests
5. Update this documentation

## License

Part of the 3D-Navier-Stokes repository.
See repository LICENSE for details.
