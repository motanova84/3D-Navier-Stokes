# Parametric Sweep Usage Guide

This guide explains how to use the parametric sweep orchestrator to run distributed simulations.

## Overview

The parametric sweep system allows you to:
- Organize simulations into packages
- Assign priorities based on parameter criticality
- Estimate computational costs
- Execute packages in parallel with progress tracking

## Components

### 1. `parametric_sweep_orchestrator.py`
Core orchestration module that handles package management and execution.

**Key Functions:**
- `load_package(package_id)` - Load package data
- `assign_priority(package)` - Determine execution priority (HIGH/MEDIUM/LOW)
- `estimate_computational_cost(package)` - Estimate time, memory, and disk usage
- `run_package(package_id, ...)` - Execute all simulations in a package
- `create_example_packages(...)` - Create test packages

### 2. `run_package.py`
CLI script for executing individual packages.

**Usage:**
```bash
python run_package.py --package-id <ID> [OPTIONS]
```

**Options:**
- `--package-id`: Package ID to execute (required)
- `--workers`: Number of parallel workers (default: auto-detect)
- `--output-dir`: Output directory (default: parametric_sweep_results)
- `--dry-run`: Show info without executing

## Quick Start

### Step 1: Create Example Packages

```bash
python parametric_sweep_orchestrator.py
```

This creates 5 example packages in `parametric_sweep_packages/` directory.

### Step 2: Inspect a Package (Dry Run)

```bash
python run_package.py --package-id 0 --dry-run
```

Output shows:
- Package size (number of simulations)
- Priority level (HIGH/MEDIUM/LOW)
- Estimated computational cost
- Sample parameters

### Step 3: Execute a Package

```bash
python run_package.py --package-id 0 --workers 4
```

The script will:
1. Display package information
2. Ask for confirmation
3. Execute simulations in parallel
4. Show progress and summary

## Priority Assignment

Packages are automatically assigned priority based on parameter criticality:

### HIGH Priority
- Frequencies near f₀ = 141.7 Hz (natural emergence frequency)
- Reynolds numbers > 10,000
- Grid resolutions > 128
- At least 2 of the above conditions met

### MEDIUM Priority
- Frequencies 100-200 Hz
- Reynolds numbers 1,000-10,000
- Grid resolutions 64-128
- At least 1 condition met

### LOW Priority
- All other parameter combinations

## Cost Estimation

The system estimates computational requirements:

```
Time:   Scales with N³ × log(Re)
Memory: Scales with N³ (peak usage)
Disk:   Scales with N² (cumulative)
```

Base values (adjustable via module constants):
- `BASE_TIME_MINUTES = 5.0`
- `BASE_MEMORY_GB = 2.0`
- `BASE_DISK_GB = 0.5`
- `BASE_N_VALUE = 64`
- `BASE_RE_VALUE = 1000`

## Package Structure

Each package is stored as JSON:

```json
{
  "id": 0,
  "size": 10,
  "parameters": [
    {
      "f0": 141.7,
      "Re": 5000,
      "N": 64,
      "nu": 0.001,
      "M": 100.0,
      "a": 2.45,
      "alpha": 2.0
    },
    ...
  ],
  "created": "2025-11-02T10:45:28.204829"
}
```

## Output Structure

Results are saved in:
```
parametric_sweep_results/
├── package_0000/
│   ├── sim_f0_141.7_Re_5000_N_64.json
│   ├── sim_f0_150.0_Re_10000_N_128.json
│   └── summary.json
├── package_0001/
│   └── ...
```

## Advanced Usage

### Custom Package Creation

```python
from parametric_sweep_orchestrator import create_example_packages

package_ids = create_example_packages(
    output_dir='my_packages',
    n_packages=10,
    sims_per_package=20
)
```

### Programmatic Execution

```python
from parametric_sweep_orchestrator import run_package

result = run_package(
    package_id=0,
    output_dir='my_results',
    n_workers=8
)

print(f"Success: {result['n_success']}/{result['n_total']}")
```

### Loading and Inspecting Packages

```python
from parametric_sweep_orchestrator import load_package, assign_priority

package = load_package(0)
priority = assign_priority(package)
print(f"Package {package['id']} has {priority} priority")
```

## Testing

Run the test suite:

```bash
python test_parametric_sweep.py
```

Tests cover:
- Package creation and loading
- Priority assignment logic
- Cost estimation accuracy
- Package structure validation
- Error handling

## Configuration

Adjust computational cost estimation by modifying constants in `parametric_sweep_orchestrator.py`:

```python
# At module level
BASE_TIME_MINUTES = 5.0  # Adjust based on benchmarks
BASE_MEMORY_GB = 2.0
BASE_DISK_GB = 0.5
BASE_N_VALUE = 64
BASE_RE_VALUE = 1000
```

## Notes

- Packages are independent and can be executed in any order
- Failed simulations are tracked but don't stop package execution
- All results include timestamps and parameter metadata
- Use `--dry-run` to verify package contents before execution

## Troubleshooting

**Package not found:**
```bash
❌ ERROR: Paquete 99 no encontrado
   Ejecuta primero: python parametric_sweep_orchestrator.py
```
→ Create packages first using the orchestrator

**Import errors:**
→ Ensure `DNS-Verification/DualLimitSolver` modules are available
→ Check that numpy is installed: `pip install numpy`

**Out of memory:**
→ Reduce `--workers` count
→ Process packages with lower N values first
→ Check estimated memory usage before execution
