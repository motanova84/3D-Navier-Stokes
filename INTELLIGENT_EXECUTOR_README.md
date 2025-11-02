# Intelligent Executor - Parametric Sweep System

## Overview

The Intelligent Executor is a dynamic optimization system for running parametric sweep simulations of the 3D Navier-Stokes equations. It intelligently selects which simulation packages to execute based on:

- **Scientific priority** (HIGH, MEDIUM, LOW)
- **Available computational resources** (CPU, memory, disk)
- **Previous results** (avoids re-running completed packages)
- **Estimated execution time** (maximizes throughput)

## Components

### 1. `parametric_sweep_orchestrator.py`

Core orchestration module that manages simulation packages.

**Key Functions:**

- `load_package(package_id)` - Loads a package configuration
- `assign_priority(package)` - Assigns scientific priority (HIGH/MEDIUM/LOW)
- `estimate_computational_cost(package)` - Estimates resource requirements
- `run_package(package_id)` - Executes a simulation package
- `create_example_packages(n_packages)` - Creates example packages for testing

### 2. `intelligent_executor.py`

Intelligent execution engine with multiple modes.

**Key Functions:**

- `get_available_resources()` - Detects available CPU, memory, and disk
- `can_run_package(package_id, resources)` - Checks resource availability
- `get_next_package_to_run()` - Selects optimal package to execute
- `run_continuous_mode()` - Runs packages continuously until completion
- `run_opportunistic_mode()` - Runs packages when system is idle

## Installation

1. Install required dependencies:

```bash
pip install -r requirements.txt
```

Required packages:
- `psutil>=5.9.0` - System resource monitoring
- `numpy>=1.21.0` - Numerical computations

## Usage

### Quick Start

1. **Create example packages** (for testing):

```bash
python3 parametric_sweep_orchestrator.py
```

This creates 10 example packages in `parametric_sweep_packages/`.

2. **Run the next optimal package**:

```bash
python3 intelligent_executor.py --mode next
```

### Execution Modes

#### Mode 1: Next Package (Default)

Executes the single next optimal package based on priority and resources.

```bash
python3 intelligent_executor.py --mode next
```

**Use case:** Run one package at a time manually.

#### Mode 2: Continuous

Executes packages continuously until all are complete or time limit is reached.

```bash
# Run continuously without time limit
python3 intelligent_executor.py --mode continuous

# Run for maximum 8 hours
python3 intelligent_executor.py --mode continuous --max-hours 8
```

**Use case:** Batch processing all pending packages.

**Features:**
- Automatically selects next package after each completion
- Respects resource constraints
- Can be time-limited with `--max-hours`
- Retries if resources temporarily unavailable

#### Mode 3: Opportunistic

Executes packages only when system is idle (CPU usage below threshold).

```bash
# Run when CPU usage < 80% (default)
python3 intelligent_executor.py --mode opportunistic

# Run when CPU usage < 50%
python3 intelligent_executor.py --mode opportunistic --cpu-threshold 50
```

**Use case:** Background execution without interfering with other work.

**Features:**
- Monitors CPU usage continuously
- Executes only when system is idle
- Single-worker execution to minimize impact

## Priority Assignment

Packages are automatically assigned priority based on scientific importance:

### HIGH Priority
- High Reynolds number (Re > 1000) with high resolution (≥64³)
- Low viscosity (ν < 1e-4) with high resolution (≥64³)

### MEDIUM Priority
- High Reynolds number OR low viscosity
- High resolution (≥64³) cases

### LOW Priority
- Validation cases with standard parameters

## Resource Management

The executor checks three resource constraints before running a package:

1. **Memory**: Available memory ≥ 1.2 × estimated memory (20% safety margin)
2. **Disk**: Available disk ≥ 1.5 × estimated disk (50% safety margin)
3. **CPU**: At least 1 free CPU core available

If resources are insufficient, the package is skipped and the next suitable package is selected.

## Directory Structure

```
parametric_sweep_packages/          # Package definitions (gitignored)
├── package_0001.json               # Individual package configs
├── package_0002.json
├── ...
└── priority_summary.json           # Priority assignments

parametric_sweep_results/           # Execution results (gitignored)
├── results_package_0001.json       # Completed package results
├── results_package_0002.json
└── ...
```

## Package Configuration Format

Each package is a JSON file with the following structure:

```json
{
  "package_id": 1,
  "name": "NavierStokes_Re1000_nu1.0e-03_res64",
  "parameters": {
    "nu": 0.001,
    "Reynolds": 1000,
    "resolution": [64, 64, 64],
    "n_timesteps": 1000,
    "domain_size": [6.283185, 6.283185, 6.283185],
    "initial_condition": "turbulent"
  },
  "cases": [1],
  "created": "2025-11-02T07:24:00.000000"
}
```

## Result Format

Execution results are saved as JSON:

```json
{
  "package_id": 1,
  "status": "completed",
  "parameters": { ... },
  "execution_time_seconds": 125.43,
  "timestamp": "2025-11-02T07:30:00.000000",
  "metrics": {
    "max_velocity": 8.5,
    "energy": 95.2,
    "enstrophy": 42.1,
    "convergence": true
  }
}
```

## Testing

Run the test suite:

```bash
python3 -m unittest test_intelligent_executor -v
```

Tests cover:
- Package creation and loading
- Priority assignment
- Cost estimation
- Resource detection
- Package selection logic
- Complete workflow integration

## Examples

### Example 1: Process all HIGH priority packages

```bash
# Continuous mode will process HIGH priority first
python3 intelligent_executor.py --mode continuous --max-hours 24
```

### Example 2: Background execution during night

```bash
# Run opportunistically with low CPU threshold
nohup python3 intelligent_executor.py --mode opportunistic --cpu-threshold 30 > executor.log 2>&1 &
```

### Example 3: Process specific number of packages

```bash
# Process next 5 packages manually
for i in {1..5}; do
    python3 intelligent_executor.py --mode next
done
```

## Notes

- The system is designed for the 3D Navier-Stokes simulation framework
- Package execution uses placeholder simulation for demonstration
- In production, `run_package()` would call the actual Navier-Stokes solver
- Results and packages directories are git-ignored to avoid large data commits

## Future Enhancements

Potential improvements:
- GPU resource detection and allocation
- Distributed execution across multiple nodes
- Real-time monitoring dashboard
- Automatic checkpoint/restart on failures
- Advanced scheduling with job dependencies
- Integration with HPC job schedulers (SLURM, PBS)

## License

Part of the 3D Navier-Stokes Global Regularity Framework.
