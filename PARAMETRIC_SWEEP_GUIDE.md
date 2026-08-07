# Parametric Sweep System - User Guide

This guide demonstrates the parametric sweep system for automated numerical simulations with intelligent execution capabilities.

## Quick Start

Run the quickstart script to get started immediately:

```bash
./quickstart_parametric_sweep.sh
```

This will:
1. Generate 135 parameter sweep packages
2. Display a summary of packages by priority
3. Show all available execution options

## System Components

### 1. Parametric Sweep Orchestrator (`parametric_sweep_orchestrator.py`)

Generates parameter sweep packages with various configurations.

**Usage:**
```bash
python3 parametric_sweep_orchestrator.py
```

**What it does:**
- Creates combinations of Reynolds numbers (100, 500, 1000, 2000, 5000)
- Grid sizes (32³, 64³, 128³)
- Time steps (0.001, 0.005, 0.01)
- Viscosities (0.01, 0.001, 0.0001)
- Assigns priority levels (HIGH, MEDIUM, LOW) based on computational cost
- Generates JSON package files in `parametric_sweep_packages/`

### 2. Package Runner (`run_package.py`)

Executes a specific parameter sweep package.

**Usage:**
```bash
python3 run_package.py --package-id 0
```

**Options:**
- `--package-id ID`: Package ID to execute (required)
- `--package-dir DIR`: Custom package directory (default: `parametric_sweep_packages`)

**Features:**
- Tracks package status (pending → running → completed/failed)
- Saves results to JSON files
- Progress tracking
- Automatic error handling

### 3. Batch Execution Script (`batch_execution.sh`)

Execute multiple packages in sequence or parallel.

**Usage:**
```bash
# Sequential execution (one at a time)
./batch_execution.sh --mode sequential --priority HIGH

# Parallel execution (4 simultaneous)
./batch_execution.sh --mode parallel --priority HIGH --max-parallel 4

# Execute all packages
./batch_execution.sh --mode sequential --priority ALL
```

**Options:**
- `--mode MODE`: Execution mode (`sequential` or `parallel`)
- `--priority PRIORITY`: Filter by priority (`HIGH`, `MEDIUM`, `LOW`, or `ALL`)
- `--max-parallel N`: Maximum parallel jobs (for parallel mode)
- `--package-dir DIR`: Custom package directory

**Features:**
- Sequential or parallel execution
- Priority-based filtering
- Progress tracking with colored output
- Comprehensive logging

### 4. Intelligent Executor (`intelligent_executor.py`)

Smart execution system with multiple modes.

#### Mode: Next (Recommended for Quick Start)
Execute the next highest priority package:
```bash
python3 intelligent_executor.py --mode next
```

#### Mode: Continuous
Execute packages continuously until time limit:
```bash
python3 intelligent_executor.py --mode continuous --max-hours 24
```

#### Mode: Opportunistic
Execute only when CPU usage is below threshold:
```bash
python3 intelligent_executor.py --mode opportunistic --cpu-threshold 50
```

#### Mode: Status
Display execution status and statistics:
```bash
python3 intelligent_executor.py --mode status
```

**Options:**
- `--mode MODE`: Execution mode (`next`, `continuous`, `opportunistic`, `status`)
- `--max-hours HOURS`: Maximum hours for continuous mode
- `--cpu-threshold PERCENT`: CPU threshold for opportunistic mode
- `--package-dir DIR`: Custom package directory

## Workflow Examples

### Example 1: Quick Test Run
```bash
# Generate packages
python3 parametric_sweep_orchestrator.py

# Run one high-priority package
python3 intelligent_executor.py --mode next
```

### Example 2: Run All High Priority Packages
```bash
# Generate packages
python3 parametric_sweep_orchestrator.py

# Execute all HIGH priority packages sequentially
./batch_execution.sh --mode sequential --priority HIGH
```

### Example 3: Parallel Execution
```bash
# Generate packages
python3 parametric_sweep_orchestrator.py

# Run 4 packages in parallel
./batch_execution.sh --mode parallel --priority HIGH --max-parallel 4
```

### Example 4: Continuous Execution with Time Limit
```bash
# Generate packages
python3 parametric_sweep_orchestrator.py

# Run continuously for 8 hours
python3 intelligent_executor.py --mode continuous --max-hours 8
```

### Example 5: Opportunistic Execution
```bash
# Generate packages
python3 parametric_sweep_orchestrator.py

# Run only when CPU < 50%
python3 intelligent_executor.py --mode opportunistic --cpu-threshold 50
```

### Example 6: Check Status
```bash
# View execution status
python3 intelligent_executor.py --mode status
```

## Output Structure

```
parametric_sweep_packages/
├── package_0000.json         # Individual package files
├── package_0001.json
├── ...
├── package_0134.json
├── priority_summary.json     # Summary by priority
├── package_index.json        # Index of all packages
├── results/                  # Execution results
│   ├── result_0000.json
│   ├── result_0001.json
│   └── ...
└── logs/                     # Execution logs
    ├── package_0000.log
    └── ...
```

## Package Structure

Each package JSON file contains:
```json
{
  "id": 0,
  "reynolds": 100,
  "grid_size": 32,
  "time_step": 0.001,
  "viscosity": 0.01,
  "priority": "MEDIUM",
  "status": "pending",
  "estimated_time_minutes": 50.0,
  "created_at": "2025-11-02T07:00:00.000000"
}
```

## Priority Levels

- **HIGH**: Reynolds 500-2000, Grid ≥ 64³ (54 packages)
- **MEDIUM**: Reynolds ≤ 5000, Grid ≥ 32³ (81 packages)
- **LOW**: Other combinations (0 packages in default configuration)

## Requirements

- Python 3.9+
- psutil (for CPU monitoring)
- Standard libraries: json, argparse, datetime, itertools

Install requirements:
```bash
pip install -r requirements.txt
```

## Testing

Run the test suite:
```bash
python3 test_parametric_sweep.py
```

Tests verify:
- Module imports
- Package generation
- Package structure
- Priority levels
- Component instantiation
- Script executability

## Integration with Navier-Stokes Solver

The current implementation uses mock simulations. To integrate with a real solver:

1. Modify `run_package.py` in the `run_simulation()` method
2. Replace the mock simulation loop with actual solver calls
3. Update the results structure to match your solver output
4. Adjust time estimates based on actual computation times

Example integration:
```python
def run_simulation(self, package: Dict[str, Any]) -> Dict[str, Any]:
    # Import your solver
    from my_solver import NavierStokesSolver
    
    # Initialize solver with package parameters
    solver = NavierStokesSolver(
        reynolds=package['reynolds'],
        grid_size=package['grid_size'],
        time_step=package['time_step'],
        viscosity=package['viscosity']
    )
    
    # Run simulation
    solver.run()
    
    # Extract results
    results = {
        "package_id": package['id'],
        "status": "completed",
        "results": solver.get_results()
    }
    
    return results
```

## Tips and Best Practices

1. **Start Small**: Test with a few packages before running large batches
2. **Monitor Resources**: Use the status mode to track progress
3. **Use Priorities**: Focus on HIGH priority packages first
4. **Parallel Execution**: Adjust `--max-parallel` based on available CPU cores
5. **Opportunistic Mode**: Ideal for running on shared systems
6. **Time Limits**: Use continuous mode with `--max-hours` to respect system policies

## Troubleshooting

### Issue: "Package directory not found"
**Solution**: Run `python3 parametric_sweep_orchestrator.py` first to generate packages

### Issue: "No pending packages found"
**Solution**: All packages have been completed. Generate new packages or reset status in package JSON files

### Issue: High CPU usage
**Solution**: Reduce `--max-parallel` value or use opportunistic mode

### Issue: Package fails
**Solution**: Check logs in `parametric_sweep_packages/logs/` for error details

## Advanced Usage

### Custom Parameter Ranges

Edit `parametric_sweep_orchestrator.py` to customize parameter ranges:

```python
reynolds_numbers = [100, 500, 1000, 2000, 5000]  # Modify these
grid_sizes = [32, 64, 128]
time_steps = [0.001, 0.005, 0.01]
viscosities = [0.01, 0.001, 0.0001]
```

### Custom Priority Logic

Modify the `_calculate_priority()` method in `parametric_sweep_orchestrator.py`:

```python
def _calculate_priority(self, re: float, grid: int, dt: float, nu: float) -> str:
    # Your custom logic here
    if your_condition:
        return "HIGH"
    elif other_condition:
        return "MEDIUM"
    else:
        return "LOW"
```

## License

This parametric sweep system is part of the 3D Navier-Stokes verification framework and is licensed under the MIT License.
