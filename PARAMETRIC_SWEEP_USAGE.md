# Parametric Sweep Orchestrator - Usage Guide

## Overview

The parametric sweep orchestrator allows systematic exploration of the Ψ-NSE parameter space through modular, independently executable packages. This enables efficient distributed computation and scientific investigation of the system's behavior across different regimes.

## Quick Start

### 1. Generate Parameter Packages

```bash
python parametric_sweep_orchestrator.py
```

This creates:
- `parametric_sweep_packages/` directory
- 90 package files (10 simulations each)
- `metadata.json` with overall statistics
- `priority_summary.json` with classified packages

### 2. Review Generated Packages

```bash
# View priority summary
cat parametric_sweep_packages/priority_summary.json

# Inspect a specific package
cat parametric_sweep_packages/package_0014.json
```

### 3. Execute a Package

```python
from parametric_sweep_orchestrator import run_package

# Execute a high-priority package with 4 workers
result = run_package(package_id=14, n_workers=4)

print(f"Completed: {result['n_success']} successful, {result['n_failed']} failed")
```

## Parameter Space

The orchestrator explores:

| Parameter | Range | Points | Scale |
|-----------|-------|--------|-------|
| f₀ (Hz) | 100 - 1000 | 20 | logarithmic |
| Re | 100 - 1000 | 15 | logarithmic |
| N | 32, 64, 128 | 3 | discrete |
| T_max (s) | 10.0 | 1 | fixed |

**Total combinations**: 900 simulations (20 × 15 × 3)

## Priority Classification

### HIGH Priority (4 packages)
- f₀ ≈ 141.7 Hz (predicted emergence frequency)
- Re ∈ [100, 500] (moderate turbulence)
- N = 64 or 128 (sufficient resolution)

**Focus**: Core validation of theoretical predictions

### MEDIUM Priority (15 packages)
- f₀ moderately distant from 141.7 Hz
- Re ∈ [500, 1000] or Re < 100
- Mixed resolution

**Focus**: Regime boundary exploration

### LOW Priority (71 packages)
- f₀ far from 141.7 Hz
- Extreme parameter corners
- Lower resolution exploratory runs

**Focus**: Complete parameter space coverage

## Computational Cost Estimates

| Metric | Per Simulation | Total (900 sims) |
|--------|---------------|------------------|
| Time | ~0.9 minutes | ~13.7 hours |
| Memory (peak) | ~0.02-0.07 GB | 0.07 GB |
| Disk (with snapshots) | ~2.5 GB | ~2.3 TB |

*Note: Estimates based on N³ scaling and FFT operations*

## Direct Simulation API

For custom parameter exploration:

```python
from psi_nse_dns_complete import run_psi_nse_simulation

# Run single simulation
result = run_psi_nse_simulation(
    N=64,               # Grid resolution
    L=2*3.14159,        # Domain size
    T=10.0,             # Simulation time
    nu=0.001,           # Viscosity
    f0=141.7,           # Coherence frequency
    dt=0.001,           # Time step
    save_interval=0.1,  # Snapshot interval
    verbose=True        # Show progress
)

# Access results
print(f"Final energy: {result['final_energy']}")
print(f"Detected frequency: {result['detected_frequency_Hz']} Hz")
print(f"Blow-up detected: {result['blow_up_detected']}")
```

## Result Structure

Each simulation returns:

```python
{
    'parameters': {
        'f0_Hz': float,
        'nu': float,
        'N': int,
        'L': float,
        'dt': float,
        'T_max': float,
        'Re': float
    },
    'time': [t0, t1, ..., tN],
    'energy': [E0, E1, ..., EN],
    'enstrophy': [Ω0, Ω1, ..., ΩN],
    'detected_frequency_Hz': float,
    'final_energy': float,
    'final_enstrophy': float,
    'max_energy': float,
    'min_energy': float,
    'blow_up_detected': bool,
    'frequency_error_percent': float
}
```

## Package Execution Workflow

1. **Load Package**: `pkg = load_package(package_id)`
2. **Estimate Cost**: `cost = estimate_computational_cost(pkg)`
3. **Execute**: `results = run_package(package_id, n_workers=4)`
4. **Save Results**: Automatically saved to `parametric_sweep_results/`

## Parallel Execution

The orchestrator uses `multiprocessing.Pool` for parallel execution:

```python
# Automatic worker count (uses CPU count)
run_package(package_id=14)

# Explicit worker count
run_package(package_id=14, n_workers=8)

# Sequential execution
run_package(package_id=14, n_workers=1)
```

## Error Handling

Simulations that fail return:

```python
{
    'status': 'failed',
    'params': {...},
    'error': str(exception),
    'completed_at': timestamp
}
```

This allows the sweep to continue even if individual simulations fail.

## Testing

Run the test suite:

```bash
python -m unittest test_parametric_sweep_orchestrator.py -v
```

Tests cover:
- ✅ Parameter package creation
- ✅ Cost estimation
- ✅ Priority assignment
- ✅ Package save/load
- ✅ Single simulation execution

## Scientific Workflow

### Phase 1: High-Priority Validation
```python
# Execute packages 14-17 (HIGH priority)
for pkg_id in [14, 15, 16, 17]:
    run_package(pkg_id, n_workers=4)
```

### Phase 2: Medium-Priority Exploration
```python
# Execute MEDIUM priority packages
medium_ids = [2, 3, 12, 13, 18, ...]  # From priority_summary.json
for pkg_id in medium_ids:
    run_package(pkg_id, n_workers=4)
```

### Phase 3: Complete Coverage
```python
# Execute remaining LOW priority packages
# Can be done incrementally as resources allow
```

## References

- **Main simulation**: `psi_nse_dns_complete.py`
- **Orchestrator**: `parametric_sweep_orchestrator.py`
- **Tests**: `test_parametric_sweep_orchestrator.py`
- **Theory**: See repository documentation for Ψ-NSE formulation

## Notes

- Generated package files are excluded from git (see `.gitignore`)
- Results directory is also excluded from git
- Packages can be executed independently on different machines
- Package JSON format allows easy integration with workflow managers
