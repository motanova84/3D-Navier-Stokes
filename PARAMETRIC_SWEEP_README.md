# Parametric Sweep Orchestration System

Complete system for running parametric sweeps of 3D Navier-Stokes simulations with intelligent execution management.

## 🎯 Overview

This system enables organized execution of large-scale parametric studies by:
- Automatically generating simulation packages with different parameter combinations
- Prioritizing packages based on computational cost and scientific value
- Supporting multiple execution modes (single, batch, continuous, opportunistic)
- Providing real-time monitoring and progress reporting

## 📦 Components

### Core Scripts

1. **`parametric_sweep_orchestrator.py`** - Package Generator
   - Defines parameter space for simulations
   - Generates organized simulation packages
   - Assigns priorities (HIGH, MEDIUM, LOW)
   - Creates metadata and tracking files

2. **`run_package.py`** - Package Executor
   - Executes individual simulation packages
   - Tracks results and failures
   - Supports dry-run mode for testing

3. **`parametric_sweep_monitor.py`** - Progress Monitor
   - Displays real-time progress reports
   - Generates detailed markdown reports
   - Shows completion statistics by priority

4. **`batch_execution.sh`** - Batch Executor
   - Runs multiple packages sequentially
   - Supports priority filtering
   - Handles execution limits

5. **`intelligent_executor.py`** - Smart Executor
   - Continuous mode: runs for specified duration
   - Opportunistic mode: runs when system is idle
   - Intelligent resource management

6. **`Makefile`** - Convenient Commands
   - Quick access to all operations
   - Simplified workflow management

7. **`ejemplo_completo.sh`** - Complete Example
   - Interactive usage guide
   - Demonstrates all features
   - User-friendly workflow

## 🚀 Quick Start

### 1. Initial Setup
```bash
# Setup directories
make setup

# Generate simulation packages
make generate-packages

# View what was created
make list-packages
```

### 2. Test the System
```bash
# Run a complete test with dry-run mode
make test-system
```

### 3. Execute Simulations

**Single Package:**
```bash
# Run next pending package
make run-next

# Run specific package
make run-package ID=0
```

**Batch Execution:**
```bash
# Run all HIGH priority packages
make run-batch-high

# Run all MEDIUM priority packages
make run-batch-medium

# Run all packages
make run-batch-all
```

**Continuous Execution:**
```bash
# Run continuously for 24 hours
make run-continuous

# Run for custom duration (e.g., 12 hours)
make run-continuous-hours HOURS=12

# Run only HIGH priority continuously
make run-continuous-high
```

**Opportunistic Mode:**
```bash
# Run in background when system is idle
make run-opportunistic

# Run HIGH priority opportunistically
make run-opportunistic-high
```

### 4. Monitor Progress
```bash
# Show current progress
make monitor

# Generate detailed report
make detailed-report

# Watch progress in real-time (updates every 10s)
make watch-progress
```

## 📊 Parameter Space

The system automatically sweeps over:

- **Viscosity (ν)**: `[1e-2, 1e-3, 1e-4]` - Controls Reynolds number
- **Grid Resolution (N)**: `[64, 128]` - Spatial discretization
- **Coupling Strength (α)**: `[0.01, 0.1, 0.5]` - QFT coupling parameter
- **Simulation Time (T_max)**: `[2.0, 5.0, 10.0]` - Duration in seconds
- **Initial Conditions**: `['taylor_green', 'random', 'shear_layer']`
- **Time Step (dt)**: `[0.001, 0.0005]` - Temporal resolution

**Total**: 324 unique parameter combinations organized into 33 packages.

## 🎯 Priority System

Packages are automatically prioritized:

### HIGH Priority (48 simulations, 5 packages)
- Standard resolution (N=64)
- Moderate viscosity (ν ≥ 1e-3)
- Short to medium runtime (T_max ≤ 5.0)
- Low coupling (α ≤ 0.1)
- **Use case**: Quick validation and standard cases

### MEDIUM Priority (186 simulations, 19 packages)
- Mixed parameters
- Balanced computational cost
- **Use case**: Extended parameter exploration

### LOW Priority (90 simulations, 9 packages)
- High resolution (N=128)
- Extreme parameters (ν=1e-4 or T_max=10.0)
- Highest computational cost
- **Use case**: High-fidelity extreme cases

## 📋 Usage Examples

### Example 1: Quick Validation
```bash
# Setup and run high priority tests
make setup
make generate-packages
make run-batch-high
make monitor
```

### Example 2: Long-Running Study
```bash
# Setup continuous execution
make setup
make generate-packages

# Run for 24 hours in background
nohup make run-continuous > continuous.log 2>&1 &

# Monitor progress
tail -f continuous.log

# Check status anytime
make monitor
```

### Example 3: Opportunistic Execution
```bash
# Start opportunistic mode in background
nohup make run-opportunistic > opportunistic.log 2>&1 &

# System will automatically run packages when idle
# Check progress periodically
make monitor
```

### Example 4: Interactive Guide
```bash
# Run the complete interactive example
./ejemplo_completo.sh
```

This will:
1. Setup the system
2. Generate packages
3. Show summary
4. Run a test package
5. Ask how you want to proceed
6. Execute your choice
7. Display progress

## 🛠️ Advanced Usage

### Custom Package Generation
```bash
# Generate with different simulations per package
python3 parametric_sweep_orchestrator.py --sims-per-package 5

# List packages with priority filter
python3 parametric_sweep_orchestrator.py --list --priority HIGH
```

### Custom Package Execution
```bash
# Run with priority filter
python3 run_package.py --next --priority HIGH

# Dry run mode (test without executing)
python3 run_package.py --package-id 0 --dry-run
```

### Custom Batch Execution
```bash
# Limit number of packages
./batch_execution.sh --priority HIGH --max-packages 3

# Dry run batch
./batch_execution.sh --dry-run
```

### Custom Continuous Execution
```bash
# Run for 6 hours with HIGH priority only
python3 intelligent_executor.py --continuous 6 --priority HIGH

# Custom sleep time between packages
python3 intelligent_executor.py --continuous 24 --sleep-between 120
```

## 📁 Directory Structure

```
parametric_sweep_packages/
├── metadata.json              # Overall package metadata
├── priority_summary.json      # Priority distribution
├── package_0000.json          # Individual package files
├── package_0001.json
├── ...
└── results/                   # Execution results
    ├── package_0000_results.json
    ├── package_0001_results.json
    └── ...
```

## 🧹 Cleanup

```bash
# Remove all packages and results
make clean

# Remove only results (keep packages)
make clean-results
```

## 📖 Make Commands Reference

```
📦 SETUP & GENERATION:
  make setup              - Initial setup (create directories)
  make generate-packages  - Generate simulation packages
  make list-packages      - List all packages

▶️  EXECUTION:
  make run-next           - Run next pending package
  make run-package ID=N   - Run specific package by ID
  make run-batch-high     - Run all HIGH priority packages
  make run-batch-medium   - Run all MEDIUM priority packages
  make run-batch-all      - Run all pending packages

🔄 CONTINUOUS EXECUTION:
  make run-continuous     - Run continuously for 24h
  make run-opportunistic  - Run in opportunistic mode

📊 MONITORING:
  make monitor            - Show progress report
  make detailed-report    - Generate detailed markdown report

🧪 TESTING:
  make test-system        - Test system with dry run

🧹 CLEANUP:
  make clean              - Remove all packages and results
  make clean-results      - Remove only results (keep packages)
```

## 🔧 Integration

To integrate actual simulation code:

1. Modify `run_package.py`, function `run_simulation()`
2. Import your simulation module
3. Pass parameters to your simulation function
4. Return results in the expected format

Example:
```python
def run_simulation(self, params: Dict, dry_run: bool = False) -> Dict:
    if dry_run:
        return {'status': 'completed_dry_run', ...}
    
    # Import your simulation
    from psi_nse_dns_complete import run_dns_simulation
    
    # Run simulation
    results = run_dns_simulation(**params)
    
    return {
        'status': 'completed',
        'params': params,
        'execution_time': results['time'],
        'max_velocity': results['max_vel'],
        'energy_final': results['energy']
    }
```

## 📝 Notes

- All execution modes support `--dry-run` for testing
- Packages are automatically marked as completed to avoid re-execution
- Progress is saved incrementally (safe to interrupt)
- Results include both successful and failed simulations
- All scripts support `--help` for detailed usage

## ✅ System Summary

```
╔═══════════════════════════════════════════════════════════════╗
║  SISTEMA COMPLETO DE BARRIDO PARAMÉTRICO                      ║
╚═══════════════════════════════════════════════════════════════╝

📦 COMPONENTES:
   ✅ parametric_sweep_orchestrator.py  - Generador de paquetes
   ✅ run_package.py                    - Ejecutor individual
   ✅ parametric_sweep_monitor.py       - Monitor de progreso
   ✅ batch_execution.sh                - Ejecución batch
   ✅ intelligent_executor.py           - Ejecutor inteligente
   ✅ Makefile                          - Comandos convenientes
   ✅ ejemplo_completo.sh               - Guía de uso

🎯 MODOS DE EJECUCIÓN:
   1. Individual:    python3 run_package.py --package-id 0
   2. Batch:         ./batch_execution.sh --priority HIGH
   3. Continuo:      make run-continuous
   4. Oportunista:   make run-opportunistic
   5. Siguiente:     make run-next

📊 MONITOREO:
   make monitor  → Genera reporte visual del progreso
```

---

**Ready to use!** Run `make help` to get started.
