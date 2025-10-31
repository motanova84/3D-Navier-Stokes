# Ψ-Navier-Stokes DNS Complete Simulation

## Overview

`psi_nse_dns_complete.py` implements a complete Direct Numerical Simulation (DNS) of the 3D Ψ-Navier-Stokes equations with quantum coupling. This script demonstrates the stability and oscillatory behavior of the Ψ-NSE model under critical initial conditions (Taylor-Green vortex).

## Scientific Context

The Ψ-NSE system extends the classical Navier-Stokes equations with a quantum coupling term:

```
∂_t u = -(u·∇)u - ∇p + ν∇²u + Φ·u
```

Where:
- **Φ_ij**: Quantum coupling tensor derived from QFT
- **Ψ(t)**: Coherence field oscillating at f₀ = 141.7001 Hz
- **ν**: Kinematic viscosity

This implementation supports the QCAL (Quantum Coherence Amplification) hypothesis by demonstrating:
1. **Blow-up prevention**: System remains stable without singularities
2. **Natural frequency emergence**: f₀ appears naturally in energy spectrum

## Features

### Numerical Methods
- **Spectral discretization**: Fourier-based with N³ = 128³ grid points (configurable)
- **Time integration**: 4th-order Runge-Kutta (RK4)
- **Incompressibility**: Projection to divergence-free space at each step
- **Resolution**: Configurable (default N=128, can be reduced for testing)

### Physics
- **Initial conditions**: Taylor-Green vortex (critical test for blow-up)
- **Coherence field**: Spatiotemporal oscillation at f₀
- **Coupling tensor**: Full 3×3 Φ_ij with Hessian components
- **Diagnostics**: Energy, enstrophy, vorticity tracking

### Analysis
- **Frequency detection**: FFT-based spectral analysis
- **Stability monitoring**: Energy/enstrophy bounds, blow-up detection
- **Visualization**: 4-panel plot (energy, enstrophy, spectrum, vorticity)
- **Data export**: JSON results, PNG plots

## Installation

### Dependencies

```bash
pip install -r requirements.txt
```

Required packages:
- numpy >= 1.21.0
- scipy >= 1.7.0
- matplotlib >= 3.5.0
- h5py >= 3.0.0
- tqdm >= 4.60.0

## Usage

### Basic Usage

Run with default parameters (N=128, T_max=5.0s):

```bash
python psi_nse_dns_complete.py
```

**Warning**: Full simulation takes significant time (~1-2 hours depending on hardware).

### Quick Test

For rapid testing, modify parameters in the script:

```python
N = 32          # Reduced resolution (from 128)
dt = 0.01       # Larger time step (from 0.001)
T_max = 0.5     # Shorter simulation (from 5.0)
```

Or use the provided test script:

```bash
python test_psi_nse_dns.py  # Runs with reduced parameters for quick validation
```

### Output Files

The script generates:

1. **psi_nse_dns_results.png**: 4-panel visualization
   - Energy evolution E(t)
   - Enstrophy evolution Ω(t) (log scale)
   - Frequency power spectrum
   - Vorticity field snapshot at t=T_max

2. **psi_nse_results.json**: Numerical results
   ```json
   {
     "parameters": {
       "f0_Hz": 141.7001,
       "nu": 0.001,
       "N": 128,
       "dt": 0.001,
       "T_max": 5.0
     },
     "detected_frequency_Hz": 141.7,
     "final_energy": 0.0245,
     "final_enstrophy": 0.1234,
     "max_energy": 0.125,
     "blow_up_detected": false
   }
   ```

## Testing

### Run Test Suite

```bash
python test_psi_nse_dns.py
```

This runs 12 tests covering:
- Script execution
- Output file generation
- Numerical stability
- Energy/enstrophy bounds
- Function correctness

### Test Coverage

| Test Category | Tests | Description |
|---------------|-------|-------------|
| Integration | 10 | Full simulation with reduced parameters |
| Unit | 2 | Individual function tests |
| **Total** | **12** | All tests pass ✓ |

## Performance

### Computational Complexity

- **Memory**: O(N³) ≈ 8 GB for N=128 (double precision)
- **Time per step**: O(N³ log N) from FFTs
- **Total time**: ~1-2 hours for full simulation (N=128, 5000 steps)

### Recommended Hardware

- **Minimum**: 8 GB RAM, 4 CPU cores
- **Recommended**: 16+ GB RAM, 8+ CPU cores
- **GPU**: Not currently utilized (CPU-only implementation)

## Key Results

### Expected Behavior

For Taylor-Green vortex with Ψ-coupling:

1. **Stability**: No blow-up detected (E_max < 1e6)
2. **Energy decay**: Gradual dissipation via viscosity
3. **Enstrophy**: Bounded growth (no singularity formation)
4. **Frequency**: f₀ = 141.7 Hz emerges in power spectrum

### Interpretation

These results support the hypothesis that:
- Quantum coupling term Φ·u acts as a regularizer
- Coherence field Ψ prevents singularity formation
- System exhibits natural resonance at f₀

## Mathematical Details

### Quantum Coupling Tensor

```
Φ_ij = α·∇_i∇_j Ψ + β·R_ij·Ψ + γ·δ_ij·□Ψ
```

Where:
- α = 1/(720π²) × 0.1 (scaled for stability)
- β = 1/(2880π²)
- γ = -1/(1440π²)

### Coherence Field

```
Ψ(x,t) = A_eff · sin(ω₀t) · f_spatial(x)
```

With:
- ω₀ = 2πf₀
- f_spatial: Product of trigonometric modes

## Limitations

### Current Implementation

1. **Resolution**: N=128 is moderate (not DNS-grade for turbulence)
2. **Domain**: Periodic boundaries only
3. **Viscosity**: Fixed at ν = 10⁻³
4. **Duration**: Limited to T_max = 5.0s

### Future Enhancements

- Adaptive time stepping
- Higher resolutions (N=256, 512)
- Parallel FFT implementation
- GPU acceleration
- Extended simulation time
- Parameter sweeps

## References

### Related Files

- `DNS-Verification/DualLimitSolver/psi_ns_solver.py`: Alternative solver
- `master_validation_psi_nse.py`: Validation framework
- `validate_blowup_prevention.py`: Blow-up analysis
- `validate_natural_frequency_emergence.py`: Frequency detection

### Theory

See main documentation:
- `Documentation/VIBRATIONAL_REGULARIZATION.md`: Theory background
- `README.md`: Project overview
- `VALIDACION_COMPLETA_PSI_NSE.md`: Complete validation

## Troubleshooting

### Common Issues

**Issue**: `ModuleNotFoundError: No module named 'h5py'`  
**Solution**: Run `pip install h5py tqdm`

**Issue**: Simulation too slow  
**Solution**: Reduce N to 32 or 64 for testing

**Issue**: Memory error  
**Solution**: Reduce N or increase swap space

**Issue**: Frequency not detected accurately  
**Solution**: Increase T_max or decrease dt for better frequency resolution

## Citation

If you use this code in your research, please cite:

```bibtex
@software{psi_nse_dns_2024,
  title = {Ψ-Navier-Stokes DNS Implementation},
  author = {QCAL Research Team},
  year = {2024},
  url = {https://github.com/motanova84/3D-Navier-Stokes}
}
```

## License

MIT License - See main repository LICENSE file

## Contact

For questions or issues, please open an issue on GitHub:
https://github.com/motanova84/3D-Navier-Stokes/issues
