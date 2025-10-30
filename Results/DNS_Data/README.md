# DNS Verification Data

This directory stores numerical simulation data from DNS verification runs.

## Expected Contents

- `f0_sweep_results/` - Frequency sweep data (f₀ ∈ [100, 1000] Hz)
- `delta_star_verification/` - Misalignment defect convergence data
- `bkm_integral_data/` - BKM criterion integral data
- Raw HDF5 files from simulation runs

## Data Format

Results are typically stored in HDF5 format with structure:
```
simulation.h5
├── /parameters (attrs: f₀, Re, N, ν)
├── /metrics
│   ├── δ_history
│   ├── besov_norm_history
│   ├── vorticity_inf_history
│   └── riccati_coefficient_history
└── /fields (optional, large)
    ├── velocity
    └── vorticity
```

## Generation

Run DNS verification:
```bash
../../Scripts/run_dns_verification.sh
```

## Note

Large data files are gitignored. Archive important results separately.
