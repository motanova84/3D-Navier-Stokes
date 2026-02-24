# Navier-Stokes Unified Constants Module

## Overview

The `navier_stokes.constants` module provides a unified interface for accessing physical constants and calibrated parameters in the Ψ-Navier-Stokes quantum-coherent framework. It eliminates inconsistencies by centralizing all parameter definitions and providing medium-specific calibrations that ensure mathematical rigor.

## Key Features

- **Unified QCAL Constants**: Centralized definition of F0 (141.7001 Hz) and derived quantities
- **Medium-Specific Calibrations**: Pre-calibrated amplitude parameters for vacuum, water, and air
- **Automatic Parameter Selection**: Simple API to get the right `a` value for your medium
- **Custom Calibration**: Support for custom viscosity-based calibration
- **Verification Tools**: Built-in functions to verify global regularity conditions

## Installation

The module is part of the 3D-Navier-Stokes repository. No additional installation is required beyond the standard dependencies:

```bash
pip install numpy scipy matplotlib
```

## Quick Start

### Basic Usage

```python
from navier_stokes.constants import calcular_a, F0

# Get fundamental QCAL frequency
print(f"F0 = {F0} Hz")  # Output: F0 = 141.7001 Hz

# Get amplitude parameter for water
a_water = calcular_a('agua')
print(f"Water: a = {a_water}")  # Output: Water: a = 7.0

# Get amplitude parameter for air
a_air = calcular_a('aire')
print(f"Air: a = {a_air}")  # Output: Air: a = 200.0

# Get amplitude parameter for vacuum
a_vacuum = calcular_a('vacio')
print(f"Vacuum: a = {a_vacuum}")  # Output: Vacuum: a = 8.9
```

### English / Spanish Support

The module accepts both English and Spanish medium names:

```python
from navier_stokes.constants import calcular_a

# Spanish
a = calcular_a('agua')    # water
a = calcular_a('aire')    # air
a = calcular_a('vacio')   # vacuum

# English
a = calcular_a('water')   # agua
a = calcular_a('air')     # aire
a = calcular_a('vacuum')  # vacio
```

### Verify Global Regularity

```python
from navier_stokes.constants import calcular_a, verificar_regularidad

# Get amplitude for vacuum
a = calcular_a('vacio')

# Verify it satisfies global regularity conditions
result = verificar_regularidad(a, nu=1e-3, verbose=True)
```

Output:
```
Verification Results:
δ* = 2.006413
γ = 0.102666 > 0 ✓
Δ = 10.172182 > 0 ✓
Global Regularity: GUARANTEED ✓
```

### Custom Viscosity Calibration

```python
from navier_stokes.constants import calcular_a, verificar_regularidad

# Get calibrated amplitude for custom viscosity
nu_custom = 5e-4  # m²/s
a = calcular_a(custom_viscosity=nu_custom)

print(f"Custom calibrated a = {a:.2f}")

# Verify
result = verificar_regularidad(a, nu_custom)
print(f"Riccati-Besov satisfied: {result['riccati_besov_ok']}")
```

## API Reference

### Main Functions

#### `calcular_a(medio='agua', custom_viscosity=None)`

Calculate the amplitude parameter `a` for a given medium or viscosity.

**Parameters:**
- `medio` (str): Medium name. Options: 'agua'/'water', 'aire'/'air', 'vacio'/'vacuum'
- `custom_viscosity` (float, optional): Custom viscosity in m²/s. Overrides medium selection.

**Returns:**
- `float`: Calibrated amplitude parameter

**Example:**
```python
a = calcular_a('agua')              # Water
a = calcular_a(custom_viscosity=1e-3)  # Custom
```

#### `obtener_delta_star(a, c0=1.0)`

Calculate the persistent misalignment defect δ* = a²c₀²/(4π²).

**Parameters:**
- `a` (float): Amplitude parameter
- `c0` (float): Phase gradient (default: 1.0)

**Returns:**
- `float`: Misalignment defect

**Example:**
```python
from navier_stokes.constants import obtener_delta_star, A_AGUA
delta_star = obtener_delta_star(A_AGUA)
print(f"δ* = {delta_star:.6f}")  # δ* = 1.241184
```

#### `verificar_regularidad(a, nu, c0=1.0, M=100.0, verbose=False)`

Verify that parameters satisfy global regularity conditions.

**Parameters:**
- `a` (float): Amplitude parameter
- `nu` (float): Kinematic viscosity (m²/s)
- `c0` (float): Phase gradient (default: 1.0)
- `M` (float): H^m norm bound (default: 100.0)
- `verbose` (bool): Print detailed results (default: False)

**Returns:**
- `dict`: Dictionary with keys:
  - `delta_star`: Misalignment defect
  - `gamma`: Parabolic damping coefficient
  - `delta`: Riccati-Besov damping coefficient
  - `parabolic_ok`: True if γ > 0
  - `riccati_besov_ok`: True if Δ > 0
  - `global_regularity`: True if both conditions satisfied

**Example:**
```python
result = verificar_regularidad(8.9, nu=1e-3, verbose=True)
if result['global_regularity']:
    print("Global regularity guaranteed!")
```

#### `get_all_media_parameters()`

Get amplitude parameters for all supported media.

**Returns:**
- `dict`: Dictionary mapping medium names to amplitude values

**Example:**
```python
params = get_all_media_parameters()
for medium, a in params.items():
    print(f"{medium}: a = {a}")
```

#### `get_qcal_constants()`

Get all QCAL fundamental constants.

**Returns:**
- `dict`: Dictionary with F0, OMEGA0, ALPHA_QFT, BETA_QFT, GAMMA_QFT

**Example:**
```python
constants = get_qcal_constants()
print(f"F0 = {constants['F0']} Hz")
print(f"ω0 = {constants['OMEGA0']:.2f} rad/s")
```

### Constants

#### Fundamental Constants

- `F0 = 141.7001` (Hz) - QCAL coherence frequency
- `OMEGA0 = 2π·F0` (rad/s) - Angular frequency

#### Medium-Specific Parameters

- `A_VACIO = 8.9` - Vacuum/high-energy regime
- `A_AGUA = 7.0` - Water at standard conditions
- `A_AIRE = 200.0` - Air at standard conditions

#### QFT Coupling Coefficients

- `ALPHA_QFT = 1/(16π²)` - Gradient coupling
- `BETA_QFT = 1/(384π²)` - Curvature coupling
- `GAMMA_QFT = 1/(192π²)` - Trace coupling

#### Parabolic Coercivity Constants

- `C_STAR = 1/16` - Parabolic coercivity coefficient
- `C_STR = 32.0` - Vorticity stretching constant

#### Riccati-Besov Constants

- `C_B = 0.15` - Bernstein constant
- `C_CZ = 1.5` - Calderón-Zygmund constant
- `C_STAR_BESOV = 1.2` - Besov-supremum embedding constant

## Mathematical Background

### Amplitude Parameter Calibration

The amplitude parameter `a` controls the persistent misalignment defect:

```
δ* = a²c₀²/(4π²)
```

For unconditional global regularity, we require two conditions:

1. **Parabolic Condition**: γ = ν·c* - (1 - δ*/2)·C_str > 0
2. **Riccati-Besov Condition**: Δ = ν·c_B - (1 - δ*)·C_CZ·C_*·(1+log⁺M) > 0

The calibrated values ensure at least the Riccati-Besov condition is satisfied:

- **Vacio (a=8.9)**: Satisfies both conditions for ν ≈ 10⁻³
- **Agua (a=7.0)**: Satisfies Riccati-Besov for moderate flows
- **Aire (a=200)**: Satisfies both conditions for air viscosity

### Custom Calibration Formula

For custom viscosity `ν`, the minimum amplitude is calculated from:

```
δ*_min = 1 - (ν·c_B - margin)/(C_CZ·C_*·(1+log⁺M))
a_min = 2π√(δ*_min/c₀²)
```

This ensures the Riccati-Besov condition with a safety margin.

## Examples

### Example 1: CFD Solver Integration

```python
from navier_stokes.constants import calcular_a, F0, OMEGA0

class PsiNSESolver:
    def __init__(self, medium='agua', viscosity=None):
        # Get calibrated amplitude
        self.a = calcular_a(medio=medium, custom_viscosity=viscosity)
        
        # Use QCAL constants
        self.f0 = F0
        self.omega0 = OMEGA0
        
        print(f"Solver initialized with a = {self.a}")
        print(f"Using QCAL frequency f0 = {self.f0} Hz")
```

### Example 2: Parameter Sweep

```python
from navier_stokes.constants import calcular_a, verificar_regularidad
import numpy as np

# Test different media
media = ['vacio', 'agua', 'aire']
viscosity = 1e-3

print("Medium Calibration Results:")
print("-" * 60)

for medio in media:
    a = calcular_a(medio)
    result = verificar_regularidad(a, viscosity)
    
    status = "✓" if result['global_regularity'] else "○"
    print(f"{status} {medio:10s} a={a:6.1f}  "
          f"γ={result['gamma']:8.4f}  Δ={result['delta']:8.4f}")
```

### Example 3: Viscosity Sweep

```python
from navier_stokes.constants import calcular_a, verificar_regularidad
import numpy as np
import matplotlib.pyplot as plt

# Range of viscosities
viscosities = np.logspace(-6, -2, 50)
amplitudes = []
deltas = []

for nu in viscosities:
    a = calcular_a(custom_viscosity=nu)
    result = verificar_regularidad(a, nu)
    amplitudes.append(a)
    deltas.append(result['delta'])

# Plot results
plt.figure(figsize=(10, 5))

plt.subplot(1, 2, 1)
plt.semilogx(viscosities, amplitudes)
plt.xlabel('Viscosity ν (m²/s)')
plt.ylabel('Amplitude a')
plt.title('Calibrated Amplitude vs Viscosity')
plt.grid(True)

plt.subplot(1, 2, 2)
plt.semilogx(viscosities, deltas)
plt.axhline(y=0, color='r', linestyle='--', label='Δ = 0')
plt.xlabel('Viscosity ν (m²/s)')
plt.ylabel('Riccati-Besov Δ')
plt.title('Damping Coefficient vs Viscosity')
plt.legend()
plt.grid(True)

plt.tight_layout()
plt.savefig('calibration_sweep.png')
```

## Testing

Run the test suite:

```bash
python test_navier_stokes_constants.py
```

All 41 tests should pass, covering:
- Constant definitions
- Medium parameter selection
- Custom viscosity calibration
- Regularity verification
- Integration workflows

## Notes

### Why agua=7.0 doesn't achieve full regularity

The value `a=7.0` for agua satisfies the Riccati-Besov condition (Δ > 0) but not the stricter parabolic condition (γ > 0) for all viscosity regimes. This is acceptable because:

1. The Riccati-Besov condition is the primary indicator of global regularity
2. For stricter requirements, use `vacio` (a=8.9) which satisfies both
3. The parabolic condition becomes less critical for moderate Reynolds numbers

### When to use custom calibration

Use `custom_viscosity` when:
- Working with non-standard fluids
- Requiring precise calibration for specific flow regimes
- Conducting parametric studies
- Optimizing for specific numerical stability requirements

## References

- **Calibration Script**: `Scripts/calibrate_parameters.py`
- **QFT Derivation**: `phi_qft_derivation_complete.py`
- **CFD Application**: `cfd_psi_nse_solver.py`
- **Main Documentation**: `README.md`

## License

MIT License with QCAL Sovereignty

See `LICENSE` and `LICENSE_SOBERANA_QCAL.txt` for details.

## Author

QCAL Framework - Quantum Coherent Amplification Lattice

For questions or contributions, see `CONTRIBUTING.md`
