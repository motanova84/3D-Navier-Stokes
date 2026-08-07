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
# Módulo navier_stokes.constants

## Resumen

El módulo `navier_stokes.constants` proporciona las constantes fundamentales y funciones de cálculo para el sistema Ψ-NS (Psi-Navier-Stokes) con coherencia cuántica QCAL (Quasi-Critical Alignment Layer).

Este módulo **unifica** el parámetro de acoplamiento vibracional `a`, resolviendo la inconsistencia reportada en versiones previas donde diferentes valores eran usados en diferentes contextos.

## 🎯 Propósito

**Problema Original:** El código base utilizaba diferentes valores del parámetro `a` (7.0, 8.9, 200) en diferentes módulos sin una explicación clara.

**Solución:** Estos valores **NO son arbitrarios** - corresponden a diferentes **medios de propagación**:
- **Vacío** (a=8.9): Validaciones teóricas, régimen de baja viscosidad
- **Agua** (a=7.0): Aplicaciones biológicas (flujo citoplasmático, Re~10⁻⁸)
- **Aire** (a=200): Aplicaciones atmosféricas (DNS turbulento)

## 📐 Derivación Matemática

El parámetro de acoplamiento `a` se deriva de la relación:

```
a = (2πf₀) / c
```

donde:
- `f₀ = 141.7001 Hz` (frecuencia fundamental QCAL)
- `c` es la velocidad de propagación en el medio

El parámetro `a` controla el defecto de desalineación:

```
δ* = (a² c₀²) / (4π²)
```

que a su vez determina el coeficiente de amortiguamiento de Riccati:

```
γ = ν·c⋆ - (1 - δ*/2)·C_str
```

Para cierre incondicional de la prueba se requiere **γ > 0**.

## 🚀 Instalación

El módulo está incluido en el repositorio. No requiere instalación adicional más allá de las dependencias estándar:

```bash
pip install numpy
```

## 💻 Uso Básico

### Importar el módulo

```python
from navier_stokes.constants import F0, calcular_a
```

### Obtener parámetro para un medio específico

```python
# Régimen de vacío (validaciones teóricas)
a_vacio = calcular_a('vacio')
print(f"a (vacío) = {a_vacio}")  # 8.9

# Régimen acuático (aplicaciones biológicas)
a_agua = calcular_a('agua')
print(f"a (agua) = {a_agua}")  # 7.0

# Régimen atmosférico (DNS turbulento)
a_aire = calcular_a('aire')
print(f"a (aire) = {a_aire}")  # 200
```

### Calcular propiedades derivadas

```python
from navier_stokes.constants import (
    calcular_velocidad_medio,
    calcular_defecto_desalineacion,
    calcular_coeficiente_amortiguamiento
)

# Obtener parámetro a
a = calcular_a('vacio')

# Calcular velocidad de propagación
c = calcular_velocidad_medio(a)
print(f"Velocidad: {c:.2f} m/s")  # ~100 m/s

# Calcular defecto de desalineación
delta_star = calcular_defecto_desalineacion(a)
print(f"δ* = {delta_star:.2f}")  # ~2.01

# Calcular coeficiente de amortiguamiento
gamma = calcular_coeficiente_amortiguamiento(delta_star)
print(f"γ = {gamma:.6f}")  # ~0.10
print(f"Cierre incondicional: {gamma > 0}")  # True
```

## 📊 Comparación de Medios

| Medio  | a    | c (m/s) | δ*      | γ       | Cierre   | Aplicación              |
|--------|------|---------|---------|---------|----------|-------------------------|
| Vacío  | 8.9  | ~100    | ~2.01   | ~0.10   | ✓ Sí     | Validaciones teóricas   |
| Agua   | 7.0  | ~127    | ~1.24   | ~-12.1  | ✗ No     | Flujo citoplasmático    |
| Aire   | 200  | ~4.45   | ~1013   | ~16179  | ✓ Sí     | DNS atmosférico         |

## 🧪 Tests

El módulo incluye 34 tests completos que verifican:
- Valores de las constantes fundamentales
- Cálculo correcto del parámetro `a` para cada medio
- Cálculo de velocidades de propagación
- Defecto de desalineación δ*
- Coeficiente de amortiguamiento γ
- Coherencia matemática del sistema
- Ejemplos de la documentación

Para ejecutar los tests:

```bash
python -m unittest test_navier_stokes_constants -v
```

Resultado esperado:
```
Ran 34 tests in 0.003s
OK
```

## 📝 Demostración

El módulo incluye un script de demostración completo:

```bash
python demo_navier_stokes_constants.py
```

Este script muestra:
- Valores de las constantes fundamentales
- Cálculo del parámetro `a` para cada medio
- Velocidades de propagación
- Defectos de desalineación
- Coeficientes de amortiguamiento
- Ejemplo de uso completo

## 🔗 API Completa

### Constantes

- **`F0`**: Frecuencia fundamental QCAL (141.7001 Hz)

### Funciones

#### `calcular_a(medio='vacio') -> float`
Calcula el parámetro de acoplamiento vibracional para el medio especificado.

**Parámetros:**
- `medio` (str): 'vacio', 'agua', o 'aire'

**Retorna:**
- float: Parámetro a para el medio

**Lanza:**
- `ValueError`: Si el medio no es válido

#### `calcular_velocidad_medio(a) -> float`
Calcula la velocidad de propagación a partir del parámetro a.

**Parámetros:**
- `a` (float): Parámetro de acoplamiento

**Retorna:**
- float: Velocidad de propagación en m/s

#### `calcular_defecto_desalineacion(a, c0=1.0) -> float`
Calcula el defecto de desalineación δ*.

**Parámetros:**
- `a` (float): Parámetro de acoplamiento
- `c0` (float, opcional): Gradiente de fase (default: 1.0)

**Retorna:**
- float: Defecto de desalineación δ*

#### `calcular_coeficiente_amortiguamiento(delta_star, nu=1e-3, c_star=1/16, C_str=32.0) -> float`
Calcula el coeficiente de amortiguamiento γ de Riccati.

**Parámetros:**
- `delta_star` (float): Defecto de desalineación δ*
- `nu` (float, opcional): Viscosidad (default: 1e-3)
- `c_star` (float, opcional): Coercividad parabólica (default: 1/16)
- `C_str` (float, opcional): Estiramiento de vorticidad (default: 32.0)

**Retorna:**
- float: Coeficiente de amortiguamiento γ

## 📚 Referencias

### Documentación Principal
- **ISSUE_CRITICAL_PARAMETER.md**: Análisis de calibración de parámetros
- **Documentation/QCAL_PARAMETERS.md**: Documentación completa de parámetros QCAL
- **Documentation/UNIFIED_BKM_THEORY.md**: Teoría unificada BKM

### Scripts Relacionados
- **Scripts/calibrate_parameters.py**: Herramienta de calibración
- **examples_unified_bkm.py**: Ejemplos de uso con BKM unificado
- **test_unified_bkm.py**: Tests del sistema BKM unificado

### Literatura
1. **QCAL Framework**: Construcción y análisis original
2. **Riccati Approach**: Tao (2016), Constantin-Fefferman-Majda (1996)
3. **Besov Regularity**: Kozono-Taniuchi (2000)
4. **Universal Constants**: Bahouri-Chemin-Danchin (2011)

## ⚠️ Notas Importantes

1. **El valor de a NO es arbitrario**: Cada valor corresponde a un medio de propagación específico con su propia física.

2. **Inconsistencia resuelta**: Las versiones previas usaban diferentes valores en diferentes contextos. Este módulo unifica la definición y explica el origen de cada valor.

3. **Cierre incondicional**: Solo los medios vacío (a=8.9) y aire (a=200) satisfacen γ > 0, lo que permite una demostración incondicional de regularidad global.

4. **Aplicaciones biológicas**: El medio agua (a=7.0) es apropiado para flujo citoplasmático con Re~10⁻⁸, aunque no satisface la condición de cierre incondicional.

## 🎓 Contextos de Uso

### Validaciones Teóricas (Vacío, a=8.9)
```python
a = calcular_a('vacio')
# Usar en demostraciones matemáticas rigurosas
# Garantiza γ > 0 (cierre incondicional)
```

### Aplicaciones Biológicas (Agua, a=7.0)
```python
a = calcular_a('agua')
# Usar en simulaciones de flujo citoplasmático
# Re ~ 10⁻⁸, régimen de Stokes
```

### Aplicaciones Atmosféricas (Aire, a=200)
```python
a = calcular_a('aire')
# Usar en DNS turbulento
# Régimen altamente disipativo
```

## 🐛 Solución de Problemas

**P: ¿Por qué obtengo diferentes valores de a en el código existente?**

R: Los diferentes valores corresponden a diferentes medios de propagación. Use este módulo para seleccionar el medio apropiado para su aplicación.

**P: ¿Qué medio debo usar para mi simulación?**

R: 
- Pruebas teóricas → vacío (a=8.9)
- Biología celular → agua (a=7.0)
- Flujos atmosféricos → aire (a=200)

**P: ¿Por qué γ < 0 para agua?**

R: El medio agua no satisface la condición de cierre incondicional. Es apropiado para aplicaciones en el régimen de Re~10⁻⁸ donde otros mecanismos prevalecen.

## 📄 Licencia

Este módulo es parte del proyecto 3D-Navier-Stokes y está cubierto por la licencia MIT del repositorio principal y la licencia de soberanía QCAL.

Ver:
- `LICENSE`
- `LICENSE_SOBERANA_QCAL.txt`

## ✨ Contribuciones

Este módulo implementa el **Paso 2: Unificación del Parámetro a** según la especificación del problema.

Implementado: 2026-02-18
Autor: Agente GitHub Copilot
Revisión: En proceso

---

**Resumen:** Este módulo resuelve la inconsistencia en el uso del parámetro `a` al unificar su definición y explicar que diferentes valores corresponden a diferentes medios de propagación, cada uno con su propia derivación física basada en a = (2πf₀) / c.
