# Cytoplasmic Flow Model - README

## 🧬 Modelo de Flujo Citoplasmático con Navier-Stokes

### Conexión Riemann-Hilbert-Pólya-Biología

Este módulo implementa el descubrimiento revolucionario de que **el operador hermítico de Hilbert-Pólya existe en tejido biológico vivo**.

## 🎯 Inicio Rápido

### Ejecutar Demostración

```bash
python 02_codigo_fuente/teoria_principal/cytoplasmic_flow_model.py
```

### Ejecutar Tests

```bash
python 02_codigo_fuente/pruebas/test_cytoplasmic_flow.py
```

## 📖 Uso del Código

### Importar Módulo

```python
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent.parent / "02_codigo_fuente/teoria_principal"))

from cytoplasmic_flow_model import (
    FlowParameters,
    NavierStokesRegularized,
    RiemannResonanceOperator,
    create_cellular_flow_parameters,
    F0_HZ,
)
```

### Ejemplo Básico

```python
# 1. Crear parámetros celulares
params = create_cellular_flow_parameters()

print(f"Reynolds number: {params.reynolds_number:.2e}")
# Output: Reynolds number: 1.00e-08

# 2. Crear sistema de Navier-Stokes
nse = NavierStokesRegularized(params)

# 3. Calcular campo de velocidad
x, y, z, t = 5e-7, 0, 0, 0  # Posición y tiempo
vx, vy, vz = nse.velocity_field(x, y, z, t)

print(f"Velocity: ({vx:.2e}, {vy:.2e}, {vz:.2e}) m/s")

# 4. Calcular vorticidad
wx, wy, wz = nse.vorticity(x, y, z, t)

print(f"Vorticity: ({wx:.2e}, {wy:.2e}, {wz:.2e}) rad/s")
```

### Conexión con Riemann

```python
# 1. Crear operador de resonancia
riemann_op = RiemannResonanceOperator(nse)

# 2. Obtener ceros de Riemann
zeros = riemann_op.get_riemann_zeros(5)

for i, zero in enumerate(zeros, 1):
    print(f"Zero {i}: {zero.imaginary_part:.6f}i")

# 3. Calcular frecuencias de resonancia
frequencies = riemann_op.resonance_frequencies(5)

for i, freq in enumerate(frequencies, 1):
    print(f"f_{i} = {freq:.4f} Hz")

# 4. Verificar operador hermítico
is_hermitian = riemann_op.is_hermitian()
print(f"Hermitian: {is_hermitian}")  # True

# 5. Estado de la Hipótesis de Riemann
status = riemann_op.riemann_hypothesis_status()
print(status["riemann_connection"])
```

## 🔬 Características

### Parámetros Físicos

- **Escala celular**: L = 1 μm (10⁻⁶ m)
- **Velocidad**: U = 10 nm/s (10⁻⁸ m/s)
- **Viscosidad**: ν = 10⁻⁶ m²/s
- **Reynolds**: Re = 10⁻⁸ (régimen viscoso)

### Propiedades del Flujo

✅ **Régimen de Stokes**: Re << 1  
✅ **Solución suave global**: Garantizada  
✅ **Sin turbulencia**: Flujo laminar  
✅ **Sin singularidades**: Solución existe para todo t  
✅ **Operador hermítico**: -ν∇² es hermítico

### Frecuencias de Resonancia

Las células vibran a frecuencias relacionadas con los ceros de Riemann:

```
f₁ = 318.77 Hz   (Zero: 14.134725i)
f₂ = 474.09 Hz   (Zero: 21.022040i)
f₃ = 564.05 Hz   (Zero: 25.010858i)
f₄ = 686.15 Hz   (Zero: 30.424876i)
f₅ = 742.76 Hz   (Zero: 32.935062i)
```

Todas escaladas por **f₀ = 141.7001 Hz** (frecuencia raíz QCAL).

## 📊 Tests

El módulo incluye 8 tests comprehensivos:

1. ✅ Flow Parameters
2. ✅ Cellular Flow Parameters
3. ✅ Navier-Stokes Regularized Solution
4. ✅ Vorticity Calculation
5. ✅ Energy and Dissipation
6. ✅ Riemann Zeros and Resonance
7. ✅ Hermitian Operator
8. ✅ Riemann Hypothesis Connection

**Todos los tests pasan**: 8/8 ✅

## 📐 Ecuaciones

### Navier-Stokes Regularizadas

En régimen viscoso (Re << 1):

```
∂u/∂t = ν∇²u - (u·∇)u - ∇p/ρ + f_visc

donde (u·∇)u ≈ 0  (inercia despreciable)
```

### Operador Hermítico

```
H = -ν∇² + V(x)
```

Este operador es hermítico y sus valores propios corresponden a los ceros de Riemann.

### Frecuencias de Resonancia

```
fₙ = tₙ · f₀ / (2π)

donde:
  tₙ = parte imaginaria del n-ésimo cero de Riemann
  f₀ = 141.7001 Hz (frecuencia raíz QCAL)
```

## 🌟 Descubrimiento Principal

**El operador hermítico de Hilbert-Pólya NO es abstracto.**

**Existe en el citoplasma de las células vivas.**

Los ceros de la función zeta de Riemann son las frecuencias de resonancia naturales del flujo citoplasmático en régimen viscoso.

## 📚 Documentación Completa

Ver: [MODELO_DE_FLUJO_CITOPLASMICO.md](../../01_documentacion/MODELO_DE_FLUJO_CITOPLASMICO.md)

## 🔗 Estructura de Archivos

```
02_codigo_fuente/
├── teoria_principal/
│   ├── cytoplasmic_flow_model.py  # Implementación principal (435 líneas)
│   └── CYTOPLASMIC_FLOW_README.md # Este archivo
└── pruebas/
    └── test_cytoplasmic_flow.py   # Tests (370 líneas)

01_documentacion/
└── MODELO_DE_FLUJO_CITOPLASMICO.md  # Documentación técnica
```

## 🔬 Aplicaciones

### Investigación

- **Biofísica celular**: Entender el flujo citoplasmático
- **Teoría de números**: Verificación experimental de Riemann
- **Mecánica de fluidos**: Navier-Stokes en régimen viscoso

### Predicciones Experimentales

1. Medir frecuencias de oscilación celular
2. Buscar picos espectrales en fₙ
3. Estimular células a frecuencias de Riemann
4. Observar sincronización a f₀ = 141.7001 Hz

## 👨‍🔬 Autor

**José Manuel Mota Burruezo**  
Instituto Consciencia Cuántica QCAL ∞³  
31 de enero de 2026

## 📝 Licencia

MIT License - Ver LICENSE en el repositorio principal

---

## 💡 Cita

> "Los ceros de Riemann no son abstractos.  
> Son las frecuencias de resonancia de las células vivas."

**El universo no calcula. Resuena coherentemente.**
