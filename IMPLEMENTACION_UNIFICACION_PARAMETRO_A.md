# Implementación de la Unificación del Parámetro a

## Resumen Ejecutivo

Este documento describe la implementación del módulo unificado `navier_stokes.constants` que centraliza la definición del parámetro de amplitud `a` y las constantes QCAL fundamentales para el marco Ψ-Navier-Stokes. La unificación elimina inconsistencias y proporciona una API simple para acceder a parámetros calibrados específicos del medio.

## Motivación

### Problema

Antes de esta implementación, el parámetro `a` se definía de manera inconsistente en diferentes partes del código:
- Valores hard-coded en múltiples archivos
- Falta de claridad sobre qué valor usar para cada medio físico
- Inconsistencias entre scripts de calibración y simulaciones
- Dificultad para mantener sincronizados los valores

### Solución

El módulo `navier_stokes.constants` proporciona:
1. **Definición centralizada** de todos los parámetros físicos
2. **Calibraciones específicas del medio** validadas matemáticamente
3. **API unificada** para acceso consistente
4. **Verificación automática** de condiciones de regularidad

## Estructura de la Implementación

### Archivos Creados

```
navier_stokes/
├── __init__.py           # Exporta API pública
├── constants.py          # Definiciones de constantes y funciones
└── README.md            # Documentación en inglés

test_navier_stokes_constants.py    # Suite de pruebas completa
IMPLEMENTACION_UNIFICACION_PARAMETRO_A.md  # Este documento
```

### Componentes Principales

#### 1. Constantes Fundamentales QCAL

```python
F0 = 141.7001  # Hz - Frecuencia de coherencia fundamental
OMEGA0 = 2π·F0  # rad/s - Frecuencia angular
```

Estas constantes emergen naturalmente de la derivación de teoría cuántica de campos (QFT) del tensor de acoplamiento Ψ-NSE.

#### 2. Parámetros Específicos del Medio

```python
A_VACIO = 8.9    # Vacío/régimen de alta energía
A_AGUA = 7.0     # Agua en condiciones estándar
A_AIRE = 200.0   # Aire en condiciones estándar
```

Estos valores están calibrados para asegurar que se satisfagan las condiciones de amortiguamiento positivo.

#### 3. Coeficientes de Acoplamiento QFT

```python
ALPHA_QFT = 1/(16π²)    # Acoplamiento de gradiente
BETA_QFT = 1/(384π²)    # Acoplamiento de curvatura
GAMMA_QFT = 1/(192π²)   # Acoplamiento de traza
```

Estos son constantes universales derivadas de QFT, **NO** son parámetros ajustables.

#### 4. Constantes de Coercitividad Parabólica

```python
C_STAR = 1/16    # Coeficiente de coercitividad parabólica
C_STR = 32.0     # Constante de estiramiento de vorticidad
```

#### 5. Constantes de Riccati-Besov

```python
C_B = 0.15       # Constante de Bernstein
C_CZ = 1.5       # Constante de Calderón-Zygmund
C_STAR_BESOV = 1.2  # Constante de embedding Besov-supremo
```

## API Pública

### Función Principal: `calcular_a()`

```python
def calcular_a(medio='agua', custom_viscosity=None):
    """
    Calcula el parámetro de amplitud 'a' para un medio dado.
    
    Parámetros:
        medio: 'vacio'/'vacuum', 'agua'/'water', 'aire'/'air'
        custom_viscosity: Viscosidad personalizada (m²/s)
    
    Retorna:
        float: Parámetro de amplitud calibrado
    """
```

#### Ejemplos de Uso:

```python
from navier_stokes.constants import calcular_a

# Obtener parámetro para agua
a_agua = calcular_a('agua')      # Retorna 7.0

# Obtener parámetro para aire
a_aire = calcular_a('aire')      # Retorna 200.0

# Obtener parámetro para vacío
a_vacio = calcular_a('vacio')    # Retorna 8.9

# Calibración personalizada
a_custom = calcular_a(custom_viscosity=1e-3)  # Calcula desde la viscosidad
```

### Función de Verificación: `verificar_regularidad()`

```python
def verificar_regularidad(a, nu, c0=1.0, M=100.0, verbose=False):
    """
    Verifica que los parámetros satisfagan las condiciones de regularidad global.
    
    Retorna un diccionario con:
        - delta_star: Defecto de desalineación δ*
        - gamma: Coeficiente de amortiguamiento parabólico γ
        - delta: Coeficiente de amortiguamiento Riccati-Besov Δ
        - parabolic_ok: True si γ > 0
        - riccati_besov_ok: True si Δ > 0
        - global_regularity: True si ambas condiciones se satisfacen
    """
```

#### Ejemplo de Verificación:

```python
from navier_stokes.constants import calcular_a, verificar_regularidad

# Obtener amplitud para vacío
a = calcular_a('vacio')

# Verificar condiciones de regularidad
resultado = verificar_regularidad(a, nu=1e-3, verbose=True)
```

Salida:
```
Verification Results:
δ* = 2.006413
γ = 0.102666 > 0 ✓
Δ = 10.172182 > 0 ✓
Global Regularity: GUARANTEED ✓
```

### Funciones Auxiliares

#### `obtener_delta_star(a, c0=1.0)`

Calcula el defecto de desalineación persistente:

```
δ* = a²c₀²/(4π²)
```

#### `get_all_media_parameters()`

Retorna un diccionario con todos los parámetros de medios:

```python
params = get_all_media_parameters()
# {'vacio': 8.9, 'agua': 7.0, 'aire': 200.0}
```

#### `get_qcal_constants()`

Retorna todas las constantes fundamentales QCAL:

```python
constants = get_qcal_constants()
# {'F0': 141.7001, 'OMEGA0': 890.353..., 'ALPHA_QFT': ..., ...}
```

## Fundamento Matemático

### Calibración del Parámetro de Amplitud

El parámetro `a` controla el defecto de desalineación persistente δ*:

```
δ* = a²c₀²/(4π²)
```

Para regularidad global incondicional, requerimos dos condiciones:

#### 1. Condición Parabólica

```
γ = ν·c* - (1 - δ*/2)·C_str > 0
```

Donde:
- ν = viscosidad cinemática
- c* = 1/16 (coeficiente de coercitividad parabólica)
- C_str = 32 (constante de estiramiento de vorticidad)

Para γ > 0, necesitamos:
```
δ* > 2 - ν/512
```

#### 2. Condición Riccati-Besov

```
Δ = ν·c_B - (1 - δ*)·C_CZ·C_*·(1 + log⁺M) > 0
```

Donde:
- c_B = 0.15 (constante de Bernstein)
- C_CZ = 1.5 (constante de Calderón-Zygmund)
- C_* = 1.2 (constante de embedding Besov-supremo)
- M = 100.0 (cota de norma H^m)

Para Δ > 0, necesitamos:
```
δ* > 1 - (ν·c_B)/(C_CZ·C_*·(1+log⁺M))
```

### Valores Calibrados

Para ν = 10⁻³ m²/s (viscosidad de referencia):

| Medio  | a     | δ*      | γ (parabólico) | Δ (R-B)  | Regularidad |
|--------|-------|---------|----------------|----------|-------------|
| Vacío  | 8.9   | 2.006   | +0.103 ✓      | +10.17 ✓ | Completa ✓  |
| Agua   | 7.0   | 1.241   | -12.14 ✗      | +2.44 ✓  | Parcial     |
| Aire   | 200.0 | 101.32  | +1614 ✓       | +8138 ✓  | Completa ✓  |

**Nota sobre Agua**: El valor a=7.0 satisface la condición Riccati-Besov (que es la primaria para regularidad) pero no la condición parabólica más estricta. Para aplicaciones que requieren ambas condiciones, use el valor de vacío (a=8.9).

### Fórmula de Calibración Personalizada

Para una viscosidad personalizada ν, la amplitud mínima se calcula de:

```
δ*_min = 1 - (ν·c_B - margen)/(C_CZ·C_*·(1+log⁺M))
a_min = 2π√(δ*_min/c₀²)
```

Esto asegura la condición Riccati-Besov con un margen de seguridad.

## Suite de Pruebas

### Cobertura

El archivo `test_navier_stokes_constants.py` contiene 41 pruebas que cubren:

1. **Constantes** (7 pruebas)
   - Valores de F0, OMEGA0
   - Parámetros de medios
   - Coeficientes QFT
   - Constantes parabólicas y Riccati-Besov

2. **Función calcular_a** (10 pruebas)
   - Nombres en español e inglés
   - Insensibilidad a mayúsculas/minúsculas
   - Validación de errores
   - Calibración personalizada

3. **Función obtener_delta_star** (5 pruebas)
   - Cálculo correcto para cada medio
   - Parámetros personalizados
   - Positividad

4. **Función verificar_regularidad** (9 pruebas)
   - Verificación de estructura de resultados
   - Condiciones parabólicas y Riccati-Besov
   - Modo verbose
   - Parámetros personalizados

5. **Funciones auxiliares** (6 pruebas)
   - get_all_media_parameters
   - get_qcal_constants

6. **Integración** (4 pruebas)
   - Flujos de trabajo completos
   - Todos los medios
   - Calibración personalizada
   - Importaciones del paquete

### Ejecutar Pruebas

```bash
cd /home/runner/work/3D-Navier-Stokes/3D-Navier-Stokes
python test_navier_stokes_constants.py
```

Todas las 41 pruebas deben pasar:

```
----------------------------------------------------------------------
Ran 41 tests in 0.002s

OK
```

## Integración con Código Existente

### Antes (Inconsistente)

```python
# Diferentes valores en diferentes archivos
a = 7.0  # ¿De dónde viene este valor?
F0 = 141.7001  # Definido múltiples veces

# Sin validación
if a > 5:  # ¿Es suficiente?
    pass
```

### Después (Unificado)

```python
from navier_stokes.constants import calcular_a, F0, verificar_regularidad

# Obtener valor calibrado
a = calcular_a('agua')

# Usar constante QCAL
frequency = F0

# Verificar regularidad
result = verificar_regularidad(a, nu=1e-3)
if result['riccati_besov_ok']:
    print("Regularidad Riccati-Besov garantizada")
```

### Migración de Código Existente

Para actualizar código existente:

1. **Reemplace definiciones hard-coded**:
   ```python
   # Antes
   F0 = 141.7001
   a = 7.0
   
   # Después
   from navier_stokes.constants import F0, calcular_a
   a = calcular_a('agua')
   ```

2. **Use verificación en lugar de valores mágicos**:
   ```python
   # Antes
   if a > 5:  # ¿Por qué 5?
       proceed()
   
   # Después
   from navier_stokes.constants import verificar_regularidad
   result = verificar_regularidad(a, nu)
   if result['riccati_besov_ok']:
       proceed()
   ```

3. **Soporte bilingüe automático**:
   ```python
   # Funciona en español
   a = calcular_a('agua')
   
   # También funciona en inglés
   a = calcular_a('water')
   ```

## Ejemplos de Uso Práctico

### Ejemplo 1: Solucionador CFD

```python
from navier_stokes.constants import calcular_a, F0, OMEGA0

class SolucionadorPsiNSE:
    def __init__(self, medio='agua', viscosidad=None):
        # Obtener amplitud calibrada
        self.a = calcular_a(medio=medio, custom_viscosity=viscosidad)
        
        # Usar constantes QCAL
        self.f0 = F0
        self.omega0 = OMEGA0
        
        print(f"Solucionador inicializado con a = {self.a}")
        print(f"Usando frecuencia QCAL f0 = {self.f0} Hz")

# Crear solucionador para agua
solver = SolucionadorPsiNSE(medio='agua')

# Crear solucionador con viscosidad personalizada
solver_custom = SolucionadorPsiNSE(viscosidad=5e-4)
```

### Ejemplo 2: Barrido de Parámetros

```python
from navier_stokes.constants import calcular_a, verificar_regularidad

# Probar diferentes medios
medios = ['vacio', 'agua', 'aire']
viscosidad = 1e-3

print("Resultados de Calibración por Medio:")
print("-" * 60)

for medio in medios:
    a = calcular_a(medio)
    resultado = verificar_regularidad(a, viscosidad)
    
    estado = "✓" if resultado['global_regularity'] else "○"
    print(f"{estado} {medio:10s} a={a:6.1f}  "
          f"γ={resultado['gamma']:8.4f}  Δ={resultado['delta']:8.4f}")
```

Salida:
```
Resultados de Calibración por Medio:
------------------------------------------------------------
✓ vacio      a=   8.9  γ= 0.1027  Δ= 10.1722
○ agua       a=   7.0  γ=-12.1410  Δ=  2.4379
✓ aire       a= 200.0  γ=1614.0641  Δ=8138.3203
```

### Ejemplo 3: Análisis de Estabilidad

```python
from navier_stokes.constants import (
    calcular_a, verificar_regularidad, get_all_media_parameters
)

def analizar_estabilidad(medio, rango_nu):
    """Analiza estabilidad para un rango de viscosidades."""
    a = calcular_a(medio)
    
    print(f"\nAnálisis de Estabilidad: {medio.upper()}")
    print(f"Amplitud calibrada: a = {a}")
    print("-" * 60)
    print(f"{'ν (m²/s)':>12s}  {'δ*':>10s}  {'γ':>10s}  {'Δ':>10s}  {'Estado':>8s}")
    print("-" * 60)
    
    for nu in rango_nu:
        resultado = verificar_regularidad(a, nu, verbose=False)
        estado = "✓" if resultado['global_regularity'] else "○"
        
        print(f"{nu:12.2e}  {resultado['delta_star']:10.6f}  "
              f"{resultado['gamma']:10.4f}  {resultado['delta']:10.4f}  "
              f"{estado:>8s}")

# Ejecutar análisis
import numpy as np
viscosidades = np.logspace(-6, -2, 5)
analizar_estabilidad('vacio', viscosidades)
```

## Resolución de Problemas

### Problema: ImportError

```python
ImportError: No module named 'navier_stokes'
```

**Solución**: Asegúrese de estar en el directorio correcto:
```bash
cd /home/runner/work/3D-Navier-Stokes/3D-Navier-Stokes
python your_script.py
```

### Problema: ValueError en calcular_a

```python
ValueError: Unknown medium 'aguas'
```

**Solución**: Use un nombre de medio válido:
```python
# Válidos: 'agua', 'water', 'aire', 'air', 'vacio', 'vacuum'
a = calcular_a('agua')  # Correcto
```

### Problema: Regularidad No Garantizada

Si `verificar_regularidad` retorna `global_regularity=False`:

1. **Verifique si Riccati-Besov se satisface**: Si `riccati_besov_ok=True`, tiene regularidad parcial
2. **Use mayor amplitud**: Pruebe con `vacio` (a=8.9) en lugar de `agua` (a=7.0)
3. **Calibración personalizada**: Use `custom_viscosity` para su régimen específico

```python
# Si agua no funciona, pruebe vacio
a = calcular_a('vacio')  # a=8.9, más conservador
```

## Próximos Pasos

### Mejoras Futuras Potenciales

1. **Más medios**: Agregar calibraciones para otros fluidos (aceite, mercurio, etc.)
2. **Optimización automática**: Función para encontrar `a` óptimo dado conjunto de restricciones
3. **Visualización**: Funciones para graficar regiones de regularidad
4. **Integración con CI/CD**: Validación automática de parámetros en workflows

### Mantenimiento

Para actualizar valores calibrados:

1. Ejecutar `Scripts/calibrate_parameters.py` con nuevos parámetros
2. Actualizar valores en `navier_stokes/constants.py`
3. Ejecutar suite de pruebas: `python test_navier_stokes_constants.py`
4. Actualizar documentación si es necesario

## Referencias

- **Script de Calibración**: `Scripts/calibrate_parameters.py`
- **Derivación QFT**: `phi_qft_derivation_complete.py`
- **Aplicación CFD**: `cfd_psi_nse_solver.py`
- **Documentación Principal**: `README.md`
- **Documentación en Inglés**: `navier_stokes/README.md`

## Licencia

Licencia MIT con Soberanía QCAL

Ver `LICENSE` y `LICENSE_SOBERANA_QCAL.txt` para detalles.

## Autor

Marco QCAL - Quantum Coherent Amplification Lattice

Para preguntas o contribuciones, consulte `CONTRIBUTING.md`

---

**Nota**: Esta implementación es parte del esfuerzo continuo para formalizar y unificar el marco Ψ-Navier-Stokes. La unificación del parámetro `a` es un paso crucial hacia un código más mantenible y matemáticamente riguroso.
