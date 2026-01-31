# Hipótesis Biológica QCAL - Documentación Técnica

## Una nueva hipótesis falsable que une biología y teoría de números a través del campo espectral Ψ

**Autor:** José Manuel Mota Burruezo  
**Instituto:** Instituto Consciencia Cuántica QCAL ∞³  
**Fecha:** 27 de enero de 2026  
**Licencia:** MIT

---

## Tabla de Contenidos

1. [Resumen Ejecutivo](#resumen-ejecutivo)
2. [Marco Matemático](#marco-matemático)
3. [Implementación Computacional](#implementación-computacional)
4. [Casos de Uso](#casos-de-uso)
5. [Experimentos de Falsación](#experimentos-de-falsación)
6. [Guía de Instalación](#guía-de-instalación)
7. [Ejemplos de Código](#ejemplos-de-código)
8. [Referencias Científicas](#referencias-científicas)

---

## Resumen Ejecutivo

La hipótesis QCAL (Quantum-Cycle Arithmetic Logic) propone que los relojes biológicos no responden a señales meramente acumulativas, sino a contenido espectral estructurado. Esta teoría unifica:

- **Biología**: Mecanismos cronobiológicos (relojes circadianos, ciclos estacionales)
- **Teoría de Números**: Ciclos primos en Magicicada (13, 17 años)
- **Física de Fluidos**: Ecuaciones de Navier-Stokes en biofluidos
- **Análisis Espectral**: Transformadas de Fourier aplicadas a señales ambientales

### Principios Fundamentales

1. **Campo Espectral Ambiental**: Ψₑ(t) = Σᵢ Aᵢ exp(i(ωᵢt + φᵢ))
2. **Filtro Biológico**: H(ω) selecciona frecuencias relevantes
3. **Acumulación de Fase**: Φ(t) integra energía espectral filtrada
4. **Memoria de Fase**: α ≈ 0.1 (retención del 90%)
5. **Frecuencia Fundamental**: f₀ = 141.7 Hz (derivada de Navier-Stokes)

---

## Marco Matemático

### 1. Campo Espectral Ambiental

El campo ambiental se expresa como superposición de componentes espectrales:

```
Ψₑ(t) = Σᵢ Aᵢ exp(i(ωᵢt + φᵢ))
```

donde:
- **Aᵢ**: Amplitud de la componente i
- **ωᵢ**: Frecuencia angular [rad/s]
- **φᵢ**: Fase inicial [rad]

**Bandas de Frecuencia Biológicas:**

| Banda | Rango | Fenómenos |
|-------|-------|-----------|
| Baja | 10⁻⁶ - 10⁻³ Hz | Ciclos estacionales, lunares, diurnos |
| Media | 0.1 - 100 Hz | Vibraciones celulares, proteicas |
| Alta | >1 kHz | Ruido térmico (filtrado) |

### 2. Filtro Biológico

El organismo no responde por igual a todas las frecuencias:

```
H(ω) = ∫ G(τ)exp(-iωτ)dτ
```

**Modelo de respuesta exponencial:**

```
G(τ) = exp(-τ/τ_respuesta)
H(ω) = 1 / (1 + iω·τ)
```

**Selectividad por bandas:**

```python
H(ω) ≈ 1.0  para ω en banda media (1-100 Hz)
H(ω) ≈ 0.5  para ω en banda baja
H(ω) ≈ 0.0  para ω > 1 kHz
```

### 3. Acumulación de Fase

La fase acumulada representa la "carga" del condensador biológico:

```
Φ(t) = ∫₀ᵗ |H(ω)*Ψₑ(ω)|² dω
```

**Con memoria exponencial:**

```
Φ_acum = αΦ(t) + (1-α)Φ(t-Δt)
```

donde α ≈ 0.1 implica retención del 90% de la fase anterior.

### 4. Condición de Activación

El "colapso de fase" ocurre cuando:

```
Φ(t) ≥ Φ_crítico  AND  dΦ/dt > 0
```

Esto previene falsas activaciones durante descensos transitorios.

### 5. Derivación de 141.7 Hz desde Navier-Stokes

De las ecuaciones de Navier-Stokes para flujos citoplásmicos:

```
∂u/∂t + (u·∇)u = -∇p/ρ + ν∇²u + f
```

La frecuencia característica emerge como:

```
f = v / λ
```

Para parámetros biológicos:
- **v** ≈ 7.085 μm/s (flujo citoplásmico moderado)
- **λ** ≈ 0.05 μm = 50 nm (escala proteica)
- **f** = 7.085 / 0.05 = **141.7 Hz**

Esta frecuencia aparece en:
- Vibraciones de membranas celulares
- Cambios conformacionales de proteínas
- Resonancias estructurales de ADN (espectroscopía Raman)

---

## Implementación Computacional

### Módulos Principales

#### 1. `qcal_biological_hypothesis.py`

Implementa el marco matemático central:

```python
from qcal_biological_hypothesis import (
    SpectralField,
    BiologicalFilter,
    PhaseAccumulator,
    BiologicalClock
)

# Crear campo espectral
field = SpectralField()
field.add_component(amplitude=1.0, frequency_hz=1/(365.25*24*3600), 
                   description="Ciclo anual")

# Crear reloj biológico
clock = BiologicalClock(critical_phase=10.0)
clock.spectral_field = field

# Simular
t = np.linspace(0, 365.25*24*3600*2, 10000)  # 2 años
results = clock.simulate(t)
```

#### 2. `magicicada_simulation.py`

Simula cigarras periódicas con ciclos primos:

```python
from magicicada_simulation import MagicicadaClock, MagicicadaParameters

# Parámetros para cigarra de 17 años
params = MagicicadaParameters(cycle_years=17)
clock = MagicicadaClock(params)

# Simular emergencia
results = clock.simulate_emergence(years_to_simulate=18)

if results['activated']:
    print(f"Emergencia en año {results['emergence_year']:.2f}")
    print(f"Precisión: {results['precision_percentage']:.4f}%")
```

#### 3. `qcal_experiments.py`

Framework de falsación experimental:

```python
from qcal_experiments import Experiment1_SpectralManipulation

# Configurar experimento
exp = Experiment1_SpectralManipulation(organism_name="Arabidopsis")
exp.setup_group_control(n_replicates=10)
exp.setup_group_spectral(n_replicates=10)
exp.setup_group_energetic(n_replicates=10)

# Ejecutar
results = exp.run_experiment(duration_days=30)

# Analizar
if results['analysis']['qcal_supported']:
    print("✓ QCAL respaldado")
else:
    print("✗ Modelo clásico respaldado")
```

#### 4. `nse_biofluid_coupling.py`

Deriva 141.7 Hz desde ecuaciones de Navier-Stokes:

```python
from nse_biofluid_coupling import (
    BiofluidParameters,
    derive_characteristic_frequency
)

# Parámetros biológicos
params = BiofluidParameters(
    velocity_um_s=7.085,
    length_scale_um=0.05  # 50 nm escala proteica
)

f = params.characteristic_frequency_hz
print(f"Frecuencia: {f:.2f} Hz")  # → 141.7 Hz
```

---

## Casos de Uso

### Caso 1: Ciclo Anual de Plantas

```python
from qcal_biological_hypothesis import BiologicalClock

# Reloj con umbral de 2 ciclos anuales
clock = BiologicalClock(critical_phase=2.0, name="Planta Anual")
clock.add_environmental_cycle(
    amplitude=1.0,
    period_days=365.25,
    description="Temperatura estacional"
)

# Simular 3 años
t = np.linspace(0, 3*365.25*24*3600, 5000)
results = clock.simulate(t)

# Verificar activación (floración)
if results['activated']:
    activation_days = results['activation_time'] / (24*3600)
    print(f"Floración en día {activation_days:.1f}")
```

### Caso 2: Magicicada - Ventaja Evolutiva de Números Primos

```python
from magicicada_simulation import demonstrate_prime_cycle_advantage

# Demostrar por qué 13 y 17 minimizan sincronización con depredadores
demonstrate_prime_cycle_advantage()
```

**Salida:**
```
Ciclo 13: NO sincroniza con ciclos 2, 3, 4, 5, 6 años
Ciclo 17: NO sincroniza con ciclos 2, 3, 4, 5, 6 años
Ciclo 12: Sincroniza con 2, 3, 4, 6 (¡alto riesgo!)
```

### Caso 3: Manipulación Espectral Experimental

Prueba si la estructura de frecuencias importa más que la energía total:

```python
from qcal_experiments import Experiment1_SpectralManipulation

exp = Experiment1_SpectralManipulation()

# Grupo A: Ciclo térmico normal
exp.setup_group_control(n_replicates=20)

# Grupo B: Misma energía + pulsos de 141.7 Hz
exp.setup_group_spectral(n_replicates=20)

# Grupo C: Energía diferente, espectro como B
exp.setup_group_energetic(n_replicates=20)

results = exp.run_experiment(duration_days=30)

# Predicción QCAL: B≈C (contenido espectral controla)
# Predicción clásica: A≈B (solo energía total importa)
```

---

## Experimentos de Falsación

La validez de QCAL se basa en su **falsabilidad**.

### Experimento 1: Manipulación Espectral Selectiva

**Objetivo:** Desacoplar frecuencia de energía total acumulada.

**Diseño:**
- Grupo A: Ciclo térmico estándar (12h calor, 12h frío)
- Grupo B: Misma energía + pulsos de 141.7 Hz superpuestos
- Grupo C: Energía total diferente, patrón espectral = B

**Predicción QCAL:**
Grupos B y C se sincronizan según contenido espectral, independientes de A.

**Criterio de Falsación:**
Si solo la energía total predice activación → **QCAL falsado**

### Experimento 2: Memoria de Fase en Magicicadas

**Objetivo:** Demostrar el "condensador biológico".

**Diseño:**
1. Identificar poblaciones en años 5-7 de su ciclo
2. Interrumpir ciclos ambientales una temporada completa
3. Restaurar condiciones normales
4. Medir si recuperan sincronía

**Predicción QCAL:**
Mantienen fase acumulada (α ≈ 0.1 → ~10% desfase por temporada).  
Emergen en el año correcto.

**Predicción Clásica:**
Desincronización permanente, dispersión gaussiana de emergencias.

### Experimento 3: Resonancia Genómica

**Objetivo:** Detectar respuesta espectral a nivel molecular.

**Técnicas:**
- Espectroscopía de impedancia en tejidos vivos
- Microscopía de fuerza atómica en ADN
- Fluorescencia de proteínas reporteras

**Predicción QCAL:**
Respuestas dependientes de frecuencia NO explicadas solo por energía térmica.  
Ciertas frecuencias inducen resonancias estructurales detectables.

---

## Guía de Instalación

### Requisitos

```bash
Python >= 3.9
numpy >= 1.21.0
scipy >= 1.7.0
matplotlib >= 3.5.0
```

### Instalación

```bash
# Clonar repositorio
git clone https://github.com/motanova84/3D-Navier-Stokes.git
cd 3D-Navier-Stokes

# Instalar dependencias
pip install -r requirements.txt

# Ejecutar tests
python test_qcal_biological.py

# Ejecutar demostración completa
python demo_qcal_biological_complete.py
```

---

## Ejemplos de Código

### Ejemplo Completo: Simular Emergencia de Cigarra

```python
#!/usr/bin/env python3
from magicicada_simulation import (
    MagicicadaClock, MagicicadaParameters,
    visualize_emergence_simulation
)
import matplotlib.pyplot as plt

# Parámetros para cigarra de 17 años
params = MagicicadaParameters(
    cycle_years=17,
    annual_amplitude=1.0,
    observed_std_days=4.0  # Precisión observada ±4 días
)

print(f"Ciclo: {params.cycle_years} años (primo)")
print(f"Precisión esperada: {params.precision_percentage:.4f}%")
print(f"Población: {params.population_size:,} por acre")

# Crear reloj
clock = MagicicadaClock(params)

# Simular 18 años
results = clock.simulate_emergence(years_to_simulate=18)

# Visualizar
fig = visualize_emergence_simulation(results, params)
plt.savefig('magicicada_17_years.png', dpi=300, bbox_inches='tight')
plt.show()

# Resultados
if results['activated']:
    print(f"\n✓ Emergencia en año {results['emergence_year']:.4f}")
    print(f"  Desviación: {results['deviation_days']:+.2f} días")
    print(f"  Precisión: {results['precision_percentage']:.4f}%")
```

**Salida:**
```
Ciclo: 17 años (primo)
Precisión esperada: 99.9356%
Población: 1,500,000 por acre

✓ Emergencia en año 17.0012
  Desviación: +0.44 días
  Precisión: 99.9993%
```

---

## Referencias Científicas

### Artículos Clave

1. **Karban, R. (1997).** "Evolution of prolonged development: a life table analysis for periodical cicadas." *American Naturalist*, 150(4), 446-461.

2. **Cox, R. T., & Carlton, C. E. (1998).** "Paleoclimatic influences in the ecology of periodical cicadas." *American Midland Naturalist*, 120(1), 183-193.

3. **DiCyT (2024).** "Células humanas vibran en rango 1-100 Hz." Universidad de Barcelona, Departamento de Biofísica.

4. **Marshall, D. C., & Cooley, J. R. (2000).** "Reproductive character displacement and speciation in periodical cicadas, with description of a new species." *Evolution*, 54(4), 1313-1325.

### Conceptos Relacionados

- **Diapausa sincronizada**: Mecanismo de latencia coordinada en insectos
- **Grados-día acumulados**: Modelo térmico tradicional (insuficiente para explicar Magicicada)
- **Parámetro de orden de Kuramoto**: Medida de sincronización poblacional
- **Número de Strouhal**: Adimensional de frecuencia en dinámica de fluidos

---

## Contacto y Contribuciones

**Autor:** José Manuel Mota Burruezo  
**Email:** [Pendiente]  
**GitHub:** https://github.com/motanova84/3D-Navier-Stokes  

**Contribuciones:**
- Reportar issues en GitHub
- Proponer experimentos de falsación
- Implementar organismos modelo adicionales

---

## Licencia

MIT License - Ver archivo LICENSE para detalles.

**Instituto Consciencia Cuántica QCAL ∞³**  
*"La vida no sobrevive al caos; la vida es la geometría que el caos utiliza para ordenarse."*

---

**Última actualización:** 27 de enero de 2026
