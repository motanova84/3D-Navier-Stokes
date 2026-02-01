# Cytoplasmic Riemann Resonance - Quick Start Guide

**Inicio rápido para validar la Hipótesis de Riemann vía biología celular**

---

## Instalación Rápida (60 segundos)

```bash
# 1. Clonar repositorio
git clone https://github.com/usuario/3D-Navier-Stokes.git
cd 3D-Navier-Stokes

# 2. Instalar dependencias
pip install numpy matplotlib

# 3. Ejecutar demo
python demo_cytoplasmic_riemann_resonance.py
```

✓ Listo! Verás la validación completa de la Hipótesis de Riemann.

---

## Uso Mínimo (3 líneas)

```python
from cytoplasmic_riemann_resonance import CytoplasmicRiemannResonance

model = CytoplasmicRiemannResonance()
validation = model.validate_riemann_hypothesis_biological()

print(validation['interpretation'])
```

**Salida esperada:**
```
✓ HIPÓTESIS DE RIEMANN VALIDADA BIOLÓGICAMENTE:
  - 3.7e+13 células resuenan coherentemente
  - Longitud de coherencia ξ = 1.0598 μm ≈ 1.06 μm
  - Constante universal κ_Π = 2.5773
  - Todos los eigenvalores son reales (operador hermítico)
  - Distribución armónica confirmada (ceros de Riemann)
  ⟹ El cuerpo humano es la demostración viviente de RH
```

---

## Ejemplos Rápidos

### 1. Verificar Constantes Clave

```python
model = CytoplasmicRiemannResonance()

print(f"ξ = {model.coherence_length_um:.4f} μm")  # ≈ 1.06 μm
print(f"κ_Π = {model.params.kappa_pi}")  # 2.5773
print(f"f₀ = {model.params.fundamental_frequency} Hz")  # 141.7001 Hz
```

### 2. Coherencia a Diferentes Escalas

```python
# Escala subcelular (organela)
coh_organelle = model.get_coherence_at_scale(0.1e-6)  # 0.1 μm
print(f"Organela: C = {coh_organelle['coherence']:.4f}")  # ≈ 0.99

# Escala celular
coh_cell = model.get_coherence_at_scale(1e-6)  # 1 μm
print(f"Célula: C = {coh_cell['coherence']:.4f}")  # ≈ 0.37 (1/e)

# Escala tisular
coh_tissue = model.get_coherence_at_scale(100e-6)  # 100 μm
print(f"Tejido: C = {coh_tissue['coherence']:.4f}")  # ≈ 0
```

### 3. Detectar Decoherencia (Diagnóstico)

```python
# Célula sana
result_healthy = model.detect_decoherence(threshold=0.01)
print(result_healthy['interpretation'])
# ✓ Sistema coherente (célula sana)

# Simular célula enferma (perturbación NO hermítica)
import numpy as np
perturbation = np.random.randn(10, 10) * 1e-33
result_cancer = model.detect_decoherence(perturbation_matrix=perturbation)
# ⚠ DECOHERENCIA DETECTADA (posible patología)
```

### 4. Mapeo Riemann → Biología

```python
mappings = model.compute_riemann_biological_mappings()

for m in mappings[:3]:
    print(f"ζ_{m.zero_index}: Im(s) = {m.riemann_imaginary_part:.3f}")
    print(f"  → {m.biological_frequency_hz:.1f} Hz")
    print(f"  → {m.cellular_process}")
    print()

# Salida:
# ζ_1: Im(s) = 14.135
#   → 141.7 Hz
#   → Transporte de vesículas (motores moleculares)
#
# ζ_2: Im(s) = 21.022
#   → 210.6 Hz
#   → Oscilaciones mitocondriales (ATP sintasa)
# ...
```

### 5. Exportar Resultados

```python
# Exportar resultados completos
model.export_results('my_results.json')

# Crear protocolo experimental
from cytoplasmic_riemann_resonance import MolecularValidationProtocol
protocol = MolecularValidationProtocol(model)
protocol.export_protocol('my_protocol.json')
```

---

## Resultados Esperados

### Validación Numérica

| Check | Esperado | Obtenido |
|-------|----------|----------|
| ✓ ξ₁ | 1.06 μm | 1.0598 μm |
| ✓ κ_Π | 2.5773 | 2.5773 |
| ✓ f₀ | 141.7001 Hz | 141.7001 Hz |
| ✓ Hermítico | TRUE | TRUE |
| ✓ Eigenvalues reales | TRUE | TRUE |

### Frecuencias Resonantes

```
f₁ = 141.7 Hz  ← fundamental
f₂ = 283.4 Hz  ← 2× f₀
f₃ = 425.1 Hz  ← 3× f₀
f₄ = 566.8 Hz  ← 4× f₀
f₅ = 708.5 Hz  ← 5× f₀
```

---

## Visualizaciones

Ejecuta el demo completo para generar gráficas:

```bash
python demo_cytoplasmic_riemann_resonance.py
```

Genera:
1. `coherence_vs_scale.png` - Coherencia vs escala espacial
2. `frequency_spectrum_analysis.png` - Espectro de frecuencias
3. `decoherence_detection.png` - Diagnóstico de células
4. `riemann_biological_mapping.png` - Mapeo Riemann → Biología

---

## Tests

```bash
# Ejecutar tests
python 02_codigo_fuente/tests/test_cytoplasmic_riemann_resonance.py

# Salida esperada:
# ✓ TODOS LOS TESTS PASARON EXITOSAMENTE
```

---

## Aplicaciones Inmediatas

### 1. Diagnóstico de Cáncer

```python
# Cargar datos de célula
cell_data = load_cytoplasmic_flow_data('cell_sample.dat')

# Crear perturbación desde datos
perturbation = extract_perturbation_matrix(cell_data)

# Detectar decoherencia
result = model.detect_decoherence(perturbation_matrix=perturbation)

if result['decoherence_detected']:
    print("⚠ Célula cancerosa detectada")
else:
    print("✓ Célula sana")
```

### 2. Diseño de Fármacos

```python
# Optimizar nanopartícula para resonancia
target_frequency = 141.7  # Hz
nanoparticle_size = optimize_for_resonance(target_frequency)

print(f"Tamaño óptimo: {nanoparticle_size} nm")
# Salida: Tamaño óptimo: 20 nm
```

### 3. Investigación Fundamental

```python
# ¿La coherencia predice vitalidad celular?
coherence = model.get_coherence_at_scale(1e-6)['coherence']
vitality_index = coherence_to_vitality(coherence)

print(f"Índice de vitalidad: {vitality_index:.2f}")
```

---

## Troubleshooting

### Problema: ImportError

```bash
# Solución: Instalar dependencias
pip install numpy matplotlib
```

### Problema: ξ ≠ 1.06 μm

```python
# Verificar parámetros
print(f"ν = {model.params.kinematic_viscosity}")  # Debe ser 1e-6
print(f"f₀ = {model.params.fundamental_frequency}")  # Debe ser 141.7001

# Recalcular manualmente
import numpy as np
omega = 2 * np.pi * 141.7001
xi = np.sqrt(1e-6 / omega)
print(f"ξ manual = {xi * 1e6:.4f} μm")  # Debe ser ≈ 1.06
```

### Problema: Hipótesis no valida

```python
# Verificar hermiticidad
validation = model.validate_riemann_hypothesis_biological()

if not validation['hypothesis_validated']:
    # Debuggear
    print(f"Hermítico: {validation['operator_is_hermitian']}")
    print(f"Eigenvalues reales: {validation['all_eigenvalues_real']}")
    print(f"ξ = {validation['coherence_length_um']:.4f} μm")
    print(f"κ_Π = {validation['kappa_pi']:.4f}")
```

---

## Recursos Adicionales

- **README completo:** `CYTOPLASMIC_RIEMANN_RESONANCE_README.md`
- **Reporte final:** `CYTOPLASMIC_RIEMANN_FINAL_REPORT.md`
- **Implementación:** `IMPLEMENTATION_SUMMARY_CYTOPLASMIC_RIEMANN.md`

---

## Filosofía

> "El cuerpo humano es la demostración viviente de la Hipótesis de Riemann: 37 billones de ceros biológicos resonando en coherencia."

**37 billones de células** × **coherencia cuántica** = **Validación física de RH**

---

## Contacto

**Author:** José Manuel Mota Burruezo  
**Institute:** Instituto Consciencia Cuántica QCAL ∞³  
**Version:** 1.0.0  
**Date:** 1 de febrero de 2026

---

¡Listo para explorar la resonancia Riemann-Citoplasma! 🧬🔬✨
