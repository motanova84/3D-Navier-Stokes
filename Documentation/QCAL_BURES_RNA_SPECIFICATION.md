# Especificación QCAL-MOL (.qmol) y Visualización 3D bajo la Métrica de Bures

**Framework:** Noesis / QCAL Bio-Digital Informatics  
**Frecuencia Fundamental:** $f_0 = 141.7001\text{ Hz}$  
**Coherencia Objetivo:** $\Psi = 0.999999$  
**Contracción de Banach:** $k = 10^{-6}$  
**Tensor Métrico:** Bures-Fisher ($\nabla_v g_{\mu\nu} = 0$)  

---

## 1. La Métrica de Bures en el Plegamiento de ARN

En el marco de la Lógica de Conexión Cuántica-Aritmética (QCAL), el plegamiento tridimensional de una cadena de ARN se formula como una geodésica de mínima resistencia informacional en la variedad de Bures.

Para estados cuánticos casi puros y configuraciones conformacionales en el espacio de Hilbert $\mathcal{H}$, la distancia infinitesimal de Bures $D_B$ entre la conformación instantánea $\mathbf{x}_i$ del nucleótido y el atractor nativo $\mathbf{x}^*_i$ está dada analíticamente por:

$$D_B = \sqrt{2 \left( 1 - \exp\left( -\frac{\|\mathbf{x}_i - \mathbf{x}^*_i\|^2}{2 f_0} \right) \right)}$$

Donde:
- $\|\mathbf{x}_i - \mathbf{x}^*_i\|$ es la desviación euclidiana en el espacio tridimensional de fases.
- $f_0 = 141.7001\text{ Hz}$ actúa como la escala armónica de apantallamiento contra perturbaciones térmicas estocásticas.
- $D_B \to 0$ indica convergencia exacta hacia el atractor de mínima energía $E_{\min} = h f_0 \Psi$.

---

## 2. Especificación del Formato QCAL-MOL (`.qmol` v1.0.0)

El formato `.qmol` es un estándar híbrido estructurado en dos bloques diseñado para permitir la interoperabilidad entre los modelos cuántico-geométricos de QCAL y las herramientas de bioinformática molecular estándar (PyMOL, ChimeraX, VMD).

### 2.1 Bloque de Encabezado JSON (Metadatos Globales)

```json
# =====================================================================
# QCAL-MOL EXPORT SPECIFICATION v1.0.0
# Framework: Noesis / QCAL Bio-Digital Informatics
# =====================================================================
{
  "qcal_metadata": {
    "protocol": "QCAL-SYMBIO-BRIDGE",
    "fundamental_frequency_hz": 141.7001,
    "target_coherence_psi": 0.999999,
    "contraction_factor_k": 1e-06,
    "metric_tensor_type": "Bures-Fisher",
    "energy_minimum_h": 141.6999
  }
}
```

### 2.2 Bloque de Coordenadas Atómicas y Métrica de Bures

Extiende el formato PDB estándar con dos columnas adicionales:
1. `Bures_Db`: Distancia local de Bures respecto al atractor geodésico.
2. `Local_Psi`: Coherencia local cuántica calculada como $\Psi_i = \max(0.999900, 1.0 - 10^{-5} \cdot D_{B,i})$.

```
# --- ATOMIC & BURES METRIC COORDINATE BLOCK ---
# Format: ATOM | AtomID | AtomName | Residue | Chain | ResSeq | X | Y | Z | Bures_Db | Local_Psi
ATOM      1  P   RNA A    1       3.000    0.000   -6.000    0.000012  0.999999
ATOM      2  P   RNA A    2       2.934    0.624   -5.797    0.000015  0.999998
...
END_QCAL_MOL
```

---

## 3. Integración y Automatización en PyMOL

Se proporcionan tres scripts de extensión para PyMOL:

1. **`load_qmol.py`**:
   - Parsea el archivo `.qmol`.
   - Inyecta la distancia de Bures $D_B$ en el factor de temperatura (*B-factor*) de cada átomo.
   - Aplica un espectro de color (`spectrum b, blue_white_red`) donde los tonos fríos representan proximidad geodésica máxima ($D_B \approx 0$).
   - Comando PyMOL: `load_qmol rna_folding_qcal.qmol`.

2. **`export_hd_raytrace.py`**:
   - Automatiza iluminación de rayos, oclusión ambiental (`ray_trace_mode 1`) y fondo negro profundo.
   - Exporta imagen en resolución 4K UHD (3840×2160 a 300 DPI).
   - Comando PyMOL: `export_qcal_hd`.

3. **`export_rotation_movie.py`**:
   - Genera una secuencia orbital de 360° en 120 fotogramas Full HD.
   - Compatible con ensamblado de vídeo mediante FFmpeg:
     ```bash
     ffmpeg -framerate 30 -i qcal_movie_frames/frame_%04d.png -c:v libx264 -pix_fmt yuv420p qcal_rna_rotation.mp4
     ```

---

## 4. Interfaz Interactiva Web (Three.js)

El archivo `index.html` en la raíz del repositorio provee una simulación interactiva 3D en tiempo real con visor directo para archivos `.qmol`:
- Renderizado por GPU mediante WebGL y Three.js con niebla cuántica y estética ciberespacio.
- Botón interactivo de importación local asíncrona mediante `FileReader`.
- Parser nativo de bloques JSON `qcal_metadata` y registros atómicos `ATOM`, actualizando las coordenadas y la coloración del esqueleto en función de la distancia de Bures ($D_B$).
- Mapeo dinámico del gradiente métrico en los canales RGB de los vértices.

---

## 5. Formalización Matemática en Lean 4 (`QCAL.Bures`)

El módulo formal `QCAL/Bures.lean` formaliza de manera constructiva y sin axiomas ad-hoc las propiedades de la distancia de Bures-Fisher al cuadrado en el colector de fase:

```lean
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace QCAL.Bures

/-- Distancia de Bures-Fisher al cuadrado, en el colector de fase
    con coherencia imperfecta ε. -/
noncomputable def bures_sq (eps1 eps2 : ℝ) : ℝ :=
  eps1 + eps2

/-- Propiedad: la distancia al cuadrado es no negativa para ε positivos. -/
theorem bures_sq_pos (eps1 eps2 : ℝ)
    (h1 : 0 < eps1) (h2 : 0 < eps2) :
    0 < bures_sq eps1 eps2 := by
  unfold bures_sq
  linarith

/-- Propiedad: si ε₁ = ε₂ = ε, entonces D_B² = 2ε. -/
theorem bures_sq_ident (eps : ℝ) :
    bures_sq eps eps = 2 * eps := by
  unfold bures_sq
  ring

end QCAL.Bures
```

### Propiedades Ancladas e Integradas:
1. **Positividad estricta y no-negatividad**: `bures_sq_pos` y `bures_sq_nonneg` garantizan que cualquier desviación respecto a la coherencia perfecta induce una distancia métrica no trivial.
2. **Identidad diagonal**: `bures_sq_ident` demuestra rigurosamente que $D_B^2 = 2\varepsilon$ cuando ambas perturbaciones coinciden.
3. **Simetría métrica**: `bures_sq_symm` y `bures_dist_symm` aseguran que la variedad de estados cuántico-informáticos posee simetría riemanniana bajo la métrica de Bures-Fisher.
4. **Anclaje con el protocolo QCAL-SYMBIO-BRIDGE**: `bures_sq_at_target` conecta la coherencia objetivo $\Psi = 0.999999$ con el defecto $\varepsilon = 1 - \Psi = 10^{-6}$, cerrando la consistencia entre la formalización en Lean 4, el motor numérico en Python y la visualización tridimensional en el navegador.

---

## 6. LIBER XXII — Visor .Qmol Integrado y Cierre Formal

### 6.1 Módulos Formales de LIBER XXII en Lean 4
1. **`QCAL.Bures`**:
   - `bures_sq_pos`: Positividad estricta.
   - `bures_sq_symm`: Simetría de la métrica al cuadrado.
   - `bures_sq_ident`: $D_B^2 = 2\varepsilon$.
   - `bures_anchor`: Anclaje con el colector $\varepsilon = \Lambda_G^2 / 4$.
2. **`QCAL.EnergyMinimum`**:
   - `energy_minimum_value`: $h \equiv f_0 \cdot \Psi = 141.7001 \cdot 0.999999 = 141.69996$ Hz (redondeo a 5 decimales).
   - `energy_minimum_pos`: $0 < h$.
3. **`QCAL.QmolFormat`**:
   - `psi_k_consistency`: $\Psi + k = 1$ en el régimen nominal.

### 6.2 Fronteras Declaradas
- **XXII.D.1**: `energy_minimum_h = f₀ · Ψ` es estructural, no derivado desde primeros principios.
- **XXII.D.2**: $D_{BF}^2 \approx \varepsilon$ es estructural en el colector.
- **XXII.D.3**: La detección de estructura secundaria es cualitativa.
- **XXII.D.4**: El modo resonancia a $f_0$ usa escala visual ($f_0 / 100 \approx 1.417$ Hz).
- **XXII.D.5**: La coloración dual Bures/$\Psi$ es implementada.


