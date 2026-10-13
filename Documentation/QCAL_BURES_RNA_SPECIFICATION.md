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

El archivo `index.html` en la raíz del repositorio provee una simulación interactiva 3D en tiempo real:
- Renderizado por GPU mediante WebGL y Three.js.
- Sliders en vivo para modular la frecuencia fundamental $f_0$ (50–300 Hz) y el nivel de perturbación térmica exógena.
- Representación dinámica de la contracción de Banach ($k = 10^{-6}$) y coloración en gradiente de Bures.
