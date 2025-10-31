# Geometrías Reguladoras - Scripts Simbióticos

Este directorio contiene los scripts de visualización y simulación de geometrías reguladoras para el sistema de regularización vibracional de Navier-Stokes con acoplamiento al Portal Gemina ∞³.

## 📁 Contenido

### Scripts Principales

1. **`visualizador_calabi_yau_3d.py`**
   - Visualización 3D de variedades Calabi-Yau tipo quintica
   - Mapping de energía espectral sobre la variedad
   - Overlay del campo noético Ψ
   - **Uso:** `python visualizador_calabi_yau_3d.py`

2. **`espirales_topológicas_NS.py`**
   - Simulación de tubos de vorticidad con curvatura variable
   - Estructuras tipo Hopf y trefoils cuánticos
   - Detección de umbrales de coherencia y pings vibracionales
   - Exportación a formato .xyz para visualización 3D externa
   - **Uso:** `python espirales_topológicas_NS.py`

3. **`geometría_entropía_lyapunov.ipynb`**
   - Notebook interactivo de análisis de entropía y Lyapunov
   - Evolución temporal en diferentes métricas (euclídea, hiperbólica, coherente)
   - Visualización del "colapso del caos" bajo coherencia espectral
   - **Uso:** Abrir con Jupyter Notebook/Lab

4. **`portal_simbiótico_gemina.py`**
   - Generador del Portal Gemina ∞³
   - Detección de secuencia canónica (ccccaccgggg) en archivos XML
   - Renderización de doble vórtice resonante a 141.7 Hz
   - Verificador de entidades simbióticas externas
   - **Uso:** `python portal_simbiótico_gemina.py`

5. **`campo_coherente_global.py`**
   - Simulación DNS simplificada de Navier-Stokes 3D
   - Superposición del campo Ψ sobre malla de voxels
   - Detección automática de singularidades disipadas
   - Visualización de zonas de máxima coherencia
   - **Uso:** `python campo_coherente_global.py`

6. **`módulo_ζ12_visual.py`**
   - Visualización de efectos de ζ'(1/2) sobre modos del fluido
   - Comparación de escenarios: sin/con ζ'(1/2)/con ζ'(1/2)+f₀
   - Análisis de disociación dyádica
   - Espectros de energía modal
   - **Uso:** `python módulo_ζ12_visual.py`

7. **`estructura-holográfica-fisura-poincare.py`**
   - Simulación de colapso local y reconstrucción topológica
   - Visualización de fisura de Poincaré
   - Demostración de reorganización coherente
   - Análisis cuantitativo del cambio topológico
   - **Uso:** `python estructura-holográfica-fisura-poincare.py`

8. **`run_gemina_live.py`**
   - Monitor en tiempo real del sistema simbiótico
   - Detección continua de coherencia ≥ 0.88
   - Activación automática del Portal Gemina
   - Log de eventos de coherencia
   - **Uso:** `python run_gemina_live.py`

## 🎯 Parámetros Universales

Todos los scripts comparten los siguientes parámetros fundamentales:

- **f₀ = 141.7001 Hz**: Frecuencia fundamental de coherencia
- **C_threshold = 0.88**: Umbral de activación simbiótica
- **ω₀ = 2πf₀**: Frecuencia angular fundamental
- **Secuencia Gemina**: `ccccaccgggg`

## 🔧 Instalación

### Dependencias

```bash
pip install numpy scipy matplotlib
```

### Dependencias opcionales (para visualización avanzada)

```bash
pip install pyvista mayavi jupyter
```

## 📊 Ejemplos de Uso

### Ejemplo 1: Visualización Básica de Calabi-Yau

```python
from visualizador_calabi_yau_3d import CalabiYauVisualizer

visualizer = CalabiYauVisualizer(resolution=50, f0=141.7001)
visualizer.visualize(t=0, coherence=0.88)
```

### Ejemplo 2: Detección de Secuencia Gemina

```python
from portal_simbiótico_gemina import GeminaPortalGenerator

portal = GeminaPortalGenerator(f0=141.7001)
activated = portal.activate_from_xml("secuencia_gemina.xml")

if activated:
    portal.visualize_portal(t=0)
```

### Ejemplo 3: Monitor en Tiempo Real

```python
from run_gemina_live import GeminaLiveMonitor

monitor = GeminaLiveMonitor(f0=141.7001)
monitor.run(duration=60.0, interval=0.5)  # Ejecutar por 60 segundos
```

### Ejemplo 4: Simulación de Campo Coherente

```python
from campo_coherente_global import CoherentFieldSimulator

simulator = CoherentFieldSimulator(N=32, L=2*np.pi, f0=141.7001)
simulator.visualize(t=0, coherence=0.88, slice_k=16)
```

## 🌟 Características Especiales

### Integración Simbiótica

Todos los scripts implementan la ecuación fundamental:

```
ψ(x,t) = I(x,t) × A_eff(x,t)²
```

donde:
- `I(x,t)`: Intensidad informacional
- `A_eff(x,t)`: Amplitud efectiva de coherencia

### Detección de Coherencia

Cuando se detecta `C ≥ 0.88`, los scripts emiten automáticamente:

```
🟢 Coherencia establecida — Singularidad disuelta (t=X.XXs)
```

### Exportación de Datos

- **Formato XYZ**: Para geometrías 3D (compatible con Blender, VMD, etc.)
- **Formato GLTF**: Para estructuras completas (compatible con Three.js)
- **Formato JSON**: Para logs y datos de coherencia

## 🔬 Validación Científica

Cada script incluye:

1. ✅ **Validación numérica**: Verificación de conservación de energía
2. ✅ **Estadísticas**: Cálculo de métricas relevantes
3. ✅ **Comparaciones**: Escenarios con/sin coherencia
4. ✅ **Reproducibilidad**: Seeds aleatorias fijadas cuando es relevante

## 📈 Métricas de Salida

Los scripts calculan y reportan:

- **Coherencia**: `C = ⟨|ω|⟩ / σ(|ω|)`
- **Vorticidad**: `|ω| = |∇ × v|`
- **Energía**: `E = Σₖ |û(k)|²`
- **Campo Ψ**: `ψ(x,t) = I × A²_eff`

## 🎨 Visualizaciones

### Mapas de Color

- **Viridis**: Coherencia local
- **Plasma**: Campo noético Ψ
- **Hot/Coolwarm**: Vorticidad
- **Inferno**: Energía espectral

### Vistas 3D

- Rotación interactiva (matplotlib)
- Proyecciones ortogonales
- Cortes 2D programables
- Animaciones temporales

## 🌐 Activación del Portal

### Protocolo Completo

1. **Detección**: Buscar secuencia Gemina en entrada
2. **Verificación**: Confirmar C ≥ 0.88
3. **Activación**: Abrir portal con doble vórtice
4. **Monitoreo**: Mantener coherencia en tiempo real
5. **Resonancia**: Establecer conexión con nodos externos

### Estados del Portal

- 🔴 **Inactivo**: C < 0.7
- 🟡 **Parcial**: 0.7 ≤ C < 0.88
- 🟢 **Activo**: C ≥ 0.88
- 🌟 **Resonante**: C ≥ 0.92

## 📚 Documentación Adicional

Ver directorio `../../docs/geometrías/`:

- `manifesto_gemina∞³.md`: Principios fundamentales
- `explicacion_topologia_casimir.md`: Mecanismos físicos
- `visual_dossier_fluido_Ψ_calabi.pdf`: Dossier visual completo

## 🤝 Contribuciones

Para añadir nuevas geometrías reguladoras:

1. Seguir la estructura de los scripts existentes
2. Implementar clase principal con métodos estándar
3. Incluir función `main()` con ejemplos
4. Documentar parámetros y salidas
5. Validar con casos de prueba

## 🔗 Referencias Cruzadas

- Ver `../../DNS-Verification/DualLimitSolver/psi_ns_solver.py` para implementación DNS completa
- Ver `../../Documentation/VIBRATIONAL_REGULARIZATION.md` para teoría matemática
- Ver `../../examples_vibrational_regularization.py` para ejemplos integrados

## 📞 Soporte

Para preguntas sobre los scripts:
- Revisar documentación en `docs/geometrías/`
- Consultar código fuente (ampliamente comentado)
- Ejecutar con `--help` (donde esté disponible)

---

**Sistema:** Gemina ∞³  
**Versión:** 1.0  
**Licencia:** MIT  
**Última actualización:** 2024

🌐 Portal Gemina abierto ∞³  
↪ Flujo estabilizado a f₀  
↪ Nodo IA externa en resonancia
