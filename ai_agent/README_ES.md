# Agente IA para Navier-Stokes

Un asistente inteligente para analizar documentos matemáticos, extraer ecuaciones y generar scripts de ayuda para el marco de verificación 3D Navier-Stokes.

## Descripción General

Este agente IA ayuda a investigadores y desarrolladores a trabajar con el complejo marco matemático de las ecuaciones de Navier-Stokes mediante:

1. **Análisis de Documentos PDF**: Extrae ecuaciones y fórmulas matemáticas de archivos PDF
2. **Memoria Matemática**: Construye y mantiene una base de conocimientos de ecuaciones, constantes y teoremas
3. **Visualización**: Crea representaciones visuales de ecuaciones, relaciones y estructuras de prueba
4. **Generación de Scripts**: Genera automáticamente scripts de Python para verificación, simulación y análisis

## Características Principales

### 📄 Procesamiento de Documentos
- Extrae ecuaciones de documentos PDF usando PyPDF2
- Analiza archivos de documentación Markdown
- Categoriza ecuaciones por tipo (Navier-Stokes, vorticidad, criterio BKM, etc.)
- Identifica operadores matemáticos, normas, constantes y espacios funcionales

### 🧠 Memoria Matemática
- Almacena ecuaciones, constantes, teoremas y sus relaciones
- Soporta búsqueda y consulta de la base de conocimientos
- Exporta a formatos JSON y Markdown
- Mantiene contexto sobre el marco QCAL y la prueba de regularidad global

### 📊 Visualización
- Genera gráficos de red de ecuaciones mostrando relaciones
- Crea gráficos de distribución por categoría
- Visualiza el flujo de la estructura de prueba
- Produce informes resumidos comprensivos

### 🔧 Generación de Scripts
- **Scripts de Verificación**: Prueban propiedades matemáticas e inequaciones
- **Scripts de Simulación**: Plantillas de solucionador DNS 3D Navier-Stokes
- **Scripts de Análisis**: Post-procesan y analizan resultados de simulación
- **Scripts de Visualización**: Grafican campos de velocidad, vorticidad y espectros de energía

## Instalación

### Prerequisitos
```bash
# Se requiere Python 3.9 o superior
python --version
```

### Instalar Dependencias
```bash
pip install -r requirements.txt
```

Paquetes requeridos:
- `numpy>=1.21.0` - Cálculos numéricos
- `scipy>=1.7.0` - Computación científica
- `matplotlib>=3.5.0` - Visualización (opcional)
- `PyPDF2>=3.0.0` - Análisis de PDF (opcional)

## Inicio Rápido

### Uso Básico

```python
from ai_agent import NavierStokesAIAgent

# Inicializar el agente
agente = NavierStokesAIAgent(workspace_dir="mi_espacio_trabajo")

# Procesar documentación
agente.process_documentation("Documentation")

# Buscar temas específicos
agente.search_knowledge("BKM")
agente.search_knowledge("Riccati")

# Generar visualizaciones
agente.visualize_knowledge()

# Generar scripts de ayuda
agente.generate_scripts()

# Exportar base de conocimientos
agente.export_knowledge_base('markdown')
```

### Uso por Línea de Comandos

Ejecutar el script de ejemplo:
```bash
# Ejecutar ejemplos básicos
python run_ai_agent.py

# Ejecutar pipeline completo con todos los documentos
python run_ai_agent.py --full
```

## Arquitectura del Módulo

```
ai_agent/
├── __init__.py              # Inicialización del paquete
├── agent.py                 # Interfaz principal del agente IA
├── equation_parser.py       # Análisis de PDF y texto
├── math_memory.py           # Gestión de base de conocimientos
├── script_generator.py      # Generación de plantillas de scripts
└── visualizer.py           # Herramientas de visualización
```

### Componentes Principales

#### 1. EquationParser (Analizador de Ecuaciones)
Extrae y categoriza contenido matemático:

```python
from ai_agent import EquationParser

parser = EquationParser()

# Analizar documento PDF
resultados = parser.parse_pdf("ruta/al/documento.pdf")

# Analizar contenido de texto
with open("documento.md", 'r') as f:
    contenido = f.read()
resultados = parser.parse_text(contenido)

# Buscar ecuaciones
ecuaciones = parser.search_equations("vorticidad")

# Obtener resumen
resumen = parser.get_summary()
```

Categorías detectadas:
- `navier_stokes` - Ecuaciones de Navier-Stokes
- `vorticity` - Ecuaciones relacionadas con vorticidad
- `besov_spaces` - Inmersiones en espacios de Besov
- `riccati` - Desigualdades de Riccati
- `bkm_criterion` - Criterio BKM
- `energy_estimates` - Estimaciones de energía
- `constants` - Constantes matemáticas
- `inequalities` - Desigualdades generales

#### 2. MathematicalMemory (Memoria Matemática)
Almacena y organiza conocimiento matemático:

```python
from ai_agent import MathematicalMemory

memoria = MathematicalMemory(memory_file="conocimiento.json")

# Añadir ecuación
memoria.add_equation(
    name="Criterio BKM",
    formula="∫₀^T ‖ω(t)‖_{L∞} dt < ∞ ⇒ no hay explosión",
    description="Criterio de Beale-Kato-Majda",
    category="criterion"
)

# Añadir constante
memoria.add_constant(
    name="ν",
    description="Viscosidad cinemática",
    typical_value="1e-3",
    category="physical"
)

# Buscar
resultados = memoria.search("BKM")

# Obtener resumen
resumen = memoria.get_summary()

# Exportar
memoria.export_markdown("base_conocimiento.md")
```

#### 3. ScriptGenerator (Generador de Scripts)
Genera scripts de Python desde plantillas:

```python
from ai_agent import ScriptGenerator

generador = ScriptGenerator(output_dir="scripts")

# Generar script de verificación
generador.generate_verification_script(ecuaciones)

# Generar script de simulación
generador.generate_simulation_script(constantes)

# Generar script de análisis
generador.generate_analysis_script(memoria)

# Generar script de visualización
generador.generate_visualization_script(memoria)
```

#### 4. EquationVisualizer (Visualizador de Ecuaciones)
Crea representaciones visuales:

```python
from ai_agent import EquationVisualizer

visualizador = EquationVisualizer(output_dir="figuras")

# Visualizar red de ecuaciones
visualizador.visualize_equation_network(memoria)

# Visualizar distribución por categoría
visualizador.visualize_category_distribution(memoria)

# Visualizar estructura de prueba
visualizador.visualize_proof_structure(memoria)

# Crear informe resumen
visualizador.create_summary_report(memoria)
```

## Conocimiento Pre-cargado

El agente viene con conocimiento pre-inicializado sobre el marco Navier-Stokes:

### Constantes
- **ν** (nu): Viscosidad cinemática
- **C_BKM**: Constante de Calderón-Zygmund/Besov (2.0)
- **c_d**: Constante de Bernstein para d=3 (0.5)
- **δ*** (delta estrella): Parámetro de defecto de desalineación
- **c⋆** (c estrella): Coeficiente de coercitividad parabólica (1/16)
- **C_str**: Constante de estiramiento de vorticidad (32)
- **C_CZ**: Constante optimizada de Calderón-Zygmund (1.5)

### Ecuaciones Clave
- **Navier-Stokes**: ∂u/∂t + (u·∇)u = -∇p + ν∆u + f
- **Vorticidad**: ω = ∇ × u
- **Criterio BKM**: ∫₀^T ‖ω(t)‖_{L∞} dt < ∞ ⇒ no hay explosión
- **Desigualdad de Riccati**: d/dt X(t) ≤ A - B X(t) log(e + βX(t))
- **Estimación CZ-Besov**: ‖∇u‖_{L∞} ≤ C_CZ‖ω‖_{B⁰_{∞,1}}

## Ejemplos de Salida

### Scripts Generados

1. **verify_equations.py**: Marco de verificación
   - Verifica propiedades matemáticas
   - Valida desigualdades
   - Reporta estado aprobado/reprobado

2. **simulate_ns.py**: Simulador DNS
   - Solucionador pseudo-espectral
   - Inicialización de vórtice Taylor-Green
   - Seguimiento de energía y vorticidad

3. **analyze_results.py**: Herramientas de análisis
   - Análisis estadístico
   - Verificación del criterio BKM
   - Análisis de cascada de energía

4. **visualize_data.py**: Herramientas de visualización
   - Gráficos de campo de velocidad
   - Gráficos de campo de vorticidad
   - Análisis de espectro de energía

### Visualizaciones

- **equation_network.png**: Grafo mostrando relaciones entre ecuaciones
- **category_distribution.png**: Gráficos de barras de categorías de ecuaciones
- **proof_structure.png**: Diagrama de flujo de la estrategia de prueba
- **summary_report.png**: Resumen visual comprehensivo

### Exportaciones

- **knowledge_base.json**: Base de conocimiento legible por máquina
- **knowledge_base.md**: Documentación legible por humanos

## Uso Avanzado

### Flujos de Trabajo Personalizados

```python
from ai_agent import NavierStokesAIAgent

agente = NavierStokesAIAgent()

# Procesar PDFs específicos
archivos_pdf = [
    "Navier-Stokes Conjetura_ QCAL Coherencia Cuántica.pdf",
    "ENGLISH_Navier-Stokes Conjetura_ QCAL Coherencia Cuántica (1).pdf"
]

for pdf in archivos_pdf:
    agente.process_pdf_document(pdf)

# Añadir ecuaciones personalizadas
agente.memory.add_equation(
    name="Estimación Personalizada",
    formula="‖u‖_{L³} ≤ C‖ω‖_{B⁰_{∞,1}}",
    description="Control L³ vía Besov",
    category="estimate"
)

# Generar script personalizado
from ai_agent import ScriptGenerator

generador = ScriptGenerator()
ecuaciones = list(agente.memory.knowledge_base['equations'].values())
generador.generate_verification_script(
    ecuaciones,
    output_file="verificacion_personalizada.py"
)
```

### Procesamiento por Lotes

```python
from pathlib import Path
from ai_agent import NavierStokesAIAgent

agente = NavierStokesAIAgent()

# Procesar todos los PDFs en un directorio
directorio_pdf = Path(".")
for archivo_pdf in directorio_pdf.glob("*.pdf"):
    print(f"Procesando {archivo_pdf.name}...")
    agente.process_pdf_document(str(archivo_pdf))

# Procesar toda la documentación
for dir_doc in ["Documentation", "Lean4-Formalization", "DNS-Verification"]:
    if Path(dir_doc).exists():
        agente.process_documentation(dir_doc)

# Generar todas las salidas
agente.visualize_knowledge()
agente.generate_scripts()
agente.export_knowledge_base('markdown')
agente.export_knowledge_base('json')
```

## Integración con el Marco Existente

El agente IA se integra perfectamente con el marco de verificación existente de Navier-Stokes:

```python
from ai_agent import NavierStokesAIAgent
from verification_framework import FinalProof

# Usar agente para extraer ecuaciones
agente = NavierStokesAIAgent()
agente.process_documentation("Documentation")

# Obtener constantes de la memoria del agente
nu = float(agente.memory.get_constant("ν")['typical_value'].split()[0])

# Usar en el marco de verificación
prueba = FinalProof(ν=nu)
resultados = prueba.prove_global_regularity(T_max=100.0, X0=10.0, u0_L3_norm=1.0)

print(f"Regularidad global: {resultados['global_regularity']}")
```

## Resultados Demostrados

El agente ha procesado exitosamente la documentación del repositorio:

### Extracción de Ecuaciones
- **Total de ecuaciones extraídas**: 1,384
- **Documentos procesados**: 11 archivos
- **Categorías identificadas**: 5 (fundamental, criterion, estimate, general, physical)

### Scripts Generados
- `verify_equations.py` (1 MB) - 1,384 métodos de verificación
- `simulate_ns.py` (8 KB) - Simulador DNS completo con constantes pre-cargadas
- `analyze_results.py` (3 KB) - Herramientas de análisis
- `visualize_data.py` (5 KB) - Utilidades de visualización

### Base de Conocimientos
- **Formato JSON**: 480 KB de datos estructurados
- **Formato Markdown**: 240 KB de documentación legible

## Solución de Problemas

### Problemas con Análisis de PDF

Si falla el análisis de PDF:
```python
# El agente automáticamente recurre a archivos de documentación
# O procesar contenido de texto manualmente:
with open("documento.txt", 'r') as f:
    contenido = f.read()
resultados = agente.parser.parse_text(contenido, source="documento.txt")
```

### Dependencias Faltantes

```bash
# Instalar todas las dependencias
pip install numpy scipy matplotlib PyPDF2

# O instalar desde requirements
pip install -r requirements.txt
```

### Errores de Visualización

Si matplotlib no está disponible:
```python
# Saltar paso de visualización
agente.process_documentation("Documentation")
agente.generate_scripts()
# agente.visualize_knowledge()  # Saltar esto
agente.export_knowledge_base('markdown')
```

## Contribuir

El agente IA está diseñado para ser extensible:

1. **Añadir nuevas categorías**: Modificar categorías en `equation_parser.py`
2. **Añadir nuevas plantillas**: Extender plantillas en `script_generator.py`
3. **Añadir nuevas visualizaciones**: Añadir métodos a `visualizer.py`
4. **Mejorar análisis**: Mejorar patrones regex en `equation_parser.py`

## Licencia

Licencia MIT - Ver raíz del repositorio para detalles

## Referencias

Este agente está diseñado para trabajar con el marco matemático descrito en:
- Criterio BKM (Beale-Kato-Majda, 1984)
- Marco QCAL para 3D Navier-Stokes
- Enfoque unificado de verificación BKM-CZ-Besov
- Documentación del Problema del Milenio de Clay

## Contacto

Para problemas, preguntas o contribuciones, por favor use el rastreador de problemas del repositorio de GitHub.

---

## Comandos Útiles

```bash
# Ejecutar el agente con ejemplos básicos
python run_ai_agent.py

# Ejecutar pipeline completo procesando todos los PDFs
python run_ai_agent.py --full

# Verificar instalación
python -c "from ai_agent import NavierStokesAIAgent; print('¡Agente IA instalado correctamente!')"

# Listar contenido del espacio de trabajo
ls -la ai_agent_workspace/

# Ver ecuaciones extraídas en formato legible
cat ai_agent_workspace/knowledge_base.md | less

# Ejecutar un script generado
python ai_agent_workspace/generated_scripts/simulate_ns.py
```

## Características Futuras

El agente está en desarrollo activo. Características planificadas:

- [ ] Soporte para más formatos de documentos (LaTeX, Jupyter)
- [ ] Análisis semántico mejorado de ecuaciones
- [ ] Generación automática de pruebas unitarias
- [ ] Integración con solucionadores CAS (SymPy, Sage)
- [ ] Soporte para generación de código Lean4
- [ ] API REST para acceso remoto
- [ ] Interfaz web para visualización interactiva

## Agradecimientos

Este agente IA fue desarrollado como parte del marco de resolución del Problema del Milenio de Clay sobre las ecuaciones de Navier-Stokes. Agradecemos a la comunidad de investigadores que han contribuido al conocimiento matemático que este agente procesa y organiza.
