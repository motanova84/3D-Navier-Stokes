# Intelligent Executor - Parametric Sweep Optimization

Sistema inteligente para gestionar barridos paramétricos en simulaciones de Navier-Stokes con optimización dinámica de recursos.

## 📋 Características

### Detección Automática de Recursos
- **CPU**: Monitorea uso y cores disponibles
- **Memoria**: Detecta memoria RAM disponible
- **Disco**: Verifica espacio en disco disponible

### Priorización Inteligente
- **HIGH**: Números de Reynolds críticos (>1000), alta resolución (>128)
- **MEDIUM**: Rangos de parámetros estándar
- **LOW**: Configuraciones exploratorias o redundantes

### Estimación de Costos Computacionales
- **Tiempo**: Basado en resolución, timesteps y número de Reynolds
- **Memoria**: Proporcional a puntos de malla (resolución³)
- **Disco**: Incluye almacenamiento de salida y checkpoints

### Modos de Ejecución

#### 1. Modo Next (Siguiente)
Ejecuta el siguiente paquete óptimo basándose en prioridad y recursos disponibles.

```bash
python intelligent_executor.py --mode next
```

#### 2. Modo Continuo
Ejecuta paquetes continuamente hasta que se completen todos o se alcance el tiempo límite.

```bash
# Con límite de tiempo
python intelligent_executor.py --mode continuous --max-hours 24

# Sin límite de tiempo
python intelligent_executor.py --mode continuous
```

#### 3. Modo Oportunista
Ejecuta paquetes solo cuando el sistema está ocioso (uso CPU < umbral).

```bash
python intelligent_executor.py --mode opportunistic --cpu-threshold 70
```

## 🚀 Inicio Rápido

### 1. Instalar Dependencias

```bash
pip install -r requirements.txt
```

### 2. Ejecutar Demo

```bash
python demo_intelligent_executor.py
```

### 3. Crear Paquetes de Barrido Paramétrico

```python
from parametric_sweep_orchestrator import create_sample_packages

# Crear 10 paquetes de ejemplo
create_sample_packages(n_packages=10)
```

### 4. Ejecutar el Siguiente Paquete Óptimo

```python
from intelligent_executor import get_next_package_to_run
from parametric_sweep_orchestrator import run_package

# Seleccionar siguiente paquete
pkg_id, pkg_info = get_next_package_to_run()

if pkg_id is not None:
    # Ejecutar paquete
    result = run_package(pkg_id)
    print(f"Completado: {result['status']}")
```

## 📊 Estructura de Archivos

### Paquetes de Entrada
```
parametric_sweep_packages/
├── package_0000.json
├── package_0001.json
├── ...
└── priority_summary.json
```

#### Ejemplo de Paquete
```json
{
  "package_id": 0,
  "parameters": {
    "reynolds": 1000,
    "resolution": 64,
    "viscosity": 0.001,
    "timesteps": 1000,
    "domain_size": 1.0,
    "initial_condition": "taylor_green"
  },
  "metadata": {
    "created": "2025-11-02 08:00:00",
    "description": "Parameter sweep package 0"
  }
}
```

### Resultados de Salida
```
parametric_sweep_results/
├── results_package_0000.json
├── results_package_0001.json
└── ...
```

#### Ejemplo de Resultado
```json
{
  "package_id": 0,
  "status": "completed",
  "parameters": { ... },
  "execution_time": 123.45,
  "timestamp": "2025-11-02 08:15:30",
  "results": {
    "convergence": true,
    "final_error": 1.23e-06,
    "iterations": 1000
  }
}
```

## 🧪 Pruebas

```bash
# Ejecutar suite de pruebas
python test_intelligent_executor.py -v

# Ejecutar pruebas específicas
python -m unittest test_intelligent_executor.TestParametricSweepOrchestrator
python -m unittest test_intelligent_executor.TestIntelligentExecutor
```

## 📚 API Reference

### parametric_sweep_orchestrator.py

#### `load_package(package_id, packages_dir='parametric_sweep_packages')`
Carga un paquete desde disco.

#### `assign_priority(package)`
Asigna prioridad científica (HIGH/MEDIUM/LOW) basándose en parámetros.

#### `estimate_computational_cost(package)`
Estima tiempo, memoria y disco requeridos.

#### `run_package(package_id, output_dir='parametric_sweep_results')`
Ejecuta un paquete y guarda resultados.

#### `create_sample_packages(n_packages=10, output_dir='parametric_sweep_packages')`
Crea paquetes de ejemplo para pruebas.

### intelligent_executor.py

#### `get_available_resources()`
Detecta recursos computacionales disponibles.

#### `can_run_package(package_id, resources, packages_dir='parametric_sweep_packages')`
Determina si hay suficientes recursos para ejecutar un paquete.

#### `get_next_package_to_run(packages_dir, results_dir)`
Selecciona el siguiente paquete óptimo para ejecutar.

#### `run_continuous_mode(max_runtime_hours, check_interval_minutes, packages_dir, results_dir)`
Ejecuta paquetes continuamente.

#### `run_opportunistic_mode(target_cpu_usage, check_interval_seconds, packages_dir, results_dir)`
Ejecuta paquetes cuando el sistema está ocioso.

## 🔧 Configuración Avanzada

### Márgenes de Recursos
El sistema aplica márgenes de seguridad para evitar sobrecarga:
- **Memoria**: 20% margen adicional
- **Disco**: 50% margen adicional
- **CPU**: Requiere al menos 1 core libre

### Priorización Personalizada
Para modificar los criterios de prioridad, editar `assign_priority()` en `parametric_sweep_orchestrator.py`:

```python
def assign_priority(package: Dict[str, Any]) -> str:
    params = package.get('parameters', {})
    
    # Criterios personalizados
    if params.get('reynolds') > 5000:
        return 'HIGH'
    # ...
```

### Estimación de Costos Personalizada
Para ajustar la estimación de costos, modificar `estimate_computational_cost()`:

```python
def estimate_computational_cost(package: Dict[str, Any]) -> Dict[str, float]:
    # Factores de escala personalizados
    base_time = 0.2  # horas base
    memory_scaling = 1.5  # factor multiplicador
    # ...
```

## 📝 Notas

- Los paquetes completados se omiten automáticamente en ejecuciones subsecuentes
- El sistema verifica recursos antes de ejecutar cada paquete
- Los resultados incluyen timestamp para tracking
- Los directorios de paquetes y resultados se crean automáticamente

## 🐛 Solución de Problemas

### "No hay paquetes ejecutables"
- Verificar que existen paquetes en `parametric_sweep_packages/`
- Verificar que `priority_summary.json` existe
- Revisar que hay suficientes recursos del sistema

### Paquetes no se ejecutan
- Verificar requisitos de recursos (memoria, disco, CPU)
- Revisar logs para mensajes de error específicos
- Intentar con paquetes de menor resolución primero

### Tiempo de ejecución más largo de lo esperado
- Verificar parámetros de resolución y timesteps
- Considerar ejecutar en modo oportunista para menor interferencia
- Revisar que no hay otros procesos consumiendo recursos

## 📄 Licencia

Este código es parte del proyecto 3D Navier-Stokes Global Regularity Verification Framework.
