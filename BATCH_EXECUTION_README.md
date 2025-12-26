# Batch Execution System for Parametric Sweeps

Sistema de ejecución por lotes para barridos paramétricos de las ecuaciones de Navier-Stokes.

## Descripción

Este sistema permite ejecutar múltiples simulaciones con diferentes parámetros de forma secuencial o paralela, con gestión de prioridades y seguimiento del progreso.

## Componentes

### 1. `batch_execution.sh`

Script principal que coordina la ejecución de paquetes.

**Características:**
- Ejecución secuencial o paralela
- Gestión de prioridades (HIGH, MEDIUM, LOW, ALL)
- Reinicio automático (salta paquetes ya completados)
- Timeouts configurables
- Logging detallado
- Reporte de progreso

**Uso:**

```bash
# Ejecución secuencial de todos los paquetes
./batch_execution.sh

# Ejecución paralela (4 procesos simultáneos por defecto)
./batch_execution.sh --mode parallel

# Solo paquetes de alta prioridad
./batch_execution.sh --priority HIGH

# Ejecución paralela con más procesos
./batch_execution.sh --mode parallel --max-parallel 8

# Detener en caso de error
./batch_execution.sh --stop-on-error
```

**Opciones:**
- `--mode sequential|parallel`: Modo de ejecución (default: sequential)
- `--priority HIGH|MEDIUM|LOW|ALL`: Filtrar por prioridad (default: ALL)
- `--max-parallel N`: Número máximo de procesos paralelos (default: 4)
- `--stop-on-error`: Detener ejecución si un paquete falla

### 2. `run_package.py`

Script para ejecutar un paquete individual.

**Uso:**

```bash
python3 run_package.py --package-id 1
python3 run_package.py --package-id 5 --output-dir custom_results/
```

**Argumentos:**
- `--package-id`: ID del paquete a ejecutar (requerido)
- `--packages-dir`: Directorio con configuraciones (default: parametric_sweep_packages)
- `--output-dir`: Directorio para resultados (default: parametric_sweep_results)

### 3. `parametric_sweep_monitor.py`

Script para monitorear el progreso y generar reportes.

**Uso:**

```bash
python3 parametric_sweep_monitor.py
```

**Salida:**
- Resumen en consola con estadísticas
- Gráfico de progreso en `artifacts/parametric_sweep_progress.png`

## Estructura de Directorios

```
.
├── parametric_sweep_packages/     # Configuraciones de entrada
│   ├── priority_summary.json      # Resumen de prioridades
│   ├── package_0001.json          # Configuración paquete 1
│   ├── package_0002.json          # Configuración paquete 2
│   └── ...
├── parametric_sweep_results/      # Resultados de simulaciones
│   ├── results_package_0001.json  # Resultados paquete 1
│   ├── results_package_0002.json  # Resultados paquete 2
│   └── ...
├── parametric_sweep_logs/         # Logs de ejecución
│   ├── batch.log                  # Log principal
│   ├── package_0001.log           # Log detallado paquete 1
│   ├── package_0002.log           # Log detallado paquete 2
│   ├── parallel.log               # Log de GNU parallel (si aplica)
│   └── ...
└── artifacts/
    └── parametric_sweep_progress.png  # Reporte visual
```

## Formato de Configuración

### priority_summary.json

```json
{
  "HIGH": [
    {
      "package_id": 1,
      "priority": "HIGH",
      "description": "Critical Reynolds number sweep",
      "parameters": {
        "Re": [100, 500, 1000],
        "grid_size": [[64, 64, 64]]
      }
    }
  ],
  "MEDIUM": [...],
  "LOW": [...]
}
```

### package_XXXX.json

```json
{
  "package_id": 1,
  "Re": 1000,
  "dt": 0.01,
  "T_final": 1.0,
  "grid_size": [64, 64, 64],
  "priority": "HIGH"
}
```

## Formato de Resultados

### results_package_XXXX.json

```json
{
  "package_id": 1,
  "timestamp": "2025-11-02T10:00:00",
  "config": {...},
  "results": {
    "success": true,
    "n_steps": 100,
    "final_time": 1.0,
    "max_velocity": 1.23,
    "max_vorticity": 4.56,
    "energy": 0.78,
    "enstrophy": 12.34,
    "convergence": true,
    "execution_time": 45.6
  },
  "execution_time": 45.6,
  "status": "completed"
}
```

## Workflow Típico

1. **Preparar paquetes:**
   ```bash
   # Crear configuraciones de paquetes
   # Editar parametric_sweep_packages/priority_summary.json
   # Crear archivos package_XXXX.json
   ```

2. **Ejecutar batch:**
   ```bash
   # Primero los de alta prioridad
   ./batch_execution.sh --priority HIGH
   
   # Luego el resto en paralelo
   ./batch_execution.sh --mode parallel --priority MEDIUM
   ./batch_execution.sh --mode parallel --priority LOW
   ```

3. **Monitorear progreso:**
   ```bash
   # Durante la ejecución o después
   python3 parametric_sweep_monitor.py
   ```

4. **Reintentar fallos:**
   ```bash
   # El script salta automáticamente paquetes completados
   ./batch_execution.sh --priority HIGH
   ```

## Características Avanzadas

### Ejecución Paralela

El script intenta usar GNU `parallel` si está disponible. Si no, usa un sistema de backgrounding manual.

**Instalar GNU parallel (opcional pero recomendado):**
```bash
# Ubuntu/Debian
sudo apt-get install parallel

# macOS
brew install parallel
```

### Reinicio Automático

El sistema detecta automáticamente paquetes ya completados y los salta, permitiendo reiniciar después de interrupciones.

### Timeouts

Cada paquete tiene un timeout de 24 horas (configurable en el script). Si se excede, el proceso se termina y se marca como fallido.

### Logging Detallado

- **batch.log**: Log principal con timestamps
- **package_XXXX.log**: Salida completa de cada paquete
- **parallel.log**: Información de GNU parallel (si se usa)

## Ejemplos de Uso

### Ejemplo 1: Ejecución Rápida de Prototipos

```bash
# Solo paquetes de alta prioridad, secuencial
./batch_execution.sh --priority HIGH
```

### Ejemplo 2: Producción Completa

```bash
# Todos los paquetes en paralelo con 8 procesos
./batch_execution.sh --mode parallel --max-parallel 8
```

### Ejemplo 3: Procesamiento por Etapas

```bash
# Etapa 1: Alta prioridad primero
./batch_execution.sh --priority HIGH

# Etapa 2: Media prioridad en paralelo
./batch_execution.sh --mode parallel --priority MEDIUM

# Etapa 3: Baja prioridad durante la noche
nohup ./batch_execution.sh --mode parallel --priority LOW &
```

### Ejemplo 4: Debugging

```bash
# Ejecutar un solo paquete manualmente
python3 run_package.py --package-id 1

# Ver progreso
python3 parametric_sweep_monitor.py
```

## Troubleshooting

### "GNU parallel no disponible"

**Solución:** Instalar GNU parallel o aceptar el fallback a backgrounding manual.

### "Archivo de configuración no encontrado"

**Solución:** Verificar que existan:
- `parametric_sweep_packages/priority_summary.json`
- `parametric_sweep_packages/package_XXXX.json`

### Paquetes que fallan consistentemente

**Diagnóstico:**
```bash
# Ver log detallado
cat parametric_sweep_logs/package_0001.log

# Ejecutar manualmente para debugging
python3 run_package.py --package-id 1
```

### División por cero en bc

**Causa:** Todos los paquetes fallaron o no hay paquetes procesados.

**Solución:** Verificar logs y reintentar paquetes fallidos.

## Integración con CI/CD

```yaml
# .github/workflows/parametric-sweep.yml
name: Parametric Sweep

on:
  workflow_dispatch:
    inputs:
      priority:
        description: 'Priority level'
        required: true
        default: 'HIGH'

jobs:
  sweep:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - name: Run batch
        run: |
          chmod +x batch_execution.sh
          ./batch_execution.sh --priority ${{ github.event.inputs.priority }}
      - name: Upload results
        uses: actions/upload-artifact@v2
        with:
          name: sweep-results
          path: parametric_sweep_results/
```

## Dependencias

**Requeridas:**
- Python 3.7+
- bash
- GNU coreutils (timeout, bc)

**Opcionales:**
- GNU parallel (para mejor paralelización)
- matplotlib (para reportes visuales)
- numpy (para análisis numérico)

**Instalar dependencias Python:**
```bash
pip install matplotlib numpy
```

## Licencia

MIT - Ver LICENSE en el repositorio principal.
