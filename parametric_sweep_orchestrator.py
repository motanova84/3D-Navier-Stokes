#!/usr/bin/env python3
"""
═══════════════════════════════════════════════════════════════
  ORQUESTADOR DE BARRIDO PARAMÉTRICO
  
  Maneja la ejecución distribuida de simulaciones paramétricas.
  Organiza paquetes, asigna prioridades y ejecuta en paralelo.
═══════════════════════════════════════════════════════════════
"""

import os
import json
import pickle
import numpy as np
from typing import Dict, List, Optional, Any
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor, as_completed
from datetime import datetime
import sys

# Add module paths for DNS verification
_current_dir = os.path.dirname(os.path.abspath(__file__))
_dns_module_dir = os.path.join(_current_dir, 'DNS-Verification', 'DualLimitSolver')
if _dns_module_dir not in sys.path:
    sys.path.insert(0, _dns_module_dir)

# Try to import simulation modules (may not be available in all environments)
try:
    from unified_bkm import (
        riccati_besov_closure,
        compute_optimal_dual_scaling,
        unified_bkm_verification
    )
    SIMULATION_MODULES_AVAILABLE = True
except ImportError:
    SIMULATION_MODULES_AVAILABLE = False

# Computational cost estimation constants
# These values can be adjusted based on benchmark results
BASE_TIME_MINUTES = 5.0  # Base time per simulation (minutes)
BASE_MEMORY_GB = 2.0     # Base memory per simulation (GB)
BASE_DISK_GB = 0.5       # Base disk per simulation (GB)
BASE_N_VALUE = 64        # Reference grid resolution
BASE_RE_VALUE = 1000     # Reference Reynolds number


def load_package(package_id: int, packages_dir: str = 'parametric_sweep_packages') -> Dict[str, Any]:
    """
    Carga un paquete desde disco
    
    Args:
        package_id: ID del paquete a cargar
        packages_dir: Directorio donde están los paquetes
        
    Returns:
        Dict con información del paquete
        
    Raises:
        FileNotFoundError: Si el paquete no existe
    """
    package_file = Path(packages_dir) / f'package_{package_id:04d}.json'
    
    if not package_file.exists():
        raise FileNotFoundError(f"Paquete {package_id} no encontrado en {packages_dir}")
    
    with open(package_file, 'r') as f:
        package = json.load(f)
    
    return package


def assign_priority(package: Dict[str, Any]) -> str:
    """
    Asigna prioridad a un paquete basado en sus parámetros
    
    Args:
        package: Diccionario con información del paquete
        
    Returns:
        String con nivel de prioridad: "HIGH", "MEDIUM", "LOW"
    """
    # Analizar parámetros para determinar prioridad
    params = package.get('parameters', [])
    if not params:
        return "LOW"
    
    # Extraer rangos de parámetros
    f0_values = [p.get('f0', 0) for p in params]
    Re_values = [p.get('Re', 0) for p in params]
    N_values = [p.get('N', 0) for p in params]
    
    # Prioridad ALTA: Regiones críticas
    # - Frecuencias cerca de f0 = 141.7 Hz (emergencia natural)
    # - Reynolds números altos (Re > 10000)
    # - Resoluciones altas (N > 128)
    high_priority_conditions = []
    
    # Verificar si hay valores cerca de la frecuencia crítica
    f0_near_critical = any(135 <= f0 <= 150 for f0 in f0_values)
    high_priority_conditions.append(f0_near_critical)
    
    # Verificar Reynolds altos
    Re_high = any(Re > 10000 for Re in Re_values)
    high_priority_conditions.append(Re_high)
    
    # Verificar resoluciones altas
    N_high = any(N > 128 for N in N_values)
    high_priority_conditions.append(N_high)
    
    if sum(high_priority_conditions) >= 2:
        return "HIGH"
    
    # Prioridad MEDIA: Condiciones intermedias
    medium_priority_conditions = []
    medium_priority_conditions.append(any(100 <= f0 <= 200 for f0 in f0_values))
    medium_priority_conditions.append(any(1000 <= Re <= 10000 for Re in Re_values))
    medium_priority_conditions.append(any(64 <= N <= 128 for N in N_values))
    
    if sum(medium_priority_conditions) >= 1:
        return "MEDIUM"
    
    return "LOW"


def estimate_computational_cost(package: Dict[str, Any]) -> Dict[str, float]:
    """
    Estima el costo computacional de un paquete
    
    Args:
        package: Diccionario con información del paquete
        
    Returns:
        Dict con estimaciones de tiempo, memoria y disco
    """
    params = package.get('parameters', [])
    n_simulations = len(params)
    
    # Estimaciones base por simulación (pueden ajustarse según benchmarks reales)
    # Estas constantes están definidas a nivel de módulo para facilitar ajustes
    
    # Ajustar según parámetros
    total_time_minutes = 0
    total_memory_gb = BASE_MEMORY_GB  # Memoria peak, no acumulativa
    total_disk_gb = 0
    
    for p in params:
        N = p.get('N', BASE_N_VALUE)
        Re = p.get('Re', BASE_RE_VALUE)
        
        # El tiempo escala con N^3 y log(Re)
        N_factor = (N / BASE_N_VALUE) ** 3
        Re_factor = np.log10(Re / BASE_RE_VALUE + 1) + 1
        
        sim_time = BASE_TIME_MINUTES * N_factor * Re_factor
        total_time_minutes += sim_time
        
        # La memoria escala con N^3
        sim_memory = BASE_MEMORY_GB * (N / BASE_N_VALUE) ** 3
        total_memory_gb = max(total_memory_gb, sim_memory)
        
        # El disco es acumulativo
        total_disk_gb += BASE_DISK_GB * (N / BASE_N_VALUE) ** 2
    
    return {
        'time_hours': total_time_minutes / 60.0,
        'time_minutes': total_time_minutes,
        'memory_gb': total_memory_gb,
        'disk_gb': total_disk_gb,
        'n_simulations': n_simulations
    }


def _run_single_simulation(params: Dict[str, Any], output_dir: str) -> Dict[str, Any]:
    """
    Ejecuta una simulación individual
    
    Args:
        params: Parámetros de la simulación
        output_dir: Directorio para guardar resultados
        
    Returns:
        Dict con resultados de la simulación
    """
    try:
        # Check if simulation modules are available
        if not SIMULATION_MODULES_AVAILABLE:
            raise ImportError("Simulation modules (unified_bkm) not available")
        
        # Extraer parámetros
        f0 = params.get('f0', 141.7)
        Re = params.get('Re', 5000)
        N = params.get('N', 64)
        nu = params.get('nu', 1e-3)
        M = params.get('M', 100.0)
        
        # Calcular parámetros derivados
        omega0 = 2 * np.pi * f0
        a = params.get('a', 2.45)
        alpha = params.get('alpha', 2.0)
        
        # Ejecutar verificación BKM
        results = unified_bkm_verification(
            a=a,
            alpha=alpha,
            omega0=omega0,
            nu=nu,
            M=M
        )
        
        # Calcular cierre de Riccati-Besov
        delta_star, Gamma = riccati_besov_closure(a, alpha, omega0, nu, M)
        
        # Añadir metadatos
        results['parameters'] = params
        results['timestamp'] = datetime.now().isoformat()
        results['success'] = True
        
        # Guardar resultados individuales
        output_file = Path(output_dir) / f"sim_f0_{f0:.1f}_Re_{Re:.0f}_N_{N}.json"
        output_file.parent.mkdir(parents=True, exist_ok=True)
        
        with open(output_file, 'w') as f:
            json.dump(results, f, indent=2)
        
        return results
        
    except Exception as e:
        return {
            'parameters': params,
            'success': False,
            'error': str(e),
            'timestamp': datetime.now().isoformat()
        }


def run_package(package_id: int, 
                output_dir: str = 'parametric_sweep_results',
                n_workers: Optional[int] = None,
                packages_dir: str = 'parametric_sweep_packages') -> Dict[str, Any]:
    """
    Ejecuta todas las simulaciones de un paquete en paralelo
    
    Args:
        package_id: ID del paquete a ejecutar
        output_dir: Directorio para guardar resultados
        n_workers: Número de workers paralelos (None = auto)
        packages_dir: Directorio donde están los paquetes
        
    Returns:
        Dict con resumen de la ejecución
    """
    # Cargar paquete
    package = load_package(package_id, packages_dir)
    params_list = package.get('parameters', [])
    
    # Crear directorio de salida
    package_output_dir = Path(output_dir) / f'package_{package_id:04d}'
    package_output_dir.mkdir(parents=True, exist_ok=True)
    
    # Determinar número de workers
    if n_workers is None:
        import multiprocessing
        n_workers = min(multiprocessing.cpu_count(), len(params_list))
    
    print(f"\n{'='*70}")
    print(f"  EJECUTANDO PAQUETE {package_id}")
    print(f"{'='*70}")
    print(f"Simulaciones: {len(params_list)}")
    print(f"Workers:      {n_workers}")
    print(f"Salida:       {package_output_dir}")
    print(f"{'='*70}\n")
    
    # Ejecutar simulaciones en paralelo
    results = []
    n_success = 0
    n_failed = 0
    
    start_time = datetime.now()
    
    with ProcessPoolExecutor(max_workers=n_workers) as executor:
        # Enviar todas las simulaciones
        futures = {
            executor.submit(_run_single_simulation, params, str(package_output_dir)): i
            for i, params in enumerate(params_list)
        }
        
        # Recoger resultados a medida que completan
        for future in as_completed(futures):
            sim_id = futures[future]
            try:
                result = future.result()
                results.append(result)
                
                if result.get('success', False):
                    n_success += 1
                    status = "✓"
                else:
                    n_failed += 1
                    status = "✗"
                
                # Mostrar progreso
                total = len(params_list)
                completed = n_success + n_failed
                progress = 100 * completed / total
                print(f"{status} [{completed}/{total}] ({progress:.1f}%) - Simulación {sim_id}")
                
            except Exception as e:
                n_failed += 1
                print(f"✗ Error en simulación {sim_id}: {e}")
                results.append({
                    'success': False,
                    'error': str(e),
                    'parameters': params_list[sim_id]
                })
    
    end_time = datetime.now()
    elapsed = (end_time - start_time).total_seconds()
    
    # Guardar resumen
    summary = {
        'package_id': package_id,
        'n_total': len(params_list),
        'n_success': n_success,
        'n_failed': n_failed,
        'elapsed_seconds': elapsed,
        'start_time': start_time.isoformat(),
        'end_time': end_time.isoformat(),
        'results': results
    }
    
    summary_file = package_output_dir / 'summary.json'
    with open(summary_file, 'w') as f:
        json.dump(summary, f, indent=2)
    
    print(f"\n{'='*70}")
    print(f"  PAQUETE {package_id} COMPLETADO")
    print(f"{'='*70}")
    print(f"Tiempo:  {elapsed/60:.1f} minutos")
    print(f"Resumen: {summary_file}")
    
    return summary


def create_example_packages(output_dir: str = 'parametric_sweep_packages', 
                           n_packages: int = 5,
                           sims_per_package: int = 10) -> List[int]:
    """
    Crea paquetes de ejemplo para demostración
    
    Args:
        output_dir: Directorio donde crear los paquetes
        n_packages: Número de paquetes a crear
        sims_per_package: Simulaciones por paquete
        
    Returns:
        Lista de IDs de paquetes creados
    """
    output_path = Path(output_dir)
    output_path.mkdir(parents=True, exist_ok=True)
    
    package_ids = []
    
    # Rangos de parámetros
    f0_range = np.logspace(np.log10(50), np.log10(500), n_packages * sims_per_package)
    Re_range = np.logspace(3, 5, n_packages * sims_per_package)
    N_values = [32, 64, 128]
    
    for pkg_id in range(n_packages):
        start_idx = pkg_id * sims_per_package
        end_idx = start_idx + sims_per_package
        
        parameters = []
        for i in range(start_idx, end_idx):
            params = {
                'f0': float(f0_range[i]),
                'Re': float(Re_range[i]),
                'N': int(N_values[i % len(N_values)]),
                'nu': 1e-3,
                'M': 100.0,
                'a': 2.45,
                'alpha': 2.0
            }
            parameters.append(params)
        
        package = {
            'id': pkg_id,
            'size': len(parameters),
            'parameters': parameters,
            'created': datetime.now().isoformat()
        }
        
        package_file = output_path / f'package_{pkg_id:04d}.json'
        with open(package_file, 'w') as f:
            json.dump(package, f, indent=2)
        
        package_ids.append(pkg_id)
    
    print(f"\n✓ Creados {n_packages} paquetes en {output_dir}/")
    return package_ids


if __name__ == '__main__':
    """Script de ejemplo para crear paquetes de prueba"""
    print("""
╔═══════════════════════════════════════════════════════════════════════╗
║                                                                       ║
║     ORQUESTADOR DE BARRIDO PARAMÉTRICO - Creación de Paquetes        ║
║                                                                       ║
╚═══════════════════════════════════════════════════════════════════════╝
    """)
    
    # Crear paquetes de ejemplo
    package_ids = create_example_packages(
        n_packages=5,
        sims_per_package=10
    )
    
    # Mostrar información de cada paquete
    print("\nPaquetes creados:")
    print("="*70)
    
    for pkg_id in package_ids:
        package = load_package(pkg_id)
        priority = assign_priority(package)
        cost = estimate_computational_cost(package)
        
        print(f"\nPaquete {pkg_id}:")
        print(f"  - Tamaño:     {package['size']} simulaciones")
        print(f"  - Prioridad:  {priority}")
        print(f"  - Tiempo est: {cost['time_hours']:.2f} horas")
        print(f"  - Memoria:    {cost['memory_gb']:.2f} GB")
        print(f"  - Disco:      {cost['disk_gb']:.2f} GB")
    
    print("\n" + "="*70)
    print("✓ Para ejecutar un paquete, usa:")
    print("  python run_package.py --package-id 0")
    print("="*70)
