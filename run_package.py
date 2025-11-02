#!/usr/bin/env python3
"""
run_package.py

Script to execute an individual parametric sweep package.
Loads package configuration and runs the simulation.
"""

import argparse
import json
import sys
import time
from pathlib import Path
from datetime import datetime
import numpy as np

# Simulation result bounds (for placeholder simulation)
VELOCITY_MIN = 0.5
VELOCITY_MAX = 2.0
VORTICITY_MIN = 1.0
VORTICITY_MAX = 10.0
ENERGY_MIN = 0.1
ENERGY_MAX = 1.0
ENSTROPHY_MIN = 1.0
ENSTROPHY_MAX = 100.0
CONVERGENCE_PROBABILITY = 0.95


def load_package_config(packages_dir: Path, package_id: int) -> dict:
    """
    Load package configuration from JSON file.
    
    Args:
        packages_dir: Directory containing package configurations
        package_id: Unique identifier for the package
        
    Returns:
        Dictionary with package configuration parameters
        
    Raises:
        FileNotFoundError: If configuration file does not exist
    """
    config_file = packages_dir / f"package_{package_id:04d}.json"
    
    if not config_file.exists():
        raise FileNotFoundError(f"Archivo de configuración no encontrado: {config_file}")
    
    with open(config_file, 'r') as f:
        return json.load(f)


def simulate_navier_stokes(config: dict) -> dict:
    """
    Simular las ecuaciones de Navier-Stokes con los parámetros del paquete.
    
    Esta es una función placeholder que simula la ejecución.
    En producción, aquí se llamaría al solver real.
    """
    # Extraer parámetros
    reynolds = config.get('Re', 1000.0)
    dt = config.get('dt', 0.01)
    T_final = config.get('T_final', 1.0)
    grid_size = config.get('grid_size', [32, 32, 32])
    
    print(f"  Ejecutando simulación:")
    print(f"    Reynolds:    {reynolds}")
    print(f"    dt:          {dt}")
    print(f"    T_final:     {T_final}")
    print(f"    Grid:        {grid_size}")
    
    # Simular trabajo computacional
    n_steps = int(T_final / dt)
    for i in range(min(n_steps, 10)):  # Simular solo unos pasos para demo
        time.sleep(0.1)  # Simular computación
        if (i + 1) % 5 == 0:
            print(f"    Paso {i+1}/{n_steps}")
    
    # Generar resultados simulados
    results = {
        'success': True,
        'n_steps': int(n_steps),
        'final_time': float(T_final),
        'max_velocity': float(np.random.uniform(VELOCITY_MIN, VELOCITY_MAX)),
        'max_vorticity': float(np.random.uniform(VORTICITY_MIN, VORTICITY_MAX)),
        'energy': float(np.random.uniform(ENERGY_MIN, ENERGY_MAX)),
        'enstrophy': float(np.random.uniform(ENSTROPHY_MIN, ENSTROPHY_MAX)),
        'convergence': bool(np.random.choice([True, False], p=[CONVERGENCE_PROBABILITY, 1-CONVERGENCE_PROBABILITY])),
        'execution_time': float(n_steps * dt * 0.1)
    }
    
    return results


def run_package(package_id: int, packages_dir: Path, output_dir: Path) -> dict:
    """Ejecutar un paquete completo."""
    print(f"\n{'='*60}")
    print(f"PAQUETE {package_id:04d}")
    print(f"{'='*60}")
    
    start_time = time.time()
    
    # Cargar configuración
    print(f"\n[1/3] Cargando configuración...")
    config = load_package_config(packages_dir, package_id)
    print(f"  ✓ Configuración cargada: {len(config)} parámetros")
    
    # Ejecutar simulación
    print(f"\n[2/3] Ejecutando simulación...")
    results = simulate_navier_stokes(config)
    
    # Guardar resultados
    print(f"\n[3/3] Guardando resultados...")
    execution_time = time.time() - start_time
    
    output_data = {
        'package_id': package_id,
        'timestamp': datetime.now().isoformat(),
        'config': config,
        'results': results,
        'execution_time': execution_time,
        'status': 'completed' if results['success'] else 'failed'
    }
    
    output_file = output_dir / f"results_package_{package_id:04d}.json"
    with open(output_file, 'w') as f:
        json.dump(output_data, f, indent=2)
    
    print(f"  ✓ Resultados guardados en: {output_file}")
    print(f"\n{'='*60}")
    print(f"PAQUETE {package_id:04d} COMPLETADO")
    print(f"Tiempo de ejecución: {execution_time:.2f}s")
    print(f"Estado: {'✅ ÉXITO' if results['success'] else '❌ FALLO'}")
    print(f"{'='*60}\n")
    
    return output_data


def main():
    """Función principal."""
    parser = argparse.ArgumentParser(
        description='Ejecutar un paquete individual del barrido paramétrico'
    )
    parser.add_argument(
        '--package-id',
        type=int,
        required=True,
        help='ID del paquete a ejecutar'
    )
    parser.add_argument(
        '--packages-dir',
        type=Path,
        default=Path('parametric_sweep_packages'),
        help='Directorio con las configuraciones de paquetes'
    )
    parser.add_argument(
        '--output-dir',
        type=Path,
        default=Path('parametric_sweep_results'),
        help='Directorio para guardar resultados'
    )
    
    args = parser.parse_args()
    
    # Crear directorio de salida si no existe
    args.output_dir.mkdir(parents=True, exist_ok=True)
    
    try:
        # Ejecutar paquete
        result = run_package(args.package_id, args.packages_dir, args.output_dir)
        
        # Código de salida basado en el éxito
        if result['status'] == 'completed':
            sys.exit(0)
        else:
            sys.exit(1)
            
    except FileNotFoundError as e:
        print(f"❌ ERROR: {e}", file=sys.stderr)
        sys.exit(2)
    except Exception as e:
        print(f"❌ ERROR INESPERADO: {e}", file=sys.stderr)
        import traceback
        traceback.print_exc()
        sys.exit(3)


if __name__ == '__main__':
    main()
