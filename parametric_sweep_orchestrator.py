#!/usr/bin/env python3
"""
═══════════════════════════════════════════════════════════════
  ORQUESTADOR DE BARRIDO PARAMÉTRICO - ESTRATEGIA MODULAR
  
  Divide el espacio de parámetros en paquetes ejecutables
  independientemente para maximizar eficiencia computacional.
═══════════════════════════════════════════════════════════════
"""

import numpy as np
import json
import os
from datetime import datetime
from pathlib import Path
import multiprocessing as mp

# ═══════════════════════════════════════════════════════════════
# DEFINICIÓN DEL ESPACIO DE PARÁMETROS
# ═══════════════════════════════════════════════════════════════

PARAMETER_SPACE = {
    'f0': {
        'min': 100.0,
        'max': 1000.0,
        'num_points': 20,  # Reducido para paquetes manejables
        'scale': 'log'     # Escala logarítmica
    },
    'Re': {
        'min': 100.0,
        'max': 1000.0,
        'num_points': 15,
        'scale': 'log'
    },
    'N': {
        'options': [32, 64, 128],  # Resoluciones disponibles
        'default': 64
    },
    'T_max': {
        'default': 10.0,  # Tiempo de simulación (segundos)
    },
    'nu': {
        'compute_from_Re': True  # ν = U*L/Re
    }
}

# ═══════════════════════════════════════════════════════════════
# DIVISIÓN EN PAQUETES
# ═══════════════════════════════════════════════════════════════

def create_parameter_packages(package_size=10):
    """
    Divide el espacio completo en paquetes manejables.
    
    Args:
        package_size: Número de simulaciones por paquete
    
    Returns:
        List[dict]: Lista de paquetes con sus parámetros
    """
    
    # Generar grid completo
    if PARAMETER_SPACE['f0']['scale'] == 'log':
        f0_values = np.logspace(
            np.log10(PARAMETER_SPACE['f0']['min']),
            np.log10(PARAMETER_SPACE['f0']['max']),
            PARAMETER_SPACE['f0']['num_points']
        )
    else:
        f0_values = np.linspace(
            PARAMETER_SPACE['f0']['min'],
            PARAMETER_SPACE['f0']['max'],
            PARAMETER_SPACE['f0']['num_points']
        )
    
    if PARAMETER_SPACE['Re']['scale'] == 'log':
        Re_values = np.logspace(
            np.log10(PARAMETER_SPACE['Re']['min']),
            np.log10(PARAMETER_SPACE['Re']['max']),
            PARAMETER_SPACE['Re']['num_points']
        )
    else:
        Re_values = np.linspace(
            PARAMETER_SPACE['Re']['min'],
            PARAMETER_SPACE['Re']['max'],
            PARAMETER_SPACE['Re']['num_points']
        )
    
    N_values = PARAMETER_SPACE['N']['options']
    
    # Crear lista de todas las combinaciones
    all_params = []
    for f0 in f0_values:
        for Re in Re_values:
            for N in N_values:
                # Calcular ν desde Re
                U_char = 1.0  # Velocidad característica
                L_char = 2*np.pi  # Longitud característica
                nu = U_char * L_char / Re
                
                all_params.append({
                    'f0': float(f0),
                    'Re': float(Re),
                    'nu': float(nu),
                    'N': int(N),
                    'T_max': PARAMETER_SPACE['T_max']['default'],
                    'L': L_char,
                    'U': U_char
                })
    
    # Dividir en paquetes
    packages = []
    for i in range(0, len(all_params), package_size):
        package = {
            'id': i // package_size,
            'size': min(package_size, len(all_params) - i),
            'parameters': all_params[i:i+package_size],
            'status': 'pending',
            'created_at': datetime.now().isoformat()
        }
        packages.append(package)
    
    print(f"✅ Creados {len(packages)} paquetes")
    print(f"   Total de simulaciones: {len(all_params)}")
    print(f"   Tamaño promedio de paquete: {package_size}")
    
    return packages

# ═══════════════════════════════════════════════════════════════
# ESTIMACIÓN DE RECURSOS
# ═══════════════════════════════════════════════════════════════

def estimate_computational_cost(package):
    """
    Estima el costo computacional de un paquete.
    
    Returns:
        dict: Estimaciones de tiempo, memoria, disco
    """
    
    cost = {
        'time_hours': 0.0,
        'memory_gb': 0.0,
        'disk_gb': 0.0,
        'cpu_cores': 1
    }
    
    for params in package['parameters']:
        N = params['N']
        T_max = params['T_max']
        
        # Tiempo de simulación (heurística basada en N³)
        # Asumiendo ~1 ms por paso temporal por punto de grid
        dt = 0.001  # CFL-limited
        n_steps = int(T_max / dt)
        ops_per_step = N**3 * np.log2(N)  # FFT cost
        total_ops = ops_per_step * n_steps
        
        # Asumiendo 1 GFlop/s por core
        time_seconds = total_ops / 1e9
        time_hours = time_seconds / 3600
        
        # Memoria (double precision, 4 campos: u_x, u_y, u_z, p)
        memory_gb = 4 * N**3 * 8 / 1e9
        
        # Disco (guardar cada 0.1s)
        n_snapshots = int(T_max / 0.1)
        disk_gb = n_snapshots * memory_gb
        
        cost['time_hours'] += time_hours
        cost['memory_gb'] = max(cost['memory_gb'], memory_gb)
        cost['disk_gb'] += disk_gb
    
    return cost

# ═══════════════════════════════════════════════════════════════
# CLASIFICACIÓN DE PRIORIDAD
# ═══════════════════════════════════════════════════════════════

def assign_priority(package):
    """
    Asigna prioridad basada en importancia científica.
    
    Prioridad ALTA:
    - f0 ≈ 141.7 Hz (frecuencia predicha)
    - Re moderado (100-500)
    - Resolución media-alta (N=64, 128)
    
    Prioridad MEDIA:
    - f0 alejado pero dentro del rango
    - Re extremo (muy bajo o muy alto)
    
    Prioridad BAJA:
    - Exploración de esquinas del espacio paramétrico
    """
    
    priority_score = 0
    
    for params in package['parameters']:
        score = 0
        
        # Factor f0 (máxima prioridad cerca de 141.7 Hz)
        f0_target = 141.7
        f0_distance = abs(params['f0'] - f0_target) / f0_target
        score += 10 * np.exp(-5 * f0_distance)  # Gaussiana centrada
        
        # Factor Re (prioridad en rango moderado)
        if 100 <= params['Re'] <= 500:
            score += 5
        elif 500 < params['Re'] <= 1000:
            score += 3
        else:
            score += 1
        
        # Factor resolución
        if params['N'] == 64:
            score += 3  # Óptimo
        elif params['N'] == 128:
            score += 4  # Mejor resolución
        else:
            score += 1  # N=32
        
        priority_score += score
    
    priority_score /= len(package['parameters'])
    
    if priority_score > 15:
        return 'HIGH'
    elif priority_score > 10:
        return 'MEDIUM'
    else:
        return 'LOW'

# ═══════════════════════════════════════════════════════════════
# GUARDADO Y CARGA DE PAQUETES
# ═══════════════════════════════════════════════════════════════

def save_packages(packages, output_dir='parametric_sweep_packages'):
    """
    Guarda paquetes en archivos JSON individuales.
    """
    Path(output_dir).mkdir(parents=True, exist_ok=True)
    
    # Guardar metadata
    metadata = {
        'total_packages': len(packages),
        'total_simulations': sum(p['size'] for p in packages),
        'created_at': datetime.now().isoformat(),
        'parameter_space': PARAMETER_SPACE
    }
    
    with open(f'{output_dir}/metadata.json', 'w') as f:
        json.dump(metadata, f, indent=2)
    
    # Guardar cada paquete
    for pkg in packages:
        pkg_file = f"{output_dir}/package_{pkg['id']:04d}.json"
        with open(pkg_file, 'w') as f:
            json.dump(pkg, f, indent=2)
    
    # Guardar resumen de prioridades
    priority_summary = {
        'HIGH': [],
        'MEDIUM': [],
        'LOW': []
    }
    
    for pkg in packages:
        priority = assign_priority(pkg)
        cost = estimate_computational_cost(pkg)
        
        priority_summary[priority].append({
            'package_id': pkg['id'],
            'size': pkg['size'],
            'estimated_time_hours': cost['time_hours'],
            'estimated_memory_gb': cost['memory_gb']
        })
    
    with open(f'{output_dir}/priority_summary.json', 'w') as f:
        json.dump(priority_summary, f, indent=2)
    
    print(f"\n✅ Paquetes guardados en: {output_dir}/")
    print(f"   📊 Resumen de prioridades:")
    print(f"      HIGH:   {len(priority_summary['HIGH'])} paquetes")
    print(f"      MEDIUM: {len(priority_summary['MEDIUM'])} paquetes")
    print(f"      LOW:    {len(priority_summary['LOW'])} paquetes")
    
    return output_dir

def load_package(package_id, input_dir='parametric_sweep_packages'):
    """
    Carga un paquete específico.
    """
    pkg_file = f"{input_dir}/package_{package_id:04d}.json"
    
    if not os.path.exists(pkg_file):
        raise FileNotFoundError(f"Paquete {package_id} no encontrado")
    
    with open(pkg_file, 'r') as f:
        package = json.load(f)
    
    return package

# ═══════════════════════════════════════════════════════════════
# EJECUCIÓN DE UN PAQUETE
# ═══════════════════════════════════════════════════════════════

def run_single_simulation(params):
    """
    Ejecuta una simulación individual con parámetros dados.
    
    Esta función será implementada en el siguiente script.
    Por ahora, retorna estructura de resultado esperada.
    """
    from psi_nse_dns_complete import run_psi_nse_simulation
    
    try:
        result = run_psi_nse_simulation(
            N=params['N'],
            L=params['L'],
            T=params['T_max'],
            nu=params['nu'],
            f0=params['f0'],
            dt=0.001,
            save_interval=0.1,
            verbose=False
        )
        
        return {
            'status': 'success',
            'params': params,
            'results': result,
            'completed_at': datetime.now().isoformat()
        }
    
    except Exception as e:
        return {
            'status': 'failed',
            'params': params,
            'error': str(e),
            'completed_at': datetime.now().isoformat()
        }

def run_package(package_id, output_dir='parametric_sweep_results', 
                n_workers=None):
    """
    Ejecuta todas las simulaciones de un paquete en paralelo.
    
    Args:
        package_id: ID del paquete a ejecutar
        output_dir: Directorio para guardar resultados
        n_workers: Número de workers paralelos (None = auto)
    """
    
    # Cargar paquete
    package = load_package(package_id)
    
    print(f"\n🚀 EJECUTANDO PAQUETE {package_id}")
    print(f"   Tamaño: {package['size']} simulaciones")
    
    # Estimar recursos
    cost = estimate_computational_cost(package)
    print(f"\n📊 ESTIMACIÓN DE RECURSOS:")
    print(f"   Tiempo:  {cost['time_hours']:.2f} horas")
    print(f"   Memoria: {cost['memory_gb']:.2f} GB")
    print(f"   Disco:   {cost['disk_gb']:.2f} GB")
    
    # Configurar paralelización
    if n_workers is None:
        n_workers = min(mp.cpu_count(), package['size'])
    
    print(f"\n⚙️  Usando {n_workers} workers paralelos")
    
    # Ejecutar simulaciones en paralelo
    Path(output_dir).mkdir(parents=True, exist_ok=True)
    
    with mp.Pool(n_workers) as pool:
        results = pool.map(run_single_simulation, package['parameters'])
    
    # Guardar resultados
    package_result = {
        'package_id': package_id,
        'completed_at': datetime.now().isoformat(),
        'n_success': sum(1 for r in results if r['status'] == 'success'),
        'n_failed': sum(1 for r in results if r['status'] == 'failed'),
        'results': results
    }
    
    result_file = f"{output_dir}/results_package_{package_id:04d}.json"
    with open(result_file, 'w') as f:
        json.dump(package_result, f, indent=2)
    
    print(f"\n✅ PAQUETE {package_id} COMPLETADO")
    print(f"   Éxitos: {package_result['n_success']}")
    print(f"   Fallos:  {package_result['n_failed']}")
    print(f"   Resultados guardados en: {result_file}")
    
    return package_result

# ═══════════════════════════════════════════════════════════════
# MAIN: GENERACIÓN DE PAQUETES
# ═══════════════════════════════════════════════════════════════

if __name__ == '__main__':
    print("╔═══════════════════════════════════════════════════════════════╗")
    print("║  ORQUESTADOR DE BARRIDO PARAMÉTRICO - GENERACIÓN DE PAQUETES ║")
    print("╚═══════════════════════════════════════════════════════════════╝")
    
    # Crear paquetes
    packages = create_parameter_packages(package_size=10)
    
    # Calcular y mostrar estadísticas
    total_cost = {'time_hours': 0, 'memory_gb': 0, 'disk_gb': 0}
    
    for pkg in packages:
        cost = estimate_computational_cost(pkg)
        total_cost['time_hours'] += cost['time_hours']
        total_cost['memory_gb'] = max(total_cost['memory_gb'], cost['memory_gb'])
        total_cost['disk_gb'] += cost['disk_gb']
    
    print(f"\n📊 ESTIMACIÓN TOTAL:")
    print(f"   Tiempo:  {total_cost['time_hours']:.2f} horas ({total_cost['time_hours']/24:.1f} días)")
    print(f"   Memoria: {total_cost['memory_gb']:.2f} GB (pico)")
    print(f"   Disco:   {total_cost['disk_gb']:.2f} GB (total)")
    
    # Guardar paquetes
    output_dir = save_packages(packages)
    
    print(f"\n✅ GENERACIÓN COMPLETADA")
    print(f"\n📋 PRÓXIMOS PASOS:")
    print(f"   1. Revisar prioridades: cat {output_dir}/priority_summary.json")
    print(f"   2. Ejecutar paquete de alta prioridad:")
    print(f"      python parametric_sweep_orchestrator.py --run <package_id>")
    print(f"   3. Monitorear progreso:")
    print(f"      python parametric_sweep_monitor.py")
