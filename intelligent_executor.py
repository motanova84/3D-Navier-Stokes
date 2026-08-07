"""
═══════════════════════════════════════════════════════════════
  EJECUTOR INTELIGENTE - OPTIMIZACIÓN DINÁMICA
  
  Selecciona automáticamente qué paquetes ejecutar basándose en:
  - Prioridad científica
  - Recursos disponibles
  - Resultados previos
  - Tiempo estimado
═══════════════════════════════════════════════════════════════
"""

import psutil
import json
import numpy as np
from pathlib import Path
from datetime import datetime, timedelta
from parametric_sweep_orchestrator import (
    load_package, 
    assign_priority, 
    estimate_computational_cost,
    run_package
)

# ═══════════════════════════════════════════════════════════════
# DETECCIÓN DE RECURSOS DISPONIBLES
# ═══════════════════════════════════════════════════════════════

def get_available_resources():
    """
    Detecta recursos computacionales disponibles.
    """
    cpu_count = psutil.cpu_count(logical=False)
    cpu_percent = psutil.cpu_percent(interval=1)
    
    memory = psutil.virtual_memory()
    memory_available_gb = memory.available / (1024**3)
    
    disk = psutil.disk_usage('/')
    disk_available_gb = disk.free / (1024**3)
    
    return {
        'cpu_cores': cpu_count,
        'cpu_usage': cpu_percent,
        'memory_available_gb': memory_available_gb,
        'disk_available_gb': disk_available_gb,
        'cpu_free_cores': int(cpu_count * (1 - cpu_percent/100))
    }

def can_run_package(package_id, resources, packages_dir='parametric_sweep_packages'):
    """
    Determina si hay suficientes recursos para ejecutar un paquete.
    """
    package = load_package(package_id, packages_dir)
    cost = estimate_computational_cost(package)
    
    checks = {
        'memory': resources['memory_available_gb'] >= cost['memory_gb'] * 1.2,  # 20% margen
        'disk': resources['disk_available_gb'] >= cost['disk_gb'] * 1.5,       # 50% margen
        'cpu': resources['cpu_free_cores'] >= 1
    }
    
    return all(checks.values()), checks

# ═══════════════════════════════════════════════════════════════
# SELECCIÓN INTELIGENTE DE PAQUETES
# ═══════════════════════════════════════════════════════════════

def get_next_package_to_run(packages_dir='parametric_sweep_packages',
                           results_dir='parametric_sweep_results'):
    """
    Selecciona el siguiente paquete óptimo para ejecutar.
    
    Criterios (en orden de importancia):
    1. Prioridad científica (HIGH > MEDIUM > LOW)
    2. No completado
    3. Recursos disponibles suficientes
    4. Menor tiempo estimado (para maximizar throughput)
    """
    
    # Cargar prioridades
    with open(f'{packages_dir}/priority_summary.json', 'r') as f:
        priorities = json.load(f)
    
    # Obtener recursos
    resources = get_available_resources()
    
    print(f"\n🔍 BUSCANDO PRÓXIMO PAQUETE ÓPTIMO")
    print(f"   Recursos disponibles:")
    print(f"     CPU:    {resources['cpu_free_cores']}/{resources['cpu_cores']} cores libres")
    print(f"     Memoria: {resources['memory_available_gb']:.1f} GB")
    print(f"     Disco:   {resources['disk_available_gb']:.1f} GB")
    
    # Iterar por prioridad
    for priority_level in ['HIGH', 'MEDIUM', 'LOW']:
        print(f"\n   Buscando en prioridad {priority_level}...")
        
        for pkg_info in priorities[priority_level]:
            pkg_id = pkg_info['package_id']
            
            # Verificar si ya está completado
            result_file = f"{results_dir}/results_package_{pkg_id:04d}.json"
            if Path(result_file).exists():
                continue
            
            # Verificar recursos
            can_run, checks = can_run_package(pkg_id, resources, packages_dir)
            
            if can_run:
                print(f"   ✅ Seleccionado: Paquete {pkg_id}")
                print(f"      Tiempo est: {pkg_info['estimated_time_hours']:.2f} h")
                print(f"      Memoria:    {pkg_info['estimated_memory_gb']:.2f} GB")
                return pkg_id, pkg_info
            else:
                failed_checks = [k for k, v in checks.items() if not v]
                print(f"   ⏭️  Paquete {pkg_id} omitido: recursos insuficientes ({', '.join(failed_checks)})")
    
    print(f"\n   ℹ️  No hay paquetes ejecutables con recursos actuales")
    return None, None

# ═══════════════════════════════════════════════════════════════
# MODO CONTINUO
# ═══════════════════════════════════════════════════════════════

def run_continuous_mode(max_runtime_hours=None, 
                       check_interval_minutes=5,
                       packages_dir='parametric_sweep_packages',
                       results_dir='parametric_sweep_results'):
    """
    Ejecuta paquetes continuamente hasta que:
    - Se completen todos los paquetes
    - Se alcance el tiempo máximo
    - No haya recursos disponibles
    """
    
    start_time = datetime.now()
    packages_completed = 0
    
    print("╔═══════════════════════════════════════════════════════════════╗")
    print("║  MODO CONTINUO - EJECUTOR INTELIGENTE                         ║")
    print("╚═══════════════════════════════════════════════════════════════╝")
    
    if max_runtime_hours:
        end_time = start_time + timedelta(hours=max_runtime_hours)
        print(f"⏱️  Tiempo máximo: {max_runtime_hours} horas")
        print(f"   Finaliza: {end_time.strftime('%Y-%m-%d %H:%M:%S')}")
    else:
        print(f"⏱️  Sin límite de tiempo")
    
    while True:
        # Verificar tiempo límite
        if max_runtime_hours and datetime.now() >= end_time:
            print(f"\n⏰ Tiempo máximo alcanzado")
            break
        
        # Buscar próximo paquete
        pkg_id, pkg_info = get_next_package_to_run(packages_dir, results_dir)
        
        if pkg_id is None:
            # No hay paquetes ejecutables
            print(f"\n⏸️  No hay paquetes ejecutables")
            print(f"   Esperando {check_interval_minutes} minutos antes de reintentar...")
            
            import time
            time.sleep(check_interval_minutes * 60)
            
            # Reintentar una vez
            pkg_id, pkg_info = get_next_package_to_run(packages_dir, results_dir)
            
            if pkg_id is None:
                print(f"\n✅ Todos los paquetes completados o sin recursos")
                break
        
        # Ejecutar paquete
        try:
            print(f"\n{'='*70}")
            print(f"  EJECUTANDO PAQUETE {pkg_id}")
            print(f"{'='*70}")
            
            result = run_package(pkg_id, output_dir=results_dir)
            
            packages_completed += 1
            
            print(f"\n✅ Paquete {pkg_id} completado")
            print(f"   Total completados en esta sesión: {packages_completed}")
            
        except Exception as e:
            print(f"\n❌ ERROR ejecutando paquete {pkg_id}: {e}")
            print(f"   Continuando con siguiente paquete...")
            continue
        
        # Pequeña pausa entre paquetes
        import time
        time.sleep(10)
    
    # Resumen final
    elapsed = datetime.now() - start_time
    
    print(f"\n╔═══════════════════════════════════════════════════════════════╗")
    print(f"║  RESUMEN FINAL - MODO CONTINUO                                ║")
    print(f"╚═══════════════════════════════════════════════════════════════╝")
    print(f"Duración:           {elapsed}")
    print(f"Paquetes completados: {packages_completed}")
    print(f"Promedio por paquete: {elapsed / packages_completed if packages_completed > 0 else timedelta(0)}")

# ═══════════════════════════════════════════════════════════════
# MODO OPORTUNISTA
# ═══════════════════════════════════════════════════════════════

def run_opportunistic_mode(target_cpu_usage=80, 
                          check_interval_seconds=30,
                          packages_dir='parametric_sweep_packages',
                          results_dir='parametric_sweep_results'):
    """
    Ejecuta paquetes cuando el sistema está ocioso (uso CPU < umbral).
    
    Ideal para ejecutar en background sin interrumpir otras tareas.
    """
    
    print("╔═══════════════════════════════════════════════════════════════╗")
    print("║  MODO OPORTUNISTA - EJECUCIÓN EN IDLE                         ║")
    print("╚═══════════════════════════════════════════════════════════════╝")
    print(f"⚙️  Umbral CPU: {target_cpu_usage}%")
    print(f"   (Ejecuta solo cuando uso < {target_cpu_usage}%)")
    
    packages_completed = 0
    
    import time
    
    while True:
        # Monitorear uso de CPU
        cpu_usage = psutil.cpu_percent(interval=1)
        
        if cpu_usage < target_cpu_usage:
            print(f"\n💤 Sistema ocioso (CPU: {cpu_usage:.1f}%)")
            
            # Intentar ejecutar paquete
            pkg_id, pkg_info = get_next_package_to_run(packages_dir, results_dir)
            
            if pkg_id is None:
                print(f"✅ Todos los paquetes completados")
                break
            
            try:
                print(f"🚀 Ejecutando paquete {pkg_id} oportunísticamente...")
                result = run_package(pkg_id, output_dir=results_dir, n_workers=1)
                packages_completed += 1
                
            except Exception as e:
                print(f"❌ Error: {e}")
        else:
            print(f"\r⏳ Sistema ocupado (CPU: {cpu_usage:.1f}%), esperando...", end='', flush=True)
        
        time.sleep(check_interval_seconds)
    
    print(f"\n✅ Modo oportunista finalizado")
    print(f"   Paquetes completados: {packages_completed}")

# ═══════════════════════════════════════════════════════════════
# CLI
# ═══════════════════════════════════════════════════════════════

if __name__ == '__main__':
    import argparse
    
    parser = argparse.ArgumentParser(description='Ejecutor inteligente de barrido paramétrico')
    parser.add_argument('--mode', choices=['next', 'continuous', 'opportunistic'],
                       default='next',
                       help='Modo de ejecución')
    parser.add_argument('--max-hours', type=float, default=None,
                       help='Tiempo máximo de ejecución (solo para modo continuo)')
    parser.add_argument('--cpu-threshold', type=float, default=80,
                       help='Umbral de uso CPU (solo para modo oportunista)')
    
    args = parser.parse_args()
    
    if args.mode == 'next':
        # Ejecutar solo el siguiente paquete óptimo
        pkg_id, pkg_info = get_next_package_to_run()
        
        if pkg_id is not None:
            result = run_package(pkg_id)
        else:
            print("❌ No hay paquetes ejecutables")
    
    elif args.mode == 'continuous':
        run_continuous_mode(max_runtime_hours=args.max_hours)
    
    elif args.mode == 'opportunistic':
        run_opportunistic_mode(target_cpu_usage=args.cpu_threshold)
