#!/usr/bin/env python3
"""
═══════════════════════════════════════════════════════════════
  EJECUTOR DE PAQUETE INDIVIDUAL
  
  Corre un paquete específico del barrido paramétrico.
  Uso: python run_package.py --package-id 0
═══════════════════════════════════════════════════════════════
"""

import argparse
from parametric_sweep_orchestrator import run_package, load_package, assign_priority, estimate_computational_cost
import sys

def main():
    parser = argparse.ArgumentParser(description='Ejecuta un paquete del barrido paramétrico')
    parser.add_argument('--package-id', type=int, required=True,
                       help='ID del paquete a ejecutar')
    parser.add_argument('--workers', type=int, default=None,
                       help='Número de workers paralelos (default: auto)')
    parser.add_argument('--output-dir', type=str, default='parametric_sweep_results',
                       help='Directorio para guardar resultados')
    parser.add_argument('--dry-run', action='store_true',
                       help='Solo mostrar información, no ejecutar')
    
    args = parser.parse_args()
    
    # Cargar y mostrar información del paquete
    try:
        package = load_package(args.package_id)
    except FileNotFoundError:
        print(f"❌ ERROR: Paquete {args.package_id} no encontrado")
        print(f"   Ejecuta primero: python parametric_sweep_orchestrator.py")
        sys.exit(1)
    
    priority = assign_priority(package)
    cost = estimate_computational_cost(package)
    
    print(f"\n{'='*70}")
    print(f"  PAQUETE {args.package_id}")
    print(f"{'='*70}")
    print(f"Tamaño:     {package['size']} simulaciones")
    print(f"Prioridad:  {priority}")
    print(f"Tiempo est: {cost['time_hours']:.2f} horas")
    print(f"Memoria:    {cost['memory_gb']:.2f} GB")
    print(f"Disco:      {cost['disk_gb']:.2f} GB")
    print(f"\nPrimeros parámetros:")
    for i, params in enumerate(package['parameters'][:3]):
        print(f"  {i+1}. f0={params['f0']:.1f} Hz, Re={params['Re']:.0f}, N={params['N']}")
    if package['size'] > 3:
        print(f"  ... y {package['size']-3} más")
    
    if args.dry_run:
        print(f"\n✅ DRY RUN - No se ejecutó nada")
        return
    
    # Confirmar ejecución
    response = input(f"\n¿Ejecutar este paquete? [y/N]: ")
    if response.lower() != 'y':
        print("❌ Cancelado")
        return
    
    # Ejecutar
    result = run_package(
        args.package_id,
        output_dir=args.output_dir,
        n_workers=args.workers
    )
    
    print(f"\n{'='*70}")
    print(f"  RESUMEN")
    print(f"{'='*70}")
    print(f"Éxitos:  {result['n_success']}/{package['size']}")
    print(f"Fallos:   {result['n_failed']}/{package['size']}")
    print(f"Tasa:     {100*result['n_success']/package['size']:.1f}%")

if __name__ == '__main__':
    main()
