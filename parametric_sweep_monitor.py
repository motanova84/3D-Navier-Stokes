#!/usr/bin/env python3
"""
parametric_sweep_monitor.py

Script para monitorear el progreso del barrido paramétrico y generar reportes visuales.
"""

import json
import sys
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Tuple
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import numpy as np


def load_priority_summary(packages_dir: Path) -> Dict:
    """Cargar el resumen de prioridades."""
    summary_file = packages_dir / "priority_summary.json"
    
    if not summary_file.exists():
        print(f"⚠️  Advertencia: No se encontró {summary_file}")
        return {'HIGH': [], 'MEDIUM': [], 'LOW': []}
    
    with open(summary_file, 'r') as f:
        return json.load(f)


def scan_results(results_dir: Path) -> Dict[int, Dict]:
    """Escanear directorio de resultados y cargar datos."""
    results = {}
    
    if not results_dir.exists():
        return results
    
    for result_file in results_dir.glob("results_package_*.json"):
        try:
            with open(result_file, 'r') as f:
                data = json.load(f)
                package_id = data['package_id']
                results[package_id] = data
        except Exception as e:
            print(f"⚠️  Error cargando {result_file}: {e}")
    
    return results


def get_package_priority(package_id: int, priority_summary: Dict) -> str:
    """Determinar la prioridad de un paquete."""
    for priority in ['HIGH', 'MEDIUM', 'LOW']:
        pkg_ids = [pkg['package_id'] for pkg in priority_summary.get(priority, [])]
        if package_id in pkg_ids:
            return priority
    return 'UNKNOWN'


def analyze_results(
    priority_summary: Dict,
    results: Dict[int, Dict]
) -> Dict:
    """Analizar resultados y generar estadísticas."""
    
    stats = {
        'total_packages': 0,
        'completed': 0,
        'pending': 0,
        'failed': 0,
        'success_rate': 0.0,
        'by_priority': {
            'HIGH': {'total': 0, 'completed': 0, 'failed': 0},
            'MEDIUM': {'total': 0, 'completed': 0, 'failed': 0},
            'LOW': {'total': 0, 'completed': 0, 'failed': 0}
        },
        'total_execution_time': 0.0
    }
    
    # Contar totales por prioridad
    for priority in ['HIGH', 'MEDIUM', 'LOW']:
        stats['by_priority'][priority]['total'] = len(
            priority_summary.get(priority, [])
        )
        stats['total_packages'] += stats['by_priority'][priority]['total']
    
    # Analizar resultados completados
    for pkg_id, data in results.items():
        priority = get_package_priority(pkg_id, priority_summary)
        
        if data['status'] == 'completed':
            stats['completed'] += 1
            if priority in stats['by_priority']:
                stats['by_priority'][priority]['completed'] += 1
        else:
            stats['failed'] += 1
            if priority in stats['by_priority']:
                stats['by_priority'][priority]['failed'] += 1
        
        stats['total_execution_time'] += data.get('execution_time', 0.0)
    
    stats['pending'] = stats['total_packages'] - stats['completed'] - stats['failed']
    
    if stats['completed'] + stats['failed'] > 0:
        stats['success_rate'] = (
            100.0 * stats['completed'] / (stats['completed'] + stats['failed'])
        )
    
    return stats


def create_progress_visualization(
    stats: Dict,
    output_file: Path
) -> None:
    """Crear visualización del progreso."""
    
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    fig.suptitle(
        'Barrido Paramétrico - Progreso de Ejecución',
        fontsize=16,
        fontweight='bold'
    )
    
    # 1. Gráfico de torta general
    ax1 = axes[0, 0]
    labels = ['Completados', 'Pendientes', 'Fallidos']
    sizes = [stats['completed'], stats['pending'], stats['failed']]
    colors = ['#28a745', '#ffc107', '#dc3545']
    explode = (0.1, 0, 0)
    
    ax1.pie(
        sizes,
        explode=explode,
        labels=labels,
        colors=colors,
        autopct='%1.1f%%',
        shadow=True,
        startangle=90
    )
    ax1.set_title('Estado General')
    
    # 2. Progreso por prioridad
    ax2 = axes[0, 1]
    priorities = ['HIGH', 'MEDIUM', 'LOW']
    x = np.arange(len(priorities))
    width = 0.25
    
    completed = [stats['by_priority'][p]['completed'] for p in priorities]
    failed = [stats['by_priority'][p]['failed'] for p in priorities]
    pending = [
        stats['by_priority'][p]['total'] - 
        stats['by_priority'][p]['completed'] - 
        stats['by_priority'][p]['failed']
        for p in priorities
    ]
    
    ax2.bar(x - width, completed, width, label='Completados', color='#28a745')
    ax2.bar(x, failed, width, label='Fallidos', color='#dc3545')
    ax2.bar(x + width, pending, width, label='Pendientes', color='#ffc107')
    
    ax2.set_xlabel('Prioridad')
    ax2.set_ylabel('Número de Paquetes')
    ax2.set_title('Progreso por Prioridad')
    ax2.set_xticks(x)
    ax2.set_xticklabels(priorities)
    ax2.legend()
    ax2.grid(axis='y', alpha=0.3)
    
    # 3. Tabla de estadísticas
    ax3 = axes[1, 0]
    ax3.axis('off')
    
    table_data = [
        ['Métrica', 'Valor'],
        ['Total de Paquetes', f"{stats['total_packages']}"],
        ['Completados', f"{stats['completed']}"],
        ['Pendientes', f"{stats['pending']}"],
        ['Fallidos', f"{stats['failed']}"],
        ['Tasa de Éxito', f"{stats['success_rate']:.1f}%"],
        ['Tiempo Total', f"{stats['total_execution_time']:.1f}s"]
    ]
    
    table = ax3.table(
        cellText=table_data,
        cellLoc='left',
        loc='center',
        colWidths=[0.6, 0.4]
    )
    table.auto_set_font_size(False)
    table.set_fontsize(10)
    table.scale(1, 2)
    
    # Estilo de la cabecera
    for i in range(2):
        table[(0, i)].set_facecolor('#4CAF50')
        table[(0, i)].set_text_props(weight='bold', color='white')
    
    ax3.set_title('Estadísticas Generales')
    
    # 4. Barra de progreso visual
    ax4 = axes[1, 1]
    ax4.axis('off')
    
    progress_percent = (
        100.0 * (stats['completed'] + stats['failed']) / 
        max(stats['total_packages'], 1)
    )
    
    # Crear barra de progreso
    rect_bg = mpatches.Rectangle(
        (0.1, 0.4), 0.8, 0.2,
        facecolor='#e0e0e0',
        edgecolor='black',
        linewidth=2
    )
    ax4.add_patch(rect_bg)
    
    rect_progress = mpatches.Rectangle(
        (0.1, 0.4), 0.8 * (progress_percent / 100.0), 0.2,
        facecolor='#4CAF50' if progress_percent == 100 else '#2196F3',
        edgecolor='black',
        linewidth=2
    )
    ax4.add_patch(rect_progress)
    
    ax4.text(
        0.5, 0.5,
        f'{progress_percent:.1f}%',
        ha='center',
        va='center',
        fontsize=20,
        fontweight='bold'
    )
    
    ax4.text(
        0.5, 0.2,
        f'{stats["completed"] + stats["failed"]} / {stats["total_packages"]} paquetes procesados',
        ha='center',
        va='center',
        fontsize=12
    )
    
    ax4.set_xlim(0, 1)
    ax4.set_ylim(0, 1)
    ax4.set_title('Progreso Total', fontsize=14, fontweight='bold')
    
    plt.tight_layout()
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    print(f"✅ Reporte visual guardado en: {output_file}")


def print_summary(stats: Dict) -> None:
    """Imprimir resumen en consola."""
    print("\n" + "="*70)
    print("  RESUMEN DE BARRIDO PARAMÉTRICO")
    print("="*70)
    
    print(f"\n📊 ESTADÍSTICAS GENERALES:")
    print(f"   Total de paquetes:    {stats['total_packages']}")
    print(f"   ✅ Completados:       {stats['completed']}")
    print(f"   ⏳ Pendientes:        {stats['pending']}")
    print(f"   ❌ Fallidos:          {stats['failed']}")
    print(f"   📈 Tasa de éxito:     {stats['success_rate']:.1f}%")
    print(f"   ⏱️  Tiempo total:      {stats['total_execution_time']:.1f}s")
    
    print(f"\n📋 PROGRESO POR PRIORIDAD:")
    for priority in ['HIGH', 'MEDIUM', 'LOW']:
        data = stats['by_priority'][priority]
        total = data['total']
        completed = data['completed']
        failed = data['failed']
        pending = total - completed - failed
        
        if total > 0:
            percent = 100.0 * completed / total
            print(f"   {priority:7s}: {completed:3d}/{total:3d} ({percent:5.1f}%) "
                  f"| Fallidos: {failed:2d} | Pendientes: {pending:2d}")
    
    print("\n" + "="*70 + "\n")


def main():
    """Función principal."""
    packages_dir = Path('parametric_sweep_packages')
    results_dir = Path('parametric_sweep_results')
    artifacts_dir = Path('artifacts')
    
    artifacts_dir.mkdir(exist_ok=True)
    
    print("\n🔍 Analizando resultados del barrido paramétrico...\n")
    
    # Cargar datos
    priority_summary = load_priority_summary(packages_dir)
    results = scan_results(results_dir)
    
    print(f"   Paquetes definidos: {sum(len(v) for v in priority_summary.values())}")
    print(f"   Resultados encontrados: {len(results)}")
    
    # Analizar
    stats = analyze_results(priority_summary, results)
    
    # Mostrar resumen
    print_summary(stats)
    
    # Generar visualización
    output_file = artifacts_dir / 'parametric_sweep_progress.png'
    try:
        create_progress_visualization(stats, output_file)
    except Exception as e:
        print(f"⚠️  No se pudo generar la visualización: {e}")
        print("   (Asegúrate de tener matplotlib instalado)")
    
    return 0


if __name__ == '__main__':
    sys.exit(main())
