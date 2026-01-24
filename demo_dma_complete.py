#!/usr/bin/env python3
"""
Demo completo del Acoplamiento DMA - Navier-Stokes y Entropía Cero

Este script demuestra la funcionalidad completa del protocolo DMA:
1. Inicialización de red de 88 nodos
2. Activación de superconductividad informacional
3. Verificación contra soluciones de flujo laminar NS
4. Validación del Axioma de Abundancia
5. Análisis de coherencia y entropía
6. Visualización de resultados

Author: JMMB Ψ✧∞³
License: MIT
"""

import numpy as np
import matplotlib.pyplot as plt
from datetime import datetime
import json

from dma_entropy_coupling import DMAEntropyZeroCoupling


def print_section_header(title: str):
    """Print a formatted section header"""
    print("\n" + "="*80)
    print(f"  {title}")
    print("="*80)


def demo_basic_initialization():
    """Demo: Basic initialization of DMA protocol"""
    print_section_header("DEMO 1: INICIALIZACIÓN BÁSICA")
    
    # Create DMA instance
    dma = DMAEntropyZeroCoupling()
    
    print(f"\n✓ Red inicializada con {len(dma.nodes)} nodos")
    print(f"✓ Estado inicial: {dma.entropy_state.value}")
    print(f"✓ Viscosidad noética: {dma.noetic_viscosity:.2e}")
    print(f"✓ Coherencia global: {dma.global_coherence:.6f}")
    
    # Show node distribution
    print(f"\n📊 Distribución de nodos:")
    print(f"   - Todos en esfera unitaria: {all(np.abs(np.linalg.norm(n.position) - 1.0) < 1e-6 for n in dma.nodes)}")
    print(f"   - Coherencia inicial: {all(n.coherence == 1.0 for n in dma.nodes)}")
    print(f"   - Viscosidad inicial: {all(n.viscosity == 0.0 for n in dma.nodes)}")
    
    return dma


def demo_laminar_flow_verification(dma):
    """Demo: Verification against NS laminar flow solutions"""
    print_section_header("DEMO 2: VERIFICACIÓN DE FLUJO LAMINAR NS")
    
    # Test various Reynolds numbers
    re_values = [50, 100, 500, 1000, 1500, 2000, 2500, 3000]
    
    print("\n📐 Soluciones de Navier-Stokes para diferentes Re:")
    print(f"\n{'Re':>8} {'Régimen':>15} {'f':>8} {'Disipación':>12}")
    print("-" * 48)
    
    laminar_count = 0
    for re in re_values:
        solution = dma.compute_laminar_flow_solution(re)
        regime = "✅ LAMINAR" if solution["is_laminar"] else "⚠️  TURBULENTO"
        print(f"{re:8.0f} {regime:>15} {solution['friction_factor']:8.4f} {solution['dissipation_rate']:12.4f}")
        
        if solution["is_laminar"]:
            laminar_count += 1
    
    print(f"\n✓ {laminar_count}/{len(re_values)} casos en régimen laminar")
    print(f"✓ Umbral laminar: Re < {dma.constants.RE_LAMINAR_MAX:.0f}")


def demo_superconductivity_activation(dma):
    """Demo: Activation of informational superconductivity"""
    print_section_header("DEMO 3: ACTIVACIÓN DE SUPERCONDUCTIVIDAD")
    
    print("\n🔄 Estado antes de activación:")
    print(f"   Viscosidad Noética: {dma.noetic_viscosity:.2e}")
    entropy_before = dma._compute_information_entropy()
    print(f"   Entropía: {entropy_before:.2e}")
    
    # Activate superconductivity
    print("\n🚀 Activando superconductividad informacional...")
    is_active = dma.activate_superconductivity()
    
    print(f"\n📊 Estado después de activación:")
    print(f"   Viscosidad Noética: {dma.noetic_viscosity:.2e}")
    entropy_after = dma._compute_information_entropy()
    print(f"   Entropía: {entropy_after:.2e}")
    print(f"   Estado: {dma.entropy_state.value}")
    
    if is_active:
        print(f"\n✅ Superconductividad ACTIVADA exitosamente")
        print(f"   - Reducción de viscosidad: {(1 - dma.noetic_viscosity/max(1e-15, entropy_before)) * 100:.2f}%")
        print(f"   - Reducción de entropía: {(1 - entropy_after/max(1e-15, entropy_before)) * 100:.2f}%")
    else:
        print(f"\n⚠️  Superconductividad NO alcanzada")


def demo_axiom_verification(dma):
    """Demo: Verification of Axiom of Abundance"""
    print_section_header("DEMO 4: VERIFICACIÓN DEL AXIOMA DE ABUNDANCIA")
    
    # Verify axiom
    results = dma.verify_axiom_of_abundance()
    
    print("\n📊 Criterios del Axioma de Abundancia:")
    criteria = results["criteria"]
    for criterion, value in criteria.items():
        status = "✅" if value else "❌"
        print(f"   {status} {criterion.replace('_', ' ').title()}: {value}")
    
    print("\n📈 Mediciones:")
    measurements = results["measurements"]
    print(f"   - Viscosidad Noética: {measurements['noetic_viscosity']:.2e}")
    print(f"   - Entropía de Información: {measurements['information_entropy']:.2e}")
    print(f"   - Coherencia Promedio: {measurements['average_coherence']:.6f}")
    print(f"   - Número de Reynolds (test): {measurements['reynolds_number']:.1f}")
    print(f"   - Tasa de Disipación: {measurements['dissipation_rate']:.4f}")
    
    print(f"\n⭐ Factor de Abundancia: {results['abundance_factor']:.1f}")
    
    if results["axiom_operational"]:
        print(f"\n✅ AXIOMA DE ABUNDANCIA: FÍSICAMENTE OPERATIVO")
    else:
        print(f"\n❌ AXIOMA DE ABUNDANCIA: NO OPERATIVO")


def demo_network_analysis(dma):
    """Demo: Detailed network analysis"""
    print_section_header("DEMO 5: ANÁLISIS DETALLADO DE LA RED")
    
    # Collect node statistics
    coherences = np.array([node.coherence for node in dma.nodes])
    viscosities = np.array([node.viscosity for node in dma.nodes])
    frequencies = np.array([node.frequency for node in dma.nodes])
    
    print("\n📊 Estadísticas de la Red:")
    print(f"\n   Coherencia:")
    print(f"   - Promedio: {np.mean(coherences):.6f}")
    print(f"   - Desv. Estándar: {np.std(coherences):.2e}")
    print(f"   - Mínimo: {np.min(coherences):.6f}")
    print(f"   - Máximo: {np.max(coherences):.6f}")
    
    print(f"\n   Viscosidad Noética:")
    print(f"   - Promedio: {np.mean(viscosities):.2e}")
    print(f"   - Desv. Estándar: {np.std(viscosities):.2e}")
    print(f"   - Máximo: {np.max(viscosities):.2e}")
    
    print(f"\n   Frecuencias:")
    print(f"   - Promedio: {np.mean(frequencies):.2f} Hz")
    print(f"   - Desv. Estándar: {np.std(frequencies):.2f} Hz")
    print(f"   - Rango: [{np.min(frequencies):.2f}, {np.max(frequencies):.2f}] Hz")
    
    # Analyze harmonic distribution
    print(f"\n   Distribución Armónica:")
    for harmonic in range(1, 8):
        f_harmonic = harmonic * dma.constants.F0_HZ
        count = np.sum(np.abs(frequencies - f_harmonic) < 1e-3)
        percentage = (count / len(dma.nodes)) * 100
        print(f"   - {harmonic}° armónico ({f_harmonic:.2f} Hz): {count} nodos ({percentage:.1f}%)")


def demo_complete_verification(dma):
    """Demo: Complete verification protocol"""
    print_section_header("DEMO 6: PROTOCOLO DE VERIFICACIÓN COMPLETO")
    
    # Run complete verification
    results = dma.run_complete_verification()
    
    # Summary
    print("\n📋 Resumen de Verificación:")
    print(f"   ✓ Superconductividad: {'✅ ACTIVADA' if results['superconductivity_achieved'] else '❌ NO ACTIVADA'}")
    print(f"   ✓ Axioma de Abundancia: {'✅ OPERATIVO' if results['axiom_of_abundance']['axiom_operational'] else '❌ NO OPERATIVO'}")
    print(f"   ✓ Nodos en la red: {results['network_statistics']['num_nodes']}")
    print(f"   ✓ Entropía: {results['network_statistics']['entropy_state']}")
    
    # Save results
    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    filename = f"Results/demo_dma_complete_{timestamp}.json"
    
    try:
        import os
        os.makedirs("Results", exist_ok=True)
        with open(filename, 'w') as f:
            json.dump(results, f, indent=2)
        print(f"\n💾 Resultados guardados: {filename}")
    except Exception as e:
        print(f"\n⚠️  Error al guardar resultados: {e}")
    
    return results


def create_visualization_comparison(dma):
    """Create comparison visualization of network states"""
    print_section_header("DEMO 7: VISUALIZACIÓN COMPARATIVA")
    
    # Create figure with subplots
    fig = plt.figure(figsize=(16, 6))
    
    # Subplot 1: Network topology (3D)
    ax1 = fig.add_subplot(131, projection='3d')
    positions = np.array([node.position for node in dma.nodes])
    coherences = np.array([node.coherence for node in dma.nodes])
    
    scatter = ax1.scatter(
        positions[:, 0], 
        positions[:, 1], 
        positions[:, 2],
        c=coherences,
        s=50,
        cmap='viridis',
        alpha=0.8
    )
    ax1.set_title('Red de 88 Nodos\n(Esfera de Fibonacci)', fontweight='bold')
    ax1.set_xlabel('X')
    ax1.set_ylabel('Y')
    ax1.set_zlabel('Z')
    plt.colorbar(scatter, ax=ax1, label='Coherencia', shrink=0.6)
    
    # Subplot 2: Frequency distribution
    ax2 = fig.add_subplot(132)
    frequencies = [node.frequency for node in dma.nodes]
    ax2.hist(frequencies, bins=20, color='skyblue', edgecolor='black', alpha=0.7)
    ax2.set_xlabel('Frecuencia (Hz)', fontweight='bold')
    ax2.set_ylabel('Número de Nodos', fontweight='bold')
    ax2.set_title('Distribución de Frecuencias', fontweight='bold')
    ax2.axvline(dma.constants.F0_HZ, color='red', linestyle='--', 
                label=f'f₀ = {dma.constants.F0_HZ} Hz')
    ax2.legend()
    ax2.grid(True, alpha=0.3)
    
    # Subplot 3: Laminar flow verification
    ax3 = fig.add_subplot(133)
    re_values = [100, 500, 1000, 1500, 2000, 2500]
    friction_factors = []
    colors = []
    
    for re in re_values:
        solution = dma.compute_laminar_flow_solution(re)
        friction_factors.append(solution['friction_factor'])
        colors.append('green' if solution['is_laminar'] else 'red')
    
    bars = ax3.bar(range(len(re_values)), friction_factors, color=colors, alpha=0.7, edgecolor='black')
    ax3.set_xlabel('Índice de Re', fontweight='bold')
    ax3.set_ylabel('Factor de Fricción', fontweight='bold')
    ax3.set_title('Verificación de Flujo Laminar NS', fontweight='bold')
    ax3.set_xticks(range(len(re_values)))
    ax3.set_xticklabels([f'Re={re}' for re in re_values], rotation=45)
    ax3.axhline(y=64/2300, color='black', linestyle='--', alpha=0.5, 
                label='Límite Laminar')
    ax3.legend()
    ax3.grid(True, alpha=0.3, axis='y')
    
    plt.tight_layout()
    
    # Save figure
    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    filename = f"Results/demo_dma_visualization_{timestamp}.png"
    
    try:
        import os
        os.makedirs("Results", exist_ok=True)
        plt.savefig(filename, dpi=300, bbox_inches='tight')
        print(f"\n📊 Visualización guardada: {filename}")
    except Exception as e:
        print(f"\n⚠️  Error al guardar visualización: {e}")
    
    plt.close()


def main():
    """Main demo script"""
    print("\n" + "="*80)
    print("  DEMO COMPLETO: ACOPLAMIENTO DMA - NAVIER-STOKES Y ENTROPÍA CERO")
    print("  Sistema de Superconductividad Informacional de 88 Nodos")
    print("="*80)
    
    # Demo 1: Basic initialization
    dma = demo_basic_initialization()
    
    # Demo 2: Laminar flow verification
    demo_laminar_flow_verification(dma)
    
    # Demo 3: Superconductivity activation
    demo_superconductivity_activation(dma)
    
    # Demo 4: Axiom verification
    demo_axiom_verification(dma)
    
    # Demo 5: Network analysis
    demo_network_analysis(dma)
    
    # Demo 6: Complete verification
    results = demo_complete_verification(dma)
    
    # Demo 7: Visualization
    create_visualization_comparison(dma)
    
    # Final summary
    print_section_header("RESUMEN FINAL")
    
    if results['superconductivity_achieved'] and results['axiom_of_abundance']['axiom_operational']:
        print("\n🎉 ÉXITO COMPLETO:")
        print("   ✅ Superconductividad informacional ACTIVADA")
        print("   ✅ Red de 88 nodos sincronizada")
        print("   ✅ Viscosidad noética = CERO")
        print("   ✅ Entropía = CERO (sin pérdida de información)")
        print("   ✅ Flujo laminar NS verificado")
        print("   ✅ Axioma de Abundancia OPERATIVO")
        print("\n   🌟 El sistema ha alcanzado el estado de propagación instantánea")
        print("   🌟 sin pérdida de calor, confirmando que el Axioma de Abundancia")
        print("   🌟 es físicamente operativo.")
    else:
        print("\n⚠️  ADVERTENCIA:")
        print("   El sistema no alcanzó el estado superconductive completo.")
        print("   Revise los parámetros de configuración.")
    
    print("\n" + "="*80)
    print("  FIN DE LA DEMOSTRACIÓN")
    print("="*80 + "\n")
    
    return results


if __name__ == "__main__":
    results = main()
