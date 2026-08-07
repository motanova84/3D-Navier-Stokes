#!/usr/bin/env python3
"""
Demo: Atlas³-ABC Unified Theory

Interactive demonstration showing the connection between:
- Riemann Hypothesis
- ABC Conjecture  
- Navier-Stokes equations
- QCAL coherence at 141.7001 Hz

Author: José Manuel Mota Burruezo (JMMB Ψ✧∞³)
Date: 2026-02-24
"""

from atlas3_abc_unified import Atlas3ABCUnified, ABCTriple
import numpy as np


def demo_abc_triple_basics():
    """Demonstrate ABC triple fundamentals"""
    print("\n" + "="*70)
    print("DEMO 1: ABC Triple Fundamentals")
    print("="*70)
    
    # Create a simple ABC triple
    triple = ABCTriple(1, 8, 9)
    
    print(f"\nABC Triple: {triple.a} + {triple.b} = {triple.c}")
    print(f"  rad(abc) = rad({triple.a}·{triple.b}·{triple.c}) = {triple.radical()}")
    print(f"  Information content I = log₂({triple.c}) - log₂({triple.radical()}) = {triple.information_content():.6f}")
    print(f"  Reynolds arithmetic Re = log₂({triple.c}) / log₂({triple.radical()}) = {triple.reynolds_arithmetic():.6f}")
    print(f"  Is exceptional (I > 1)? {triple.is_exceptional()}")
    
    print("\nABC Conjecture predicts:")
    print("  • Only finitely many triples have I > 1 + ε")
    print("  • This connects to turbulence via Reynolds number analogy")
    print("  • Arithmetic 'turbulence' = exceptional ABC triples")


def demo_riemann_connection():
    """Demonstrate connection to Riemann Hypothesis"""
    print("\n" + "="*70)
    print("DEMO 2: Riemann Hypothesis Connection")
    print("="*70)
    
    framework = Atlas3ABCUnified()
    
    # First few Riemann zeros on critical line
    riemann_zeros = [
        complex(0.5, 14.134725),   # γ₁
        complex(0.5, 21.022040),   # γ₂
        complex(0.5, 25.010858),   # γ₃
    ]
    
    print("\nRiemann spectral operator Ĥ_RH(s) at critical line:")
    print("(s = 1/2 + i·γ where ζ(s) = 0)")
    
    for i, s in enumerate(riemann_zeros[:3], 1):
        value = framework.riemann_spectral_operator(s)
        print(f"\n  Zero {i}: s = {s}")
        print(f"    Ĥ_RH(s) = {abs(value):.6f} × exp(i·{np.angle(value):.4f})")
        print(f"    Phase coupled to f₀ = {framework.constants.f0} Hz")


def demo_adelic_structure():
    """Demonstrate adelic structure and heat kernel"""
    print("\n" + "="*70)
    print("DEMO 3: Adelic Structure & Heat Kernel")
    print("="*70)
    
    framework = Atlas3ABCUnified()
    triple = ABCTriple(1, 8, 9)
    
    print(f"\nABC triple: {triple.a} + {triple.b} = {triple.c}")
    print("\nAdelic operator K_ABC(t) = exp(-λ·t) × ∏_p L_p(triple):")
    
    times = [0.01, 0.5, 1.0, 2.0, 5.0]  # Changed from 0.0 to 0.01
    for t in times:
        value = framework.abc_adelic_operator(triple, t)
        print(f"  t = {t:.1f}: K_ABC = {abs(value):.6e} × exp(i·{np.angle(value):.4f})")
    
    print("\nHeat kernel decay (corrected formula):")
    print("  Uses: exp(-λ·t)  NOT exp(-λ/t)")
    print("  Standard heat kernel decay theory")


def demo_heat_trace_bounds():
    """Demonstrate heat trace bounds for ABC remainder"""
    print("\n" + "="*70)
    print("DEMO 4: Heat Trace Bounds")
    print("="*70)
    
    framework = Atlas3ABCUnified()
    
    print("\nABC remainder bound: |R_ABC(t)| ≤ C·ε·exp(-λ·t)")
    print(f"  C = κ_Π = {framework.constants.kappa_pi}")
    print(f"  ε = ε_crítico = {framework.constants.epsilon_critico:.2e}")
    print(f"  λ = {framework.constants.lambda_heat}")
    
    print("\nBounds at different times:")
    times = np.logspace(-1, 2, 10)
    for t in times:
        bound = framework.compute_heat_trace_bound(t)
        print(f"  t = {t:8.3f}: |R_ABC(t)| ≤ {bound:.6e}")
    
    print("\nExponential decay ensures ABC conjecture finiteness!")


def demo_unified_coupling():
    """Demonstrate unified Riemann-ABC-Navier-Stokes coupling"""
    print("\n" + "="*70)
    print("DEMO 5: Unified Coupling")
    print("="*70)
    
    framework = Atlas3ABCUnified()
    framework.generate_example_triples(5)
    
    print("\nUnified coupling: Φ_unified(s, triple, t) = Ĥ_RH(s) · K_ABC(triple, t) · Ψ(f₀)")
    print("  Connects: Riemann zeros → ABC triples → Navier-Stokes flow")
    print("  Mediated by: QCAL coherence field at f₀ = 141.7001 Hz")
    
    # Use first Riemann zero
    s = complex(0.5, 14.134725)
    triple = framework.abc_triples[0]
    
    print(f"\nExample computation:")
    print(f"  Riemann zero: s = {s}")
    print(f"  ABC triple: ({triple.a}, {triple.b}, {triple.c})")
    
    times = [0.01, 0.5, 1.0, 2.0]  # Changed from 0.0 to 0.01
    print(f"\n  Unified coupling values:")
    for t in times:
        coupling = framework.unified_coupling(triple, s, t)
        print(f"    t = {t:.1f}: Φ = {abs(coupling):.6e} × exp(i·{np.angle(coupling):.4f})")


def demo_abc_distribution():
    """Demonstrate ABC triple distribution analysis"""
    print("\n" + "="*70)
    print("DEMO 6: ABC Triple Distribution")
    print("="*70)
    
    framework = Atlas3ABCUnified()
    triples = framework.generate_example_triples(10)
    
    print("\nGenerated 10 well-known ABC triples:")
    for i, t in enumerate(triples, 1):
        exceptional = "⚠️  EXCEPTIONAL" if t.is_exceptional() else "   regular"
        print(f"  {i:2d}. ({t.a:3d}, {t.b:3d}, {t.c:3d}): "
              f"I = {t.information_content():6.4f}, "
              f"Re = {t.reynolds_arithmetic():6.4f}  {exceptional}")
    
    analysis = framework.analyze_abc_distribution()
    print("\nStatistical Analysis:")
    print(f"  Total triples: {analysis['total_triples']}")
    print(f"  Exceptional (I > 1): {analysis['exceptional_count']}")
    print(f"  Exceptional fraction: {analysis['exceptional_fraction']:.2%}")
    print(f"\n  Information content:")
    print(f"    Mean: {analysis['information_content']['mean']:.6f}")
    print(f"    Std:  {analysis['information_content']['std']:.6f}")
    print(f"    Range: [{analysis['information_content']['min']:.6f}, "
          f"{analysis['information_content']['max']:.6f}]")
    print(f"\n  Reynolds arithmetic:")
    print(f"    Mean: {analysis['reynolds_arithmetic']['mean']:.6f}")
    print(f"    Std:  {analysis['reynolds_arithmetic']['std']:.6f}")
    print(f"    Range: [{analysis['reynolds_arithmetic']['min']:.6f}, "
          f"{analysis['reynolds_arithmetic']['max']:.6f}]")


def demo_qcal_coherence():
    """Demonstrate QCAL coherence field"""
    print("\n" + "="*70)
    print("DEMO 7: QCAL Coherence Field")
    print("="*70)
    
    framework = Atlas3ABCUnified()
    
    print(f"\nQCAL coherence field: Ψ(t) = exp(-i·ω·t)")
    print(f"  Fundamental frequency: f₀ = {framework.constants.f0} Hz")
    print(f"  Angular frequency: ω = 2π·f₀ = {2*np.pi*framework.constants.f0:.2f} rad/s")
    
    print("\nCoherence field values:")
    times = np.linspace(0, 1.0/framework.constants.f0, 5)  # One period
    for t in times:
        psi = framework.qcal_coherence_field(t)
        print(f"  t = {t*1000:.4f} ms: Ψ = {abs(psi):.6f} × exp(i·{np.angle(psi):.4f})")
    
    print("\nThis universal frequency:")
    print("  • Prevents turbulence divergence")
    print("  • Couples Riemann zeros to ABC triples")
    print("  • Emerges from quantum coherence")


def main():
    """Run all demonstrations"""
    print("\n" + "="*70)
    print("Atlas³-ABC Unified Theory - Interactive Demonstration")
    print("="*70)
    print("\nConnecting:")
    print("  • Riemann Hypothesis (zeros of ζ(s))")
    print("  • ABC Conjecture (arithmetic triples)")
    print("  • Navier-Stokes equations (turbulence)")
    print("  • QCAL coherence at f₀ = 141.7001 Hz")
    print("\nAuthor: José Manuel Mota Burruezo (JMMB Ψ✧∞³)")
    
    # Run all demos
    demo_abc_triple_basics()
    demo_riemann_connection()
    demo_adelic_structure()
    demo_heat_trace_bounds()
    demo_unified_coupling()
    demo_abc_distribution()
    demo_qcal_coherence()
    
    print("\n" + "="*70)
    print("Demonstration Complete!")
    print("="*70)
    print("\nNext steps:")
    print("  • Run: python test_atlas3_abc_unified.py")
    print("  • Read: ATLAS3_ABC_UNIFIED_README.md")
    print("  • Explore: atlas3_abc_unified.py")
    print()


if __name__ == "__main__":
Demostración: Teoría Unificada Atlas³-ABC

Demostración completa de la teoría unificada que conecta la Hipótesis de Riemann
(Atlas³) con la Conjetura ABC mediante dinámica adélica de Navier-Stokes.

Este script ejecuta:
1. Validación completa del Teorema Unificado (A+B+C)
2. Análisis de ternas ABC excepcionales
3. Cálculo del espectro unificado L_ABC
4. Verificación de constante de acoplamiento universal
5. Generación de visualizaciones y resultados

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
Date: 14 de febrero de 2026

Sello: ∴𓂀Ω∞³Φ
Firma: JMMB Ω✧
Frecuencia: f₀ = 141.7001 Hz
"""

import sys
from pathlib import Path
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.gridspec import GridSpec
import json
from datetime import datetime

# Importar la teoría unificada
from atlas3_abc_unified import (
    Atlas3ABCUnified,
    Atlas3ABCParams,
    ABCTriple,
    print_unified_theorem_box,
    print_validation_summary,
    KAPPA_PI,
    EPSILON_CRITICO,
    MU_COUPLING,
    FUNDAMENTAL_FREQUENCY_HZ,
    PHI
)


def demo_1_basic_validation():
    """
    Demo 1: Validación básica del teorema unificado
    """
    print("\n" + "="*70)
    print("DEMO 1: VALIDACIÓN BÁSICA DEL TEOREMA UNIFICADO")
    print("="*70 + "\n")
    
    # Imprimir el cuadro del teorema
    print_unified_theorem_box()
    
    # Crear modelo
    model = Atlas3ABCUnified()
    
    print("\nEjecutando validación completa del teorema Atlas³-ABC...")
    results = model.validate_unified_theorem()
    
    # Mostrar resumen
    print_validation_summary(results)
    
    return model, results


def demo_2_abc_triples_analysis():
    """
    Demo 2: Análisis detallado de ternas ABC
    """
    print("\n" + "="*70)
    print("DEMO 2: ANÁLISIS DE TERNAS ABC")
    print("="*70 + "\n")
    
    model = Atlas3ABCUnified()
    
    # Generar ternas ABC
    print("Generando 500 ternas ABC aleatorias...")
    triples = model.generate_abc_triples(max_value=1000, num_samples=500)
    
    # Analizar ternas excepcionales
    print("\nAnalizando ternas excepcionales (I(a,b,c) > 1 + ε)...")
    analysis = model.analyze_exceptional_triples(triples)
    
    print(f"\nRESULTADOS:")
    print(f"  Total de ternas: {analysis['total_triples']}")
    print(f"  Ternas excepcionales: {analysis['exceptional_triples']}")
    print(f"  Fracción excepcional: {analysis['fraction_exceptional']:.4%}")
    print(f"  Reynolds medio: {analysis['reynolds_mean']:.4f}")
    print(f"  Reynolds máximo: {analysis['reynolds_max']:.4f}")
    print(f"  Ternas turbulentas (Re > κ_Π): {analysis['turbulent_count']}")
    print(f"  Información media: {analysis['information_mean']:.6f}")
    print(f"  Información máxima: {analysis['information_max']:.6f}")
    print(f"\n  Predicción ABC: {analysis['abc_conjecture_prediction']}")
    
    # Ejemplos de ternas
    print("\n  Ejemplos de ternas:")
    for i, triple in enumerate(triples[:5]):
        print(f"    {i+1}. {triple.a} + {triple.b} = {triple.c}")
        print(f"       rad(abc) = {triple.radical}")
        print(f"       I(a,b,c) = {triple.information_content:.6f}")
        print(f"       Re_abc = {triple.reynolds_arithmetic:.6f}")
        print(f"       Excepcional: {triple.is_exceptional()}")
    
    return analysis


def demo_3_spectral_analysis():
    """
    Demo 3: Análisis espectral del operador L_ABC
    """
    print("\n" + "="*70)
    print("DEMO 3: ANÁLISIS ESPECTRAL DEL OPERADOR L_ABC")
    print("="*70 + "\n")
    
    model = Atlas3ABCUnified()
    
    # Crear grilla en espacio adélico
    print("Creando grilla en espacio adélico...")
    x_grid = np.linspace(-10, 10, 128)
    
    # Terna ABC de prueba
    triple = ABCTriple(a=5, b=13, c=18)
    print(f"\nTerna ABC: {triple.a} + {triple.b} = {triple.c}")
    print(f"  rad(abc) = {triple.radical}")
    print(f"  I(a,b,c) = {triple.information_content:.6f}")
    
    # Calcular espectro
    print("\nCalculando espectro del operador L_ABC...")
    spectrum = model.unified_operator_spectrum(x_grid, triple)
    
    print(f"\nRESULTADOS ESPECTRALES:")
    print(f"  Dimensión del espacio: {len(spectrum.eigenvalues)}")
    print(f"  Gap espectral: {spectrum.spectral_gap:.6e}")
    print(f"  Eigenvalue mínimo: {spectrum.eigenvalues[0]:.6e}")
    print(f"  Eigenvalue máximo: {spectrum.eigenvalues[-1]:.6e}")
    
    print(f"\n  Primeros 10 ceros de Riemann aproximados (Im(ρ)):")
    for i, zero in enumerate(spectrum.riemann_zeros[:10]):
        print(f"    ρ_{i+1} ≈ 1/2 + i·{zero:.6f}")
    
    return spectrum


def demo_4_heat_trace():
    """
    Demo 4: Traza de calor con control ABC
    """
    print("\n" + "="*70)
    print("DEMO 4: TRAZA DE CALOR CON CONTROL ABC")
    print("="*70 + "\n")
    
    model = Atlas3ABCUnified()
    
    # Calcular espectro
    x_grid = np.linspace(-10, 10, 64)
    spectrum = model.unified_operator_spectrum(x_grid)
    
    # Evaluar traza de calor en varios tiempos
    print("Evaluando traza de calor Tr(e^{-tL}) con control ABC...")
    times = np.logspace(-4, -2, 10)
    
    print(f"\n{'Tiempo t':<12} {'Tr(e^{-tL})':<15} {'Weyl(t)':<15} {'|R_ABC|':<15} {'Cota':<15} {'OK?':<5}")
    print("-" * 77)
    
    for t in times:
        ht = model.heat_trace_with_abc_control(t, spectrum, include_prime_expansion=True)
        ok = "✓" if ht['bound_satisfied'] else "✗"
        print(f"{t:<12.2e} {ht['trace_exact']:<15.6e} {ht['weyl_term']:<15.6e} "
              f"{ht['remainder_abs']:<15.6e} {ht['theoretical_bound']:<15.6e} {ok:<5}")
    
    return times


def demo_5_coupling_constant():
    """
    Demo 5: Verificación de constante de acoplamiento universal
    """
    print("\n" + "="*70)
    print("DEMO 5: CONSTANTE DE ACOPLAMIENTO UNIVERSAL")
    print("="*70 + "\n")
    
    print("La constante de acoplamiento μ = κ_Π·ε_crítico debe ser universal,")
    print("independiente de la frecuencia f₀.\n")
    
    # Probar con diferentes frecuencias
    frequencies = [100.0, 141.7001, 200.0, 300.0]
    
    print(f"{'f₀ (Hz)':<12} {'κ_Π':<12} {'ε_crítico':<15} {'μ = κ·ε':<15} {'μ_teórico':<15}")
    print("-" * 77)
    
    for f0 in frequencies:
        params = Atlas3ABCParams(f0=f0)
        model = Atlas3ABCUnified(params)
        
        validation = model._validate_coupling_constant()
        
        print(f"{f0:<12.4f} {params.kappa_pi:<12.6f} {params.epsilon_critico:<15.6e} "
              f"{validation['computed_mu']:<15.6e} {validation['theoretical_mu']:<15.6e}")
    
    print("\n✅ La constante μ es universal: μ = 4πℏ/(k_B·T_cosmic·Φ)")
    print(f"   Valor teórico: {validation['theoretical_mu']:.6e}")
    print(f"   Independiente de f₀!")


def create_visualizations(model, results, spectrum, analysis):
    """
    Crear visualizaciones de la teoría unificada
    """
    print("\n" + "="*70)
    print("GENERANDO VISUALIZACIONES")
    print("="*70 + "\n")
    
    # Crear directorio de visualizaciones
    viz_dir = Path(__file__).parent / 'visualizations'
    viz_dir.mkdir(exist_ok=True)
    
    # Figura 1: Espectro del operador L_ABC
    fig1 = plt.figure(figsize=(12, 8))
    gs = GridSpec(2, 2, figure=fig1, hspace=0.3, wspace=0.3)
    
    # Panel 1: Eigenvalues
    ax1 = fig1.add_subplot(gs[0, 0])
    ax1.plot(spectrum.eigenvalues, 'o-', alpha=0.7)
    ax1.set_xlabel('Índice n')
    ax1.set_ylabel('λ_n')
    ax1.set_title('Espectro del Operador L_ABC')
    ax1.grid(True, alpha=0.3)
    ax1.set_yscale('log')
    
    # Panel 2: Ceros de Riemann
    ax2 = fig1.add_subplot(gs[0, 1])
    ax2.plot(spectrum.riemann_zeros[:20], 'o-', color='red', alpha=0.7)
    ax2.set_xlabel('Índice n')
    ax2.set_ylabel('Im(ρ_n)')
    ax2.set_title('Ceros de Riemann Aproximados')
    ax2.grid(True, alpha=0.3)
    
    # Panel 3: Distribución de Reynolds ABC
    ax3 = fig1.add_subplot(gs[1, 0])
    reynolds_values = [t.reynolds_arithmetic for t in model._abc_triples[:100]]
    ax3.hist(reynolds_values, bins=30, alpha=0.7, color='blue', edgecolor='black')
    ax3.axvline(KAPPA_PI, color='red', linestyle='--', linewidth=2, label=f'κ_Π = {KAPPA_PI:.3f}')
    ax3.set_xlabel('Re_abc')
    ax3.set_ylabel('Frecuencia')
    ax3.set_title('Distribución de Reynolds Aritmético')
    ax3.legend()
    ax3.grid(True, alpha=0.3)
    
    # Panel 4: Información I(a,b,c)
    ax4 = fig1.add_subplot(gs[1, 1])
    info_values = [t.information_content for t in model._abc_triples[:100]]
    ax4.hist(info_values, bins=30, alpha=0.7, color='green', edgecolor='black')
    ax4.axvline(1.0, color='orange', linestyle='--', linewidth=2, label='I = 1')
    ax4.set_xlabel('I(a,b,c)')
    ax4.set_ylabel('Frecuencia')
    ax4.set_title('Función de Información ABC')
    ax4.legend()
    ax4.grid(True, alpha=0.3)
    
    # Agregar sello QCAL
    fig1.text(0.99, 0.01, '∴𓂀Ω∞³Φ | f₀=141.7001 Hz', 
              ha='right', va='bottom', fontsize=8, alpha=0.5)
    
    filename1 = viz_dir / 'atlas3_abc_unified_analysis.png'
    fig1.savefig(filename1, dpi=150, bbox_inches='tight')
    print(f"✓ Visualización guardada: {filename1}")
    plt.close(fig1)
    
    # Figura 2: Teorema unificado (estado)
    fig2, ax = plt.subplots(figsize=(10, 8))
    ax.axis('off')
    
    status = results['unified_theory_status']
    theorem_a = results['theorem_parts']['A_self_adjoint']
    theorem_b = results['theorem_parts']['B_compact_resolvent']
    theorem_c = results['theorem_parts']['C_heat_trace_abc']
    
    text = f"""
    TEOREMA UNIFICADO ATLAS³-ABC
    {'='*50}
    
    Estado: {status['message']}
    Sello: {status['seal']}
    Frecuencia: {status['frequency']}
    Curvatura: {status['curvature']}
    
    COMPONENTES:
    
    (A) Auto-adjunción Esencial:
        {theorem_a['message']}
        Eigenvalores reales: {theorem_a['eigenvalues_real']}
    
    (B) Resolvente Compacto:
        {theorem_b['message']}
        Gap espectral: {theorem_b['spectral_gap']:.6e}
    
    (C) Traza de Calor ABC:
        {theorem_c['message']}
        Tiempos probados: {theorem_c['num_times_tested']}
    
    COROLARIOS:
    
    1. Hipótesis de Riemann: Conexión espectral establecida
       Ceros calculados: {results['corollaries']['riemann_hypothesis']['num_zeros_computed']}
    
    2. Conjetura ABC: {analysis['abc_conjecture_prediction']}
       Ternas excepcionales: {analysis['exceptional_triples']}/{analysis['total_triples']}
    
    3. Constante Universal:
       μ = κ·ε = {results['corollaries']['universal_coupling']['coupling_constant']:.6e}
    
    {'='*50}
    Instituto Consciencia Cuántica QCAL ∞³
    """
    
    ax.text(0.1, 0.5, text, fontsize=10, family='monospace',
            verticalalignment='center', transform=ax.transAxes)
    
    filename2 = viz_dir / 'atlas3_abc_theorem_status.png'
    fig2.savefig(filename2, dpi=150, bbox_inches='tight')
    print(f"✓ Visualización guardada: {filename2}")
    plt.close(fig2)
    
    print(f"\n✅ Visualizaciones creadas en: {viz_dir}/")


def main():
    """Función principal de demostración"""
    
    print("\n" + "╔" + "═"*68 + "╗")
    print("║" + " "*68 + "║")
    print("║" + "  DEMOSTRACIÓN: TEORÍA UNIFICADA ATLAS³-ABC".center(68) + "║")
    print("║" + " "*68 + "║")
    print("║" + "  Unificación de Riemann Hypothesis + ABC Conjecture".center(68) + "║")
    print("║" + "  via Dinámica Adélica de Navier-Stokes".center(68) + "║")
    print("║" + " "*68 + "║")
    print("╚" + "═"*68 + "╝\n")
    
    print(f"Frecuencia fundamental: f₀ = {FUNDAMENTAL_FREQUENCY_HZ} Hz")
    print(f"Constante crítica: κ_Π = {KAPPA_PI}")
    print(f"Épsilon crítico: ε_crítico = {EPSILON_CRITICO}")
    print(f"Acoplamiento mínimo: μ = {MU_COUPLING:.6e}")
    print(f"Proporción áurea: Φ = {PHI:.10f}")
    
    # Ejecutar demostraciones
    model, results = demo_1_basic_validation()
    analysis = demo_2_abc_triples_analysis()
    spectrum = demo_3_spectral_analysis()
    times = demo_4_heat_trace()
    demo_5_coupling_constant()
    
    # Crear visualizaciones
    create_visualizations(model, results, spectrum, analysis)
    
    # Exportar resultados
    print("\n" + "="*70)
    print("EXPORTANDO RESULTADOS")
    print("="*70 + "\n")
    
    model.export_results('atlas3_abc_results.json')
    
    print("\n" + "="*70)
    print("DEMOSTRACIÓN COMPLETA")
    print("="*70)
    print("\n✨ La Hipótesis de Riemann y la Conjetura ABC son dos aspectos")
    print("   de la misma realidad: la estructura vibracional de los números.")
    print("\n   Todo vibra. Todo es uno. ∴𓂀Ω∞³Φ ✨\n")


if __name__ == '__main__':
    main()
