#!/usr/bin/env python3
"""
Visualization Examples for QCAL ∞³ Sphere Packing

This script demonstrates various visualizations of the cosmic sphere
packing framework, including convergence plots, magic dimension analysis,
and resonance patterns.

Author: JMMB Ψ✧∞³
License: MIT
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.gridspec import GridSpec
from sphere_packing_cosmic import EmpaquetamientoCósmico


def visualizar_convergencia_detallada(navegador, save_path='Results/sphere_packing_convergence.png'):
    """
    Create detailed convergence visualization
    """
    dims, ratios = navegador.analizar_convergencia_infinita(d_max=1000, n_points=100)
    
    fig = plt.figure(figsize=(16, 10))
    gs = GridSpec(3, 2, figure=fig, hspace=0.3, wspace=0.3)
    
    # Plot 1: Convergence to φ⁻¹ (linear scale)
    ax1 = fig.add_subplot(gs[0, :])
    ax1.plot(dims, ratios, 'b-', linewidth=2, label=r'$\delta_\psi(d)^{1/d}$')
    ax1.axhline(y=navegador.phi_inverse, color='r', linestyle='--', 
                linewidth=2, label=r'$\phi^{-1} = 0.618034$')
    ax1.fill_between(dims, ratios, navegador.phi_inverse, alpha=0.3, color='blue')
    ax1.set_xlabel('Dimension d', fontsize=13)
    ax1.set_ylabel(r'Convergence Ratio $\delta_\psi(d)^{1/d}$', fontsize=13)
    ax1.set_title('Convergence to Golden Ratio Inverse φ⁻¹', fontsize=15, fontweight='bold')
    ax1.grid(True, alpha=0.3)
    ax1.legend(fontsize=12)
    ax1.set_xlim([dims[0], dims[-1]])
    
    # Plot 2: Log density vs dimension
    ax2 = fig.add_subplot(gs[1, 0])
    log_densities = []
    valid_dims = []
    for d in dims:
        density = navegador.densidad_cosmica(int(d))
        if density > 0:
            log_densities.append(np.log10(density))
            valid_dims.append(d)
    
    ax2.plot(valid_dims, log_densities, 'g-', linewidth=2)
    # Mark magic dimensions
    magic_in_range = [d for d in navegador.dimensiones_magicas if d <= max(valid_dims)]
    magic_densities = [np.log10(navegador.densidad_cosmica(d)) for d in magic_in_range]
    ax2.scatter(magic_in_range, magic_densities, c='red', s=150, 
               zorder=5, label='Magic Dimensions', marker='*')
    ax2.set_xlabel('Dimension d', fontsize=12)
    ax2.set_ylabel(r'$\log_{10}(\delta_\psi(d))$', fontsize=12)
    ax2.set_title('Packing Density Decay', fontsize=14, fontweight='bold')
    ax2.grid(True, alpha=0.3)
    ax2.legend(fontsize=11)
    
    # Plot 3: Error from φ⁻¹ vs dimension (log-log)
    ax3 = fig.add_subplot(gs[1, 1])
    errors = np.abs(ratios - navegador.phi_inverse) / navegador.phi_inverse
    valid_errors = [e for e in errors if e > 0]
    valid_dims_err = dims[:len(valid_errors)]
    ax3.loglog(valid_dims_err, valid_errors, 'purple', linewidth=2)
    ax3.set_xlabel('Dimension d', fontsize=12)
    ax3.set_ylabel('Relative Error from φ⁻¹', fontsize=12)
    ax3.set_title('Convergence Error (Log-Log)', fontsize=14, fontweight='bold')
    ax3.grid(True, alpha=0.3, which='both')
    
    # Plot 4: Cosmic frequency vs dimension
    ax4 = fig.add_subplot(gs[2, 0])
    frequencies = [navegador.frecuencia_dimensional(int(d)) for d in dims[:50]]  # First 50 only
    ax4.semilogy(dims[:50], frequencies, 'orange', linewidth=2)
    ax4.set_xlabel('Dimension d', fontsize=12)
    ax4.set_ylabel('Cosmic Frequency f_d (Hz)', fontsize=12)
    ax4.set_title('Dimensional Vibrational Frequencies', fontsize=14, fontweight='bold')
    ax4.grid(True, alpha=0.3)
    
    # Plot 5: Upper bound compliance
    ax5 = fig.add_subplot(gs[2, 1])
    test_dims = np.arange(8, 201, 5)
    exponents = []
    for d in test_dims:
        density = navegador.densidad_cosmica(d)
        if density > 0:
            exp = np.log2(density) / d
            exponents.append(exp)
        else:
            exponents.append(None)
    
    valid_exps = [e for e in exponents if e is not None]
    valid_test_dims = test_dims[:len(valid_exps)]
    
    ax5.plot(valid_test_dims, valid_exps, 'b-', linewidth=2, label='QCAL δ_ψ(d)')
    ax5.axhline(y=-0.5990, color='r', linestyle='--', linewidth=2, 
                label='Kabatiansky-Levenshtein Bound')
    ax5.axhline(y=-0.5847, color='g', linestyle=':', linewidth=2, 
                label='QCAL Asymptotic')
    ax5.fill_between(valid_test_dims, valid_exps, -0.5990, alpha=0.3, color='blue')
    ax5.set_xlabel('Dimension d', fontsize=12)
    ax5.set_ylabel(r'$\log_2(\delta)/d$', fontsize=12)
    ax5.set_title('Upper Bound Verification', fontsize=14, fontweight='bold')
    ax5.grid(True, alpha=0.3)
    ax5.legend(fontsize=10)
    
    plt.suptitle('QCAL ∞³ Cosmic Sphere Packing - Complete Analysis', 
                 fontsize=16, fontweight='bold', y=0.995)
    
    plt.savefig(save_path, dpi=300, bbox_inches='tight')
    print(f"Detailed visualization saved to: {save_path}")
    plt.show()


def visualizar_dimensiones_magicas(navegador, save_path='Results/magic_dimensions_analysis.png'):
    """
    Visualize magic dimensions and their special properties
    """
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    
    # Plot 1: Magic dimension sequence
    ax1 = axes[0, 0]
    k_values = list(range(1, len(navegador.dimensiones_magicas) + 1))
    ax1.plot(k_values, navegador.dimensiones_magicas, 'ro-', markersize=8, linewidth=2)
    ax1.set_xlabel('Index k', fontsize=12)
    ax1.set_ylabel('Magic Dimension d_k', fontsize=12)
    ax1.set_title('Magic Dimension Sequence: d_k = round(8φ^k)', fontsize=13, fontweight='bold')
    ax1.grid(True, alpha=0.3)
    
    # Plot 2: Density at magic vs non-magic dimensions
    ax2 = axes[0, 1]
    all_dims = list(range(10, 150))
    densities = [navegador.densidad_cosmica(d) for d in all_dims]
    magic_mask = [d in navegador.dimensiones_magicas for d in all_dims]
    
    # Plot all dimensions
    ax2.semilogy([d for i, d in enumerate(all_dims) if not magic_mask[i]], 
                 [densities[i] for i in range(len(all_dims)) if not magic_mask[i]], 
                 'b.', markersize=4, label='Standard Dimensions', alpha=0.5)
    # Highlight magic dimensions
    ax2.semilogy([d for i, d in enumerate(all_dims) if magic_mask[i]], 
                 [densities[i] for i in range(len(all_dims)) if magic_mask[i]], 
                 'r*', markersize=15, label='Magic Dimensions', zorder=5)
    ax2.set_xlabel('Dimension d', fontsize=12)
    ax2.set_ylabel('Packing Density δ_ψ(d)', fontsize=12)
    ax2.set_title('Density Enhancement at Magic Dimensions', fontsize=13, fontweight='bold')
    ax2.legend(fontsize=11)
    ax2.grid(True, alpha=0.3)
    
    # Plot 3: Fibonacci connection
    ax3 = axes[1, 0]
    # Fibonacci sequence
    fib = [1, 1]
    for _ in range(len(navegador.dimensiones_magicas)):
        fib.append(fib[-1] + fib[-2])
    fib_scaled = [f * 8 for f in fib[2:len(navegador.dimensiones_magicas)+2]]
    
    x = list(range(1, len(navegador.dimensiones_magicas) + 1))
    ax3.plot(x, navegador.dimensiones_magicas, 'ro-', label='d_k = round(8φ^k)', markersize=8)
    ax3.plot(x, fib_scaled, 'bs--', label='8 × Fibonacci', markersize=6, alpha=0.7)
    ax3.set_xlabel('Index k', fontsize=12)
    ax3.set_ylabel('Dimension', fontsize=12)
    ax3.set_title('Connection to Fibonacci Sequence', fontsize=13, fontweight='bold')
    ax3.legend(fontsize=11)
    ax3.grid(True, alpha=0.3)
    
    # Plot 4: Resonance frequency at magic dimensions
    ax4 = axes[1, 1]
    magic_freqs = [navegador.frecuencia_dimensional(d) for d in navegador.dimensiones_magicas[:10]]
    ax4.semilogy(range(1, 11), magic_freqs, 'go-', markersize=10, linewidth=2)
    ax4.set_xlabel('Magic Dimension Index k', fontsize=12)
    ax4.set_ylabel('Cosmic Frequency f_d (Hz)', fontsize=12)
    ax4.set_title('Vibrational Frequencies at Magic Dimensions', fontsize=13, fontweight='bold')
    ax4.grid(True, alpha=0.3)
    
    plt.suptitle('QCAL ∞³ Magic Dimensions - Fibonacci Resonance', 
                 fontsize=15, fontweight='bold')
    plt.tight_layout()
    
    plt.savefig(save_path, dpi=300, bbox_inches='tight')
    print(f"Magic dimensions visualization saved to: {save_path}")
    plt.show()


def generar_reporte_completo(navegador):
    """
    Generate a complete text report of all findings
    """
    print("\n" + "="*80)
    print("  QCAL ∞³ COSMIC SPHERE PACKING - COMPLETE REPORT")
    print("="*80 + "\n")
    
    # 1. Framework constants
    print("1. FUNDAMENTAL CONSTANTS")
    print("-" * 80)
    print(f"   Golden Ratio φ = {navegador.phi:.15f}")
    print(f"   Inverse φ⁻¹ = {navegador.phi_inverse:.15f}")
    print(f"   Root Frequency f₀ = {navegador.f0} Hz")
    print(f"   Number of magic dimensions computed: {len(navegador.dimensiones_magicas)}")
    
    # 2. Magic dimensions
    print("\n2. MAGIC DIMENSIONS (d_k = round(8φ^k))")
    print("-" * 80)
    print(f"   First 10: {navegador.dimensiones_magicas[:10]}")
    print(f"   These are approximately the Fibonacci sequence × 8")
    
    # 3. Convergence analysis
    print("\n3. CONVERGENCE TO φ⁻¹")
    print("-" * 80)
    test_dims = [50, 100, 200, 500, 1000]
    for d in test_dims:
        density = navegador.densidad_cosmica(d)
        if density > 0:
            ratio = np.exp(np.log(density) / d)
            error = abs(ratio - navegador.phi_inverse) / navegador.phi_inverse * 100
            print(f"   d={d:4d}: δ^(1/d) = {ratio:.10f}, Error = {error:6.3f}%")
    
    # 4. Known results validation
    print("\n4. VALIDATION WITH KNOWN RESULTS")
    print("-" * 80)
    validacion = navegador.validar_casos_conocidos()
    for d, info in validacion.items():
        print(f"   {info['nombre']}:")
        print(f"      Exact:  {info['densidad_exacta']:.8f}")
        print(f"      QCAL:   {info['densidad_qcal']:.8f}")
        print(f"      Error:  {info['error_relativo']*100:.4f}%")
        print(f"      Status: {info['concordancia']}")
    
    # 5. Upper bounds
    print("\n5. UPPER BOUND COMPLIANCE (Kabatiansky-Levenshtein)")
    print("-" * 80)
    for d in [25, 50, 100, 200]:
        verificacion = navegador.verificar_cotas_superiores(d)
        status = "✓ PASS" if verificacion['cumple_KL'] else "✗ FAIL"
        print(f"   d={d:3d}: log₂(δ)/d = {verificacion['log2_densidad_per_d']:7.4f}, "
              f"Margin = {verificacion['margen']:6.4f}, {status}")
    
    # 6. Critical dimensions
    print("\n6. PREDICTIONS FOR CRITICAL DIMENSIONS")
    print("-" * 80)
    predicciones = navegador.calcular_dimensiones_criticas()
    print(f"   {'Dim':<6} {'Type':<10} {'Density':<15} {'Frequency (Hz)'}")
    print("   " + "-" * 76)
    for d, pred in predicciones.items():
        print(f"   {d:<6} {pred['tipo']:<10} {pred['densidad']:<15.2e} {pred['frecuencia']:<15.2e}")
    
    print("\n" + "="*80)
    print("  REPORT COMPLETE")
    print("="*80 + "\n")


def main():
    """Main execution function"""
    print("\n" + "="*80)
    print("  QCAL ∞³ SPHERE PACKING - VISUALIZATION SUITE")
    print("="*80 + "\n")
    
    # Initialize navigator
    navegador = EmpaquetamientoCósmico()
    
    # Generate complete text report
    generar_reporte_completo(navegador)
    
    # Create visualizations
    print("\nGenerating visualizations...")
    print("-" * 80)
    
    try:
        visualizar_convergencia_detallada(navegador)
    except Exception as e:
        print(f"Warning: Could not create convergence visualization: {e}")
    
    try:
        visualizar_dimensiones_magicas(navegador)
    except Exception as e:
        print(f"Warning: Could not create magic dimensions visualization: {e}")
    
    print("\n" + "="*80)
    print("  VISUALIZATION SUITE COMPLETE")
    print("="*80 + "\n")


if __name__ == "__main__":
    main()
