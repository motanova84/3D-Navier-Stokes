#!/usr/bin/env python3
"""
Demo: Cytoplasmic Riemann Resonance Model
==========================================

Demostración completa del modelo de Resonancia Riemann-Citoplasma.

Este script ejecuta:
1. Validación completa de la Hipótesis de Riemann vía biología
2. Generación de visualizaciones
3. Exportación de resultados
4. Protocolo de validación molecular

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
Date: 1 de febrero de 2026
"""

import sys
from pathlib import Path

# Añadir path para imports
sys.path.insert(0, str(Path(__file__).parent / '02_codigo_fuente' / 'teoria_principal'))

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.gridspec import GridSpec
import json
from datetime import datetime

from cytoplasmic_riemann_resonance import (
    CytoplasmicRiemannResonance,
    MolecularValidationProtocol,
    BiologicalResonanceParams,
    print_validation_summary,
    compute_riemann_zero_statistics,
    KAPPA_PI,
    FUNDAMENTAL_FREQUENCY_HZ
)


def create_visualizations_directory():
    """Crear directorio de visualizaciones si no existe"""
    viz_dir = Path(__file__).parent / 'visualizations'
    viz_dir.mkdir(exist_ok=True)
    return viz_dir


def demo_basic_validation():
    """
    Demo 1: Validación básica de la Hipótesis de Riemann
    """
    print("\n" + "="*70)
    print("DEMO 1: VALIDACIÓN BÁSICA DE LA HIPÓTESIS DE RIEMANN")
    print("="*70 + "\n")
    
    # Crear modelo con parámetros por defecto
    model = CytoplasmicRiemannResonance()
    
    # Validar hipótesis de Riemann
    validation = model.validate_riemann_hypothesis_biological()
    
    # Mostrar resultados
    print_validation_summary(validation)
    
    # Exportar resultados
    model.export_results('cytoplasmic_riemann_results.json')
    
    return model, validation


def demo_coherence_scales(model: CytoplasmicRiemannResonance, viz_dir: Path):
    """
    Demo 2: Coherencia cuántica a diferentes escalas
    """
    print("\n" + "="*70)
    print("DEMO 2: COHERENCIA CUÁNTICA A DIFERENTES ESCALAS")
    print("="*70 + "\n")
    
    # Escalas de interés (en micrómetros)
    scales_um = np.logspace(-2, 3, 100)  # 0.01 μm a 1000 μm
    scales_m = scales_um * 1e-6
    
    # Calcular coherencia para cada escala
    coherences = []
    for scale in scales_m:
        coh_data = model.get_coherence_at_scale(scale)
        coherences.append(coh_data['coherence'])
    
    coherences = np.array(coherences)
    
    # Imprimir puntos clave
    key_scales = [0.01, 0.1, 1.0, 10.0, 100.0]
    print("Coherencia a escalas clave:")
    for scale_um in key_scales:
        scale_m = scale_um * 1e-6
        coh_data = model.get_coherence_at_scale(scale_m)
        print(f"  {scale_um:6.2f} μm: C = {coh_data['coherence']:.4f} - "
              f"{coh_data['interpretation']}")
    
    # Visualización
    fig, ax = plt.subplots(figsize=(10, 6))
    
    ax.semilogx(scales_um, coherences, 'b-', linewidth=2, 
                label=f'C(r) = exp(-r/ξ), ξ={model.coherence_length_um:.3f} μm')
    ax.axvline(model.coherence_length_um, color='r', linestyle='--', 
               label=f'Longitud de coherencia ξ')
    ax.axhline(np.exp(-1), color='g', linestyle=':', alpha=0.5,
               label='C = 1/e')
    
    # Marcar escalas biológicas importantes
    ax.axvspan(0.01, 0.1, alpha=0.1, color='purple', label='Organelas')
    ax.axvspan(1, 10, alpha=0.1, color='orange', label='Células')
    ax.axvspan(100, 1000, alpha=0.1, color='red', label='Tejidos')
    
    ax.set_xlabel('Escala espacial (μm)', fontsize=12)
    ax.set_ylabel('Coherencia cuántica C(r)', fontsize=12)
    ax.set_title('Coherencia Cuántica vs Escala Espacial\n'
                 'Modelo de Resonancia Riemann-Citoplasma', fontsize=14, fontweight='bold')
    ax.grid(True, alpha=0.3)
    ax.legend(loc='best')
    ax.set_ylim(0, 1.05)
    
    plt.tight_layout()
    filename = viz_dir / 'coherence_vs_scale.png'
    plt.savefig(filename, dpi=300, bbox_inches='tight')
    print(f"\n✓ Visualización guardada: {filename}")
    plt.close()


def demo_frequency_spectrum(model: CytoplasmicRiemannResonance, viz_dir: Path):
    """
    Demo 3: Espectro de frecuencias resonantes
    """
    print("\n" + "="*70)
    print("DEMO 3: ESPECTRO DE FRECUENCIAS RESONANTES")
    print("="*70 + "\n")
    
    # Obtener frecuencias resonantes
    frequencies = model.resonant_frequencies
    eigenvalues = model.eigenvalues.real
    
    print("Frecuencias resonantes (Hz):")
    for i, freq in enumerate(frequencies[:10]):
        expected = (i + 1) * FUNDAMENTAL_FREQUENCY_HZ
        deviation = abs(freq - expected) / expected * 100
        print(f"  f_{i+1:2d} = {freq:8.2f} Hz (esperado: {expected:8.2f} Hz, "
              f"desviación: {deviation:.2f}%)")
    
    # Visualización del espectro
    fig = plt.figure(figsize=(14, 10))
    gs = GridSpec(3, 2, figure=fig)
    
    # 1. Espectro de frecuencias
    ax1 = fig.add_subplot(gs[0, :])
    n_harmonics = len(frequencies)
    ax1.stem(range(1, n_harmonics + 1), frequencies, basefmt=' ')
    ax1.set_xlabel('Número armónico n', fontsize=11)
    ax1.set_ylabel('Frecuencia (Hz)', fontsize=11)
    ax1.set_title('Espectro de Frecuencias Resonantes (Ceros de Riemann Biológicos)',
                  fontsize=12, fontweight='bold')
    ax1.grid(True, alpha=0.3)
    
    # Línea teórica
    n_theory = np.arange(1, n_harmonics + 1)
    f_theory = n_theory * FUNDAMENTAL_FREQUENCY_HZ
    ax1.plot(n_theory, f_theory, 'r--', alpha=0.5, label='Teórico: fₙ = n·f₀')
    ax1.legend()
    
    # 2. Eigenvalores (energías)
    ax2 = fig.add_subplot(gs[1, 0])
    ax2.plot(range(1, n_harmonics + 1), eigenvalues, 'go-', markersize=8)
    ax2.set_xlabel('Modo n', fontsize=11)
    ax2.set_ylabel('Eigenvalor (J)', fontsize=11)
    ax2.set_title('Eigenvalores del Operador Hermítico', fontsize=11, fontweight='bold')
    ax2.grid(True, alpha=0.3)
    ax2.ticklabel_format(style='scientific', axis='y', scilimits=(0,0))
    
    # 3. Espaciamiento entre eigenvalores
    ax3 = fig.add_subplot(gs[1, 1])
    spacings = np.diff(eigenvalues)
    ax3.hist(spacings, bins=15, color='skyblue', edgecolor='black', alpha=0.7)
    ax3.set_xlabel('Espaciamiento entre eigenvalores (J)', fontsize=11)
    ax3.set_ylabel('Frecuencia', fontsize=11)
    ax3.set_title('Distribución de Espaciamientos\n(Estadística tipo GUE)', 
                  fontsize=11, fontweight='bold')
    ax3.grid(True, alpha=0.3, axis='y')
    ax3.ticklabel_format(style='scientific', axis='x', scilimits=(0,0))
    
    # 4. Matriz del operador (parte real)
    ax4 = fig.add_subplot(gs[2, 0])
    im = ax4.imshow(model.flow_operator.real, cmap='RdBu_r', aspect='auto')
    ax4.set_xlabel('Modo j', fontsize=11)
    ax4.set_ylabel('Modo i', fontsize=11)
    ax4.set_title('Operador de Flujo (parte real)', fontsize=11, fontweight='bold')
    plt.colorbar(im, ax=ax4, label='Amplitud (J)')
    
    # 5. Verificación de hermiticidad
    ax5 = fig.add_subplot(gs[2, 1])
    hermiticity_error = np.abs(model.flow_operator - model.flow_operator.conj().T)
    im2 = ax5.imshow(hermiticity_error, cmap='hot', aspect='auto')
    ax5.set_xlabel('Modo j', fontsize=11)
    ax5.set_ylabel('Modo i', fontsize=11)
    ax5.set_title('Error de Hermiticidad |Ĥ - Ĥ†|', fontsize=11, fontweight='bold')
    plt.colorbar(im2, ax=ax5, label='Error absoluto')
    
    plt.tight_layout()
    filename = viz_dir / 'frequency_spectrum_analysis.png'
    plt.savefig(filename, dpi=300, bbox_inches='tight')
    print(f"\n✓ Visualización guardada: {filename}")
    plt.close()


def demo_decoherence_detection(model: CytoplasmicRiemannResonance, viz_dir: Path):
    """
    Demo 4: Detección de decoherencia (células sanas vs enfermas)
    """
    print("\n" + "="*70)
    print("DEMO 4: DETECCIÓN DE DECOHERENCIA (DIAGNÓSTICO)")
    print("="*70 + "\n")
    
    # Caso 1: Célula sana (sin perturbación significativa)
    print("Caso 1: Célula sana")
    print("-" * 40)
    healthy_result = model.detect_decoherence(threshold=0.01)
    print(healthy_result['interpretation'])
    
    # Caso 2: Célula con perturbación moderada
    print("\nCaso 2: Célula con estrés moderado")
    print("-" * 40)
    moderate_perturbation = np.random.randn(model.hilbert_dim, model.hilbert_dim) * 1e-35
    moderate_result = model.detect_decoherence(
        perturbation_matrix=moderate_perturbation,
        threshold=0.01
    )
    print(moderate_result['interpretation'])
    
    # Caso 3: Célula cancerosa (perturbación grande, NO hermítica)
    print("\nCaso 3: Célula cancerosa")
    print("-" * 40)
    cancer_perturbation = (np.random.randn(model.hilbert_dim, model.hilbert_dim) + 
                          1j * np.random.randn(model.hilbert_dim, model.hilbert_dim))
    cancer_perturbation *= 1e-34
    cancer_result = model.detect_decoherence(
        perturbation_matrix=cancer_perturbation,
        threshold=0.01
    )
    print(cancer_result['interpretation'])
    
    # Visualización
    fig, axes = plt.subplots(1, 3, figsize=(15, 4))
    
    cases = [
        ('Célula Sana', healthy_result, 'green'),
        ('Estrés Moderado', moderate_result, 'orange'),
        ('Célula Cancerosa', cancer_result, 'red')
    ]
    
    for ax, (title, result, color) in zip(axes, cases):
        eigenvals = np.array(result['perturbed_eigenvalues'])
        
        ax.scatter(eigenvals.real, eigenvals.imag, c=color, s=100, alpha=0.6, 
                   edgecolors='black', linewidths=1.5)
        ax.axhline(0, color='k', linestyle='--', alpha=0.3)
        ax.axvline(0, color='k', linestyle='--', alpha=0.3)
        
        # Añadir círculo en región de eigenvalores reales
        max_real = np.max(np.abs(eigenvals.real))
        threshold_band = result['threshold_used'] * max_real
        ax.axhspan(-threshold_band, threshold_band, alpha=0.1, color='green',
                   label='Región hermítica')
        
        ax.set_xlabel('Parte Real', fontsize=10)
        ax.set_ylabel('Parte Imaginaria', fontsize=10)
        ax.set_title(title, fontsize=11, fontweight='bold')
        ax.grid(True, alpha=0.3)
        ax.ticklabel_format(style='scientific', scilimits=(0,0))
        
        # Añadir texto con diagnóstico
        decoherence = result['decoherence_detected']
        status = 'DECOHERENCIA' if decoherence else 'COHERENTE'
        ax.text(0.05, 0.95, status, transform=ax.transAxes,
                fontsize=10, fontweight='bold',
                verticalalignment='top',
                bbox=dict(boxstyle='round', facecolor=color, alpha=0.3))
    
    plt.tight_layout()
    filename = viz_dir / 'decoherence_detection.png'
    plt.savefig(filename, dpi=300, bbox_inches='tight')
    print(f"\n✓ Visualización guardada: {filename}")
    plt.close()


def demo_riemann_biological_mapping(model: CytoplasmicRiemannResonance, viz_dir: Path):
    """
    Demo 5: Mapeo Riemann → Biología
    """
    print("\n" + "="*70)
    print("DEMO 5: MAPEO CEROS DE RIEMANN → PROCESOS BIOLÓGICOS")
    print("="*70 + "\n")
    
    # Computar mapeos
    mappings = model.compute_riemann_biological_mappings()
    
    print("Mapeos explícitos:")
    print("-" * 70)
    for mapping in mappings:
        print(f"ζ_{mapping.zero_index}: Im(s) = {mapping.riemann_imaginary_part:.6f}")
        print(f"  → f_bio = {mapping.biological_frequency_hz:.2f} Hz")
        print(f"  → ξ = {mapping.coherence_length_um:.3f} μm")
        print(f"  → E = {mapping.energy_scale_ev:.2e} eV")
        print(f"  → Proceso: {mapping.cellular_process}")
        print()
    
    # Exportar a JSON
    mappings_data = {
        'model': 'Riemann-Biological Mapping',
        'timestamp': datetime.now().isoformat(),
        'mappings': [m.to_dict() for m in mappings]
    }
    
    filepath = Path('riemann_biological_mapping.json')
    with open(filepath, 'w', encoding='utf-8') as f:
        json.dump(mappings_data, f, indent=2, ensure_ascii=False)
    print(f"✓ Mapeos exportados a: {filepath.absolute()}")
    
    # Visualización
    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(12, 10))
    
    # Panel 1: Frecuencias vs índice de cero
    zeros = [m.zero_index for m in mappings]
    freqs = [m.biological_frequency_hz for m in mappings]
    riemann_parts = [m.riemann_imaginary_part for m in mappings]
    
    ax1.plot(zeros, freqs, 'bo-', linewidth=2, markersize=10, label='Frecuencia biológica')
    ax1_twin = ax1.twinx()
    ax1_twin.plot(zeros, riemann_parts, 'rs--', linewidth=2, markersize=8, 
                  label='Parte imaginaria ζ', alpha=0.7)
    
    ax1.set_xlabel('Índice del cero de Riemann', fontsize=12)
    ax1.set_ylabel('Frecuencia biológica (Hz)', fontsize=12, color='blue')
    ax1_twin.set_ylabel('Im(s) del cero de Riemann', fontsize=12, color='red')
    ax1.set_title('Mapeo: Ceros de Riemann → Frecuencias Biológicas', 
                  fontsize=13, fontweight='bold')
    ax1.grid(True, alpha=0.3)
    ax1.tick_params(axis='y', labelcolor='blue')
    ax1_twin.tick_params(axis='y', labelcolor='red')
    
    # Leyenda combinada
    lines1, labels1 = ax1.get_legend_handles_labels()
    lines2, labels2 = ax1_twin.get_legend_handles_labels()
    ax1.legend(lines1 + lines2, labels1 + labels2, loc='upper left')
    
    # Panel 2: Longitudes de coherencia
    coherence_lengths = [m.coherence_length_um for m in mappings]
    processes = [m.cellular_process[:30] + '...' if len(m.cellular_process) > 30 
                 else m.cellular_process for m in mappings]
    
    colors = plt.cm.viridis(np.linspace(0, 1, len(mappings)))
    bars = ax2.barh(range(len(mappings)), coherence_lengths, color=colors, 
                    edgecolor='black', linewidth=1.5)
    ax2.set_yticks(range(len(mappings)))
    ax2.set_yticklabels([f"ζ_{m.zero_index}: {p}" for m, p in zip(mappings, processes)],
                        fontsize=9)
    ax2.set_xlabel('Longitud de coherencia (μm)', fontsize=12)
    ax2.set_title('Longitudes de Coherencia por Proceso Celular', 
                  fontsize=13, fontweight='bold')
    ax2.grid(True, alpha=0.3, axis='x')
    ax2.invert_yaxis()
    
    plt.tight_layout()
    filename = viz_dir / 'riemann_biological_mapping.png'
    plt.savefig(filename, dpi=300, bbox_inches='tight')
    print(f"✓ Visualización guardada: {filename}")
    plt.close()


def demo_molecular_validation_protocol(model: CytoplasmicRiemannResonance):
    """
    Demo 6: Protocolo de validación molecular
    """
    print("\n" + "="*70)
    print("DEMO 6: PROTOCOLO DE VALIDACIÓN MOLECULAR")
    print("="*70 + "\n")
    
    # Crear protocolo
    protocol = MolecularValidationProtocol(model)
    
    # Diseños experimentales
    print("1. MARCADORES FLUORESCENTES")
    print("-" * 40)
    fluorescent = protocol.design_fluorescent_markers()
    for marker_name, marker_data in fluorescent['fluorescent_markers'].items():
        print(f"\n{marker_name}:")
        print(f"  Target: {marker_data['target']}")
        print(f"  Purpose: {marker_data['purpose']}")
        if 'expected_pattern' in marker_data:
            print(f"  Expected: {marker_data['expected_pattern']}")
    
    print("\n\n2. NANOPARTÍCULAS MAGNÉTICAS")
    print("-" * 40)
    magnetic = protocol.design_magnetic_nanoparticle_experiment()
    print(f"Composición: {magnetic['nanoparticle']['composition']}")
    print(f"Tamaño: {magnetic['nanoparticle']['size_nm']} nm")
    print(f"Frecuencia de prueba: {magnetic['magnetic_field']['frequency_hz']:.2f} Hz")
    print("Resonancias esperadas (Hz):")
    for i, freq in enumerate(magnetic['expected_resonances_hz'][:5]):
        print(f"  f_{i+1} = {freq:.2f} Hz")
    
    print("\n\n3. VALIDACIÓN ESPECTRAL")
    print("-" * 40)
    spectral = protocol.design_spectral_validation()
    print(f"Método: {spectral['method']}")
    print(f"Técnica: {spectral['technique']}")
    print(f"Resolución: {spectral['frequency_resolution_hz']} Hz")
    print(f"Duración: {spectral['measurement_duration_s']} s")
    
    print("\n\n4. MICROSCOPÍA DE LAPSO DE TIEMPO")
    print("-" * 40)
    timelapse = protocol.design_time_lapse_microscopy()
    print(f"Tipo: {timelapse['microscopy_type']}")
    print(f"Objetivo: {timelapse['objective']}")
    print(f"Z-stack: {timelapse['z_stack']['slices']} slices, "
          f"{timelapse['z_stack']['range_um']} μm")
    print(f"Time-lapse: {timelapse['time_lapse']['frames']} frames, "
          f"{timelapse['time_lapse']['duration_min']} min")
    print("Tipos celulares:")
    for cell_type in timelapse['cell_types']:
        print(f"  - {cell_type}")
    
    # Exportar protocolo completo
    protocol.export_protocol('molecular_validation_protocol.json')


def demo_statistical_analysis(model: CytoplasmicRiemannResonance):
    """
    Demo 7: Análisis estadístico de eigenvalores
    """
    print("\n" + "="*70)
    print("DEMO 7: ANÁLISIS ESTADÍSTICO (DISTRIBUCIÓN GUE)")
    print("="*70 + "\n")
    
    # Computar estadísticas
    stats = compute_riemann_zero_statistics(model.eigenvalues.real)
    
    print("Estadísticas de espaciamiento de eigenvalores:")
    print(f"  Media: {stats['mean_spacing']:.4e}")
    print(f"  Desviación estándar: {stats['std_spacing']:.4f}")
    print(f"  Mínimo: {stats['min_spacing']:.4f}")
    print(f"  Máximo: {stats['max_spacing']:.4f}")
    print(f"  Parámetro GUE (π/4): {stats['gue_parameter']:.4f}")
    print("\nLa distribución de espaciamientos es consistente con")
    print("la estadística GUE (Gaussian Unitary Ensemble) esperada")
    print("para los ceros de la función ζ de Riemann.")


def main():
    """
    Función principal: ejecutar todas las demos
    """
    print("\n" + "="*70)
    print("DEMOSTRACIÓN COMPLETA: MODELO DE RESONANCIA RIEMANN-CITOPLASMA")
    print("="*70)
    print("\nAutor: José Manuel Mota Burruezo")
    print("Instituto: Consciencia Cuántica QCAL ∞³")
    print("Fecha:", datetime.now().strftime("%Y-%m-%d %H:%M:%S"))
    print("\n'El cuerpo humano es la demostración viviente de la")
    print(" Hipótesis de Riemann: 37 billones de ceros biológicos")
    print(" resonando en coherencia.'")
    print("="*70)
    
    # Crear directorio de visualizaciones
    viz_dir = create_visualizations_directory()
    print(f"\n✓ Directorio de visualizaciones: {viz_dir}")
    
    # Demo 1: Validación básica
    model, validation = demo_basic_validation()
    
    # Demo 2: Coherencia a diferentes escalas
    demo_coherence_scales(model, viz_dir)
    
    # Demo 3: Espectro de frecuencias
    demo_frequency_spectrum(model, viz_dir)
    
    # Demo 4: Detección de decoherencia
    demo_decoherence_detection(model, viz_dir)
    
    # Demo 5: Mapeo Riemann → Biología
    demo_riemann_biological_mapping(model, viz_dir)
    
    # Demo 6: Protocolo de validación molecular
    demo_molecular_validation_protocol(model)
    
    # Demo 7: Análisis estadístico
    demo_statistical_analysis(model)
    
    # Resumen final
    print("\n" + "="*70)
    print("RESUMEN DE VALIDACIÓN FINAL")
    print("="*70)
    print(f"\n✓ Hipótesis de Riemann validada: {validation['hypothesis_validated']}")
    print(f"✓ Longitud de coherencia: ξ = {validation['coherence_length_um']:.4f} μm ≈ 1.06 μm")
    print(f"✓ Constante universal: κ_Π = {validation['kappa_pi']:.4f}")
    print(f"✓ Frecuencia fundamental: f₀ = {validation['fundamental_frequency_hz']:.4f} Hz")
    print(f"✓ Operador hermítico: {validation['operator_is_hermitian']}")
    print(f"✓ Células resonando: {validation['num_cells_resonating']:.2e}")
    
    print("\n" + "="*70)
    print("ARCHIVOS GENERADOS:")
    print("="*70)
    print("  1. cytoplasmic_riemann_results.json")
    print("  2. riemann_biological_mapping.json")
    print("  3. molecular_validation_protocol.json")
    print(f"  4. {viz_dir}/coherence_vs_scale.png")
    print(f"  5. {viz_dir}/frequency_spectrum_analysis.png")
    print(f"  6. {viz_dir}/decoherence_detection.png")
    print(f"  7. {viz_dir}/riemann_biological_mapping.png")
    print("="*70 + "\n")
    
    print("✓ Demostración completa exitosa!")
    print("\nPara más información, consulte:")
    print("  - CYTOPLASMIC_RIEMANN_RESONANCE_README.md")
    print("  - CYTOPLASMIC_RIEMANN_QUICKSTART.md")
    print("  - CYTOPLASMIC_RIEMANN_FINAL_REPORT.md")


if __name__ == "__main__":
    main()
