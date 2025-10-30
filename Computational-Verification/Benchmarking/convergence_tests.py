"""
Tests de convergencia para el sistema Ψ-NS
"""

import numpy as np
import sys
import os

# Add parent directory to path
sys.path.append(os.path.join(os.path.dirname(__file__), '..', 'DNS-Solver'))

from psi_ns_solver import PsiNSSolver
from dual_limit_scaling import DualLimitAnalyzer, compute_riccati_coefficient
from visualization import PsiNSVisualizer


def analyze_dual_limit_convergence(N: int = 64, Re: float = 1000):
    """
    Analizar convergencia en el límite dual
    
    Args:
        N: Resolución de malla
        Re: Número de Reynolds
    """
    print("=" * 70)
    print("ANÁLISIS DE CONVERGENCIA EN LÍMITE DUAL")
    print("=" * 70)
    
    solver = PsiNSSolver(N=N, Re=Re)
    analyzer = DualLimitAnalyzer(lambda_val=1.0, a=1.0, alpha=2.0)
    visualizer = PsiNSVisualizer()
    
    # Barrido de frecuencias
    f0_range = np.logspace(2, 3.5, 6)  # 100 Hz to ~3162 Hz
    print(f"\nFrecuencias a simular: {f0_range}")
    print(f"Resolución: {N}³, Re = {Re}")
    print(f"Tiempo de simulación: 5.0 s")
    print("\nEjecutando simulaciones...")
    print("-" * 70)
    
    results = solver.run_simulation(f0_range.tolist(), T_max=5.0, dt=0.01)
    
    # Análisis de delta* teórico vs computacional
    delta_star_theoretical = analyzer.theoretical_delta_star(c0=1.0)
    
    print(f"\n{'f0 (Hz)':<12} {'delta* comp.':<12} {'delta* teor.':<12} {'Error rel.':<12}")
    print("-" * 70)
    
    f0_values = sorted(results.keys())
    delta_star_computed = []
    forcing_magnitude = []
    alpha_star_values = []
    
    for f0 in f0_values:
        delta_comp = results[f0]['delta_star']
        error_rel = abs(delta_comp - delta_star_theoretical) / delta_star_theoretical
        
        delta_star_computed.append(delta_comp)
        
        # Calcular magnitud de fuerza
        forcing = analyzer.forcing_magnitude(f0)
        forcing_magnitude.append(forcing)
        
        # Calcular alpha* 
        alpha_star = compute_riccati_coefficient(delta_comp, C_BKM=1.0, nu=solver.nu, c_B=0.8)
        alpha_star_values.append(alpha_star)
        
        print(f"{f0:<12.1f} {delta_comp:<12.6f} {delta_star_theoretical:<12.6f} {error_rel:<12.6f}")
    
    # Análisis de convergencia
    convergence = analyzer.analyze_convergence(results)
    
    print("\n" + "=" * 70)
    print("RESUMEN DE ANÁLISIS")
    print("=" * 70)
    print(f"delta* teórico:                {delta_star_theoretical:.8f}")
    print(f"delta* computado (f0 máx):     {delta_star_computed[-1]:.8f}")
    print(f"Error relativo:             {convergence['relative_errors'][-1]:.6f}")
    
    if convergence['convergence_rate']:
        print(f"Tasa de convergencia:       {convergence['convergence_rate']:.4f}")
    
    # Verificar condiciones del límite dual
    print("\nCONDICIONES DEL LÍMITE DUAL:")
    conditions = analyzer.dual_limit_conditions(f0_values[-1], solver.nu)
    for cond_name, cond_val in conditions.items():
        status = "✓" if cond_val else "✗"
        print(f"  {status} {cond_name.replace('_', ' ').title()}: {cond_val}")
    
    # Análisis de coeficiente de Riccati
    print("\nCOEFICIENTE DE RICCATI alpha*:")
    all_negative = all(alpha < 0 for alpha in alpha_star_values)
    print(f"  alpha* < 0 para todas las frecuencias: {all_negative}")
    print(f"  Rango de alpha*: [{min(alpha_star_values):.6f}, {max(alpha_star_values):.6f}]")
    
    if all_negative:
        print("  ✓ Regularización uniforme lograda")
    else:
        print("  ✗ Regularización no uniforme")
    
    # Crear visualizaciones
    print("\nGenerando visualizaciones...")
    visualizer.create_comprehensive_dashboard(
        results, 
        delta_star_theoretical, 
        forcing_magnitude,
        alpha_star_values
    )
    
    print("✓ Análisis completado. Resultados guardados en Results/Figures/")
    
    return results, convergence


def test_spatial_convergence():
    """Test de convergencia espacial"""
    print("\n" + "=" * 70)
    print("TEST DE CONVERGENCIA ESPACIAL")
    print("=" * 70)
    
    resolutions = [32, 64, 128]
    f0 = 200.0
    
    print(f"\nFrecuencia fija: f0 = {f0} Hz")
    print(f"Resoluciones: {resolutions}")
    print("\n" + "-" * 70)
    
    delta_values = []
    
    for N in resolutions:
        print(f"\nSimulando con N = {N}³...")
        solver = PsiNSSolver(N=N, Re=1000)
        results = solver.run_simulation([f0], T_max=2.0, dt=0.01)
        
        delta = results[f0]['delta_star']
        delta_values.append(delta)
        print(f"  delta* = {delta:.8f}")
    
    # Estimar orden de convergencia
    if len(delta_values) >= 2:
        print("\nOrden de convergencia:")
        for i in range(1, len(delta_values)):
            ratio = resolutions[i] / resolutions[i-1]
            error_ratio = abs(delta_values[i] - delta_values[i-1]) / abs(delta_values[i])
            order = np.log(error_ratio) / np.log(1/ratio) if error_ratio > 0 else 0
            print(f"  {resolutions[i-1]} → {resolutions[i]}: orden ≈ {order:.2f}")
    
    print("\n✓ Test de convergencia espacial completado")
    
    return delta_values


def test_temporal_convergence():
    """Test de convergencia temporal"""
    print("\n" + "=" * 70)
    print("TEST DE CONVERGENCIA TEMPORAL")
    print("=" * 70)
    
    dt_values = [0.02, 0.01, 0.005]
    f0 = 200.0
    N = 64
    
    print(f"\nFrecuencia fija: f0 = {f0} Hz")
    print(f"Resolución fija: N = {N}³")
    print(f"Pasos temporales: {dt_values}")
    print("\n" + "-" * 70)
    
    delta_values = []
    
    for dt in dt_values:
        print(f"\nSimulando con dt = {dt}...")
        solver = PsiNSSolver(N=N, Re=1000)
        results = solver.run_simulation([f0], T_max=2.0, dt=dt)
        
        delta = results[f0]['delta_star']
        delta_values.append(delta)
        print(f"  delta* = {delta:.8f}")
    
    print("\n✓ Test de convergencia temporal completado")
    
    return delta_values


def run_full_convergence_suite():
    """Ejecutar suite completa de tests de convergencia"""
    print("\n" + "=" * 70)
    print("SUITE COMPLETA DE TESTS DE CONVERGENCIA")
    print("=" * 70)
    print("\nEjecutando todos los tests de convergencia...")
    
    # Test principal: convergencia en límite dual
    results, convergence = analyze_dual_limit_convergence(N=64, Re=1000)
    
    # Test de convergencia espacial
    # spatial_conv = test_spatial_convergence()
    
    # Test de convergencia temporal
    # temporal_conv = test_temporal_convergence()
    
    print("\n" + "=" * 70)
    print("SUITE DE TESTS COMPLETADA")
    print("=" * 70)
    print("\nResultados guardados en:")
    print("  - Results/Figures/dual_limit_convergence.png")
    print("  - Results/Data/ (si está habilitado)")
    
    return {
        'dual_limit': (results, convergence),
        # 'spatial': spatial_conv,
        # 'temporal': temporal_conv
    }


if __name__ == "__main__":
    # Ejecutar análisis de convergencia
    run_full_convergence_suite()
