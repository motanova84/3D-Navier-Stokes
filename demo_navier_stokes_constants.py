#!/usr/bin/env python3
"""
Demostración del módulo navier_stokes.constants

Este script demuestra cómo usar el nuevo módulo de constantes
para calcular los parámetros del sistema Ψ-NS QCAL en diferentes medios.
"""

from navier_stokes.constants import (
    F0,
    calcular_a,
    calcular_velocidad_medio,
    calcular_defecto_desalineacion,
    calcular_coeficiente_amortiguamiento
)


def demo_constante_frecuencia():
    """Demuestra el uso de la constante F0."""
    print("=" * 70)
    print("FRECUENCIA FUNDAMENTAL QCAL")
    print("=" * 70)
    print(f"F₀ = {F0} Hz")
    print(f"Periodo T₀ = {1/F0:.6f} s")
    print(f"Frecuencia angular ω₀ = {2 * 3.14159 * F0:.2f} rad/s")
    print()


def demo_parametro_a():
    """Demuestra el cálculo del parámetro a para diferentes medios."""
    print("=" * 70)
    print("PARÁMETRO DE ACOPLAMIENTO a SEGÚN EL MEDIO")
    print("=" * 70)
    print()
    print("DERIVACIÓN: a = (2πf₀) / c")
    print("donde c es la velocidad de propagación en el medio")
    print()
    
    medios = ['vacio', 'agua', 'aire']
    print(f"{'Medio':<15} {'a':<10} {'Descripción':<40}")
    print("-" * 70)
    
    for medio in medios:
        a = calcular_a(medio)
        if medio == 'vacio':
            desc = "Régimen de baja viscosidad"
        elif medio == 'agua':
            desc = "Régimen acuático/biológico"
        else:
            desc = "Régimen atmosférico"
        print(f"{medio.capitalize():<15} {a:<10.1f} {desc:<40}")
    print()


def demo_velocidades():
    """Demuestra el cálculo de velocidades de propagación."""
    print("=" * 70)
    print("VELOCIDADES DE PROPAGACIÓN EN DIFERENTES MEDIOS")
    print("=" * 70)
    print()
    print("DERIVACIÓN INVERSA: c = (2πf₀) / a")
    print()
    
    medios = ['vacio', 'agua', 'aire']
    print(f"{'Medio':<15} {'a':<10} {'c (m/s)':<15} {'Verificación':<30}")
    print("-" * 70)
    
    for medio in medios:
        a = calcular_a(medio)
        c = calcular_velocidad_medio(a)
        # Verificar la relación inversa
        a_verificado = (2 * 3.14159265359 * F0) / c
        error = abs(a - a_verificado) / a * 100
        print(f"{medio.capitalize():<15} {a:<10.1f} {c:<15.2f} {error:<.6f}% error")
    print()


def demo_defecto_desalineacion():
    """Demuestra el cálculo del defecto de desalineación."""
    print("=" * 70)
    print("DEFECTO DE DESALINEACIÓN δ*")
    print("=" * 70)
    print()
    print("FÓRMULA: δ* = (a² c₀²) / (4π²)")
    print("con c₀ = 1.0 (gradiente de fase)")
    print()
    print("δ* mide la desalineación persistente entre vorticidad ω y deformación S")
    print()
    
    medios = ['vacio', 'agua', 'aire']
    print(f"{'Medio':<15} {'a':<10} {'δ*':<15} {'Interpretación':<30}")
    print("-" * 70)
    
    for medio in medios:
        a = calcular_a(medio)
        delta = calcular_defecto_desalineacion(a)
        if medio == 'vacio':
            interp = "Óptimo (γ > 0)"
        elif medio == 'agua':
            interp = "Marginal"
        else:
            interp = "Altamente disipativo"
        print(f"{medio.capitalize():<15} {a:<10.1f} {delta:<15.2f} {interp:<30}")
    print()


def demo_coeficiente_amortiguamiento():
    """Demuestra el cálculo del coeficiente de amortiguamiento."""
    print("=" * 70)
    print("COEFICIENTE DE AMORTIGUAMIENTO γ")
    print("=" * 70)
    print()
    print("FÓRMULA: γ = ν·c⋆ - (1 - δ*/2)·C_str")
    print("donde:")
    print("  - ν = 10⁻³ (viscosidad)")
    print("  - c⋆ = 1/16 (coercividad parabólica)")
    print("  - C_str = 32 (estiramiento de vorticidad)")
    print()
    print("CONDICIÓN DE CIERRE INCONDICIONAL: γ > 0")
    print()
    
    medios = ['vacio', 'agua', 'aire']
    print(f"{'Medio':<15} {'a':<10} {'δ*':<15} {'γ':<15} {'Cierre':<15}")
    print("-" * 70)
    
    for medio in medios:
        a = calcular_a(medio)
        delta = calcular_defecto_desalineacion(a)
        gamma = calcular_coeficiente_amortiguamiento(delta)
        cierre = "✓ Sí" if gamma > 0 else "✗ No"
        print(f"{medio.capitalize():<15} {a:<10.1f} {delta:<15.2f} {gamma:<15.6f} {cierre:<15}")
    print()


def demo_ejemplo_uso():
    """Demuestra un ejemplo de uso completo."""
    print("=" * 70)
    print("EJEMPLO DE USO COMPLETO")
    print("=" * 70)
    print()
    print("# Importar el módulo")
    print("from navier_stokes.constants import calcular_a")
    print()
    print("# Seleccionar medio de propagación")
    print("medio = 'vacio'")
    print()
    print("# Obtener parámetro a")
    print("a = calcular_a(medio)")
    print(f"# a = {calcular_a('vacio')}")
    print()
    print("# Usar en simulación Ψ-NS")
    print("# solver = PsiNSSolver(a=a, f0=F0, ...)")
    print()


def main():
    """Función principal que ejecuta todas las demostraciones."""
    print()
    print("╔" + "=" * 68 + "╗")
    print("║" + " " * 15 + "DEMOSTRACIÓN: navier_stokes.constants" + " " * 15 + "║")
    print("║" + " " * 20 + "Unificación del Parámetro a" + " " * 21 + "║")
    print("╚" + "=" * 68 + "╝")
    print()
    
    demo_constante_frecuencia()
    demo_parametro_a()
    demo_velocidades()
    demo_defecto_desalineacion()
    demo_coeficiente_amortiguamiento()
    demo_ejemplo_uso()
    
    print("=" * 70)
    print("CONCLUSIÓN")
    print("=" * 70)
    print()
    print("El parámetro a NO es arbitrario. Depende del medio de propagación:")
    print()
    print("  • Vacío (a=8.9):  Validaciones teóricas, cierre incondicional")
    print("  • Agua (a=7.0):   Aplicaciones biológicas (flujo citoplasmático)")
    print("  • Aire (a=200):   Aplicaciones atmosféricas (DNS turbulento)")
    print()
    print("La inconsistencia reportada correspondía a usar diferentes medios")
    print("en diferentes contextos. Este módulo unifica la definición.")
    print()
    print("=" * 70)
    print()


if __name__ == '__main__':
    main()
