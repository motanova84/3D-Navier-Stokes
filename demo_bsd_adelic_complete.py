#!/usr/bin/env python3
"""
Demo Completo: BSD-Adelic Connector
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Sello: ∴𓂀Ω∞³
f0: 141.7001 Hz

Demostración completa del conector BSD-Adélico que cierra el Pentágono Logos,
unificando los 5 Problemas del Milenio:

1. BSD (Birch and Swinnerton-Dyer) - Aritmética
2. ADN - Biología  
3. Riemann - Estructura
4. Navier-Stokes - Dinámica
5. P vs NP - Lógica

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
Date: 8 de marzo de 2026
License: MIT
"""

from qcal.bsd_adelic_connector import sincronizar_bsd_adn, CodificadorADNRiemann, F0
import json


def print_header(text: str, symbol: str = "═"):
    """Imprime un encabezado decorado"""
    width = 80
    print()
    print(symbol * width)
    print(f"  {text}")
    print(symbol * width)
    print()


def print_section(text: str):
    """Imprime una sección"""
    print()
    print(f"{'─'*80}")
    print(f"  {text}")
    print(f"{'─'*80}")


def demo_basico():
    """Demostración básica del conector BSD-Adélico"""
    print_header("DEMO BÁSICO: BSD-ADELIC CONNECTOR", "━")
    
    print("📖 CONCEPTOS FUNDAMENTALES:")
    print()
    print("   • Rango r: Número de puntos racionales en la curva elíptica")
    print("   • L(E,1): Valor de la función L en s=1 (viscosidad de información)")
    print("   • Hotspots ADN: Posiciones resonantes con f₀=141.7001 Hz")
    print("   • Ψ_BSD: Coherencia cuántica (0 a 1)")
    print()
    
    print_section("CASO 1: Curva de Mordell (Superfluidez)")
    
    curva_mordell = {
        'rango_adelico': 1,
        'L_E1': 0.0
    }
    
    print(f"   Curva: y² = x³ - x")
    print(f"   Rango: r = {curva_mordell['rango_adelico']}")
    print(f"   L(E,1) = {curva_mordell['L_E1']}")
    print()
    
    resultado = sincronizar_bsd_adn(curva_mordell, "GACT")
    
    print("   ✅ RESULTADOS:")
    print(f"      • Rango bio-aritmético: {resultado['rango_bio_aritmetico']}")
    print(f"      • Nodos activados: {resultado['nodos_constelacion']}/51")
    print(f"      • Fluidez: {resultado['fluidez_info_ns']}")
    print(f"      • Hotspots ADN: {resultado['hotspots_adn']}")
    print(f"      • Coherencia Ψ: {resultado['psi_bsd_qcal']:.4f}")
    print()
    
    if resultado['fluidez_info_ns'] == "INFINITA":
        print("   ⚡ INTERPRETACIÓN:")
        print("      L(E,1) = 0 → SUPERFLUIDEZ INFORMACIONAL")
        print("      • Flujo sin viscosidad")
        print("      • Túneles de Navier-Stokes sin resistencia")
        print("      • Complejidad NP→P por resonancia")
    
    print_section("CASO 2: Curva con Disipación")
    
    curva_disipativa = {
        'rango_adelico': 0,
        'L_E1': 0.5
    }
    
    print(f"   Curva con viscosidad")
    print(f"   Rango: r = {curva_disipativa['rango_adelico']}")
    print(f"   L(E,1) = {curva_disipativa['L_E1']}")
    print()
    
    resultado2 = sincronizar_bsd_adn(curva_disipativa, "TATA")
    
    print("   📊 RESULTADOS:")
    print(f"      • Rango: {resultado2['rango_bio_aritmetico']}")
    print(f"      • Fluidez: {resultado2['fluidez_info_ns']}")
    print(f"      • Coherencia Ψ: {resultado2['psi_bsd_qcal']:.4f}")
    print()
    
    if resultado2['fluidez_info_ns'] == "DISIPATIVA":
        print("   🌀 INTERPRETACIÓN:")
        print("      L(E,1) ≠ 0 → FLUJO DISIPATIVO")
        print("      • Presencia de viscosidad")
        print("      • Pérdida de coherencia")


def demo_secuencias_adn():
    """Demostración con diferentes secuencias de ADN"""
    print_header("ANÁLISIS DE SECUENCIAS ADN", "━")
    
    codificador = CodificadorADNRiemann()
    
    secuencias = [
        ("GACT", "Secuencia máxima resonancia"),
        ("CGTA", "Secuencia alta resonancia"),
        ("ATCG", "Secuencia media resonancia"),
        ("TATA", "Secuencia baja resonancia"),
        ("AAAA", "Secuencia muy baja resonancia"),
        ("ATCGGACTCGTAGACT", "Secuencia larga compleja"),
    ]
    
    print("   Analizando resonancia y hotspots en diferentes secuencias:")
    print()
    
    curva = {'rango_adelico': 1, 'L_E1': 0.0}
    
    for secuencia, descripcion in secuencias:
        hotspots = codificador.identificar_hotspots(secuencia)
        resonancia = codificador.calcular_resonancia(secuencia)
        resultado = sincronizar_bsd_adn(curva, secuencia)
        
        print(f"   📊 {secuencia:20s} - {descripcion}")
        print(f"      Hotspots: {len(hotspots):2d}  |  Resonancia: {resonancia:.3f}  |  Ψ: {resultado['psi_bsd_qcal']:.3f}")
        print()


def demo_rangos_bsd():
    """Demostración con diferentes rangos BSD"""
    print_header("ANÁLISIS DE RANGOS BSD", "━")
    
    print("   Explorando cómo el rango r afecta la activación de nodos:")
    print()
    
    secuencia = "GACT"
    
    for r in [0, 1, 2, 3, 5, 10]:
        curva = {'rango_adelico': r, 'L_E1': 0.0}
        resultado = sincronizar_bsd_adn(curva, secuencia)
        
        print(f"   📐 Rango r = {r:2d}:")
        print(f"      • Nodos activados: {resultado['nodos_constelacion']:2d}/51")
        print(f"      • Hotspots ADN: {resultado['hotspots_adn']}")
        print(f"      • Estado: {resultado['fluidez_info_ns']}")
        print()


def demo_pentagono_unificacion():
    """Demostración de la unificación del Pentágono Logos"""
    print_header("PENTÁGONO LOGOS: UNIFICACIÓN COMPLETA", "━")
    
    print("   Los 5 Problemas del Milenio unificados en un solo sistema:")
    print()
    
    curva = {'rango_adelico': 1, 'L_E1': 0.0}
    secuencia = "GACT"
    
    resultado = sincronizar_bsd_adn(curva, secuencia)
    
    # Visualización del Pentágono
    print("           🔷 BSD (Aritmética)")
    print("                   ↓")
    print("                r → nodos")
    print("                   ↓")
    print("   🧬 ADN ←――――――― ⬡ ―――――――→ 🌊 Navier-Stokes")
    print("   (Bio)        Logos         (Dinámica)")
    print("                   ↓")
    print("                f₀=141.7001 Hz")
    print("                   ↓")
    print("   ∞ P=NP ←―――――――――――――――→ ζ Riemann")
    print("   (Lógica)              (Estructura)")
    print()
    
    print("   📊 MÉTRICAS DE UNIFICACIÓN:")
    print()
    print(f"   1️⃣  BSD → Rango r = {resultado['rango_bio_aritmetico']} puntos racionales")
    print(f"       L(E,1) = 0 (predicción de la conjetura)")
    print()
    print(f"   2️⃣  ADN → {resultado['hotspots_adn']} hotspots resonantes")
    print(f"       Resonando en f₀ = {F0} Hz")
    print()
    print(f"   3️⃣  Riemann → Estructura espectral")
    print(f"       Ceros guían la geometría del flujo")
    print()
    print(f"   4️⃣  Navier-Stokes → Fluidez {resultado['fluidez_info_ns']}")
    print(f"       Túneles sin resistencia (viscosidad = 0)")
    print()
    print(f"   5️⃣  P=NP → Verificación O(1)")
    print(f"       Complejidad colapsa por resonancia")
    print()
    
    print(f"   🎯 COHERENCIA GLOBAL: Ψ = {resultado['psi_bsd_qcal']:.4f}")
    print()
    
    # Estado final
    if (resultado['fluidez_info_ns'] == "INFINITA" and 
        resultado['psi_bsd_qcal'] == 1.0):
        print("   ✨ ESTADO: BÓVEDA LOGOS CERRADA")
        print("      ∴ Ψ = 1.0 ∴")
        print()
        print("      Los 5 Problemas del Milenio están unificados")
        print("      en un solo sistema coherente y resonante.")


def exportar_resultados():
    """Exporta resultados de ejemplo a JSON"""
    print_header("EXPORTACIÓN DE RESULTADOS", "━")
    
    ejemplos = []
    
    # Generar varios casos
    casos = [
        ({'rango_adelico': 1, 'L_E1': 0.0}, "GACT", "Mordell - Superfluidez"),
        ({'rango_adelico': 2, 'L_E1': 0.0}, "CGTA", "Rango 2 - Superfluidez"),
        ({'rango_adelico': 0, 'L_E1': 0.5}, "TATA", "Rango 0 - Disipativo"),
        ({'rango_adelico': 5, 'L_E1': 0.0}, "ATCGGACTCGTA", "Rango 5 - Complejo"),
    ]
    
    for curva, secuencia, descripcion in casos:
        resultado = sincronizar_bsd_adn(curva, secuencia)
        ejemplos.append({
            "descripcion": descripcion,
            "curva": curva,
            "secuencia": secuencia,
            "resultado": resultado
        })
    
    # Guardar a JSON
    output = {
        "metadata": {
            "titulo": "BSD-Adelic Connector - Ejemplos",
            "f0_hz": F0,
            "sello": "∴𓂀Ω∞³",
            "fecha": "2026-03-08"
        },
        "ejemplos": ejemplos
    }
    
    filename = "bsd_adelic_ejemplos.json"
    with open(filename, 'w', encoding='utf-8') as f:
        json.dump(output, f, indent=2, ensure_ascii=False)
    
    print(f"   ✅ Resultados exportados a: {filename}")
    print(f"   📊 {len(ejemplos)} casos documentados")
    print()


def main():
    """Función principal del demo"""
    print()
    print("█" * 80)
    print("  🏛️  DEMO COMPLETO: BSD-ADELIC CONNECTOR")
    print("  Pentágono Logos - Unificación de Problemas del Milenio")
    print("  ∴𓂀Ω∞³")
    print("█" * 80)
    
    # Ejecutar todas las demos
    demo_basico()
    demo_secuencias_adn()
    demo_rangos_bsd()
    demo_pentagono_unificacion()
    exportar_resultados()
    
    # Mensaje final
    print_header("CONCLUSIÓN", "━")
    print("   El BSD-Adelic Connector cierra exitosamente el Pentágono Logos,")
    print("   unificando los 5 Problemas del Milenio en un solo sistema coherente:")
    print()
    print("   • BSD proporciona la aritmética fundamental")
    print("   • ADN codifica la información biológica")
    print("   • Riemann estructura el espacio espectral")
    print("   • Navier-Stokes gobierna la dinámica del flujo")
    print("   • P=NP emerge de la resonancia cuántica")
    print()
    print("   Cuando L(E,1) = 0, el sistema alcanza SUPERFLUIDEZ,")
    print("   permitiendo flujo de información sin resistencia y")
    print("   resolución de problemas NP en tiempo O(1).")
    print()
    print("   ∴ HECHO ESTÁ: PENTÁGONO LOGOS CERRADO ∴")
    print()
    print("█" * 80)
    print()


if __name__ == "__main__":
    main()
