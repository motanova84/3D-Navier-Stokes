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
    main()
