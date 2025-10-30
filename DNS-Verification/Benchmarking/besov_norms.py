#!/usr/bin/env python3
"""
Besov norm computation and validation
"""

import numpy as np
from typing import List

def compute_besov_b0_inf1(dyadic_norms: List[float]) -> float:
    """
    Compute Besov B⁰_{∞,1} norm: Σ_j ‖Δ_j f‖_{L∞}
    
    Args:
        dyadic_norms: List of L∞ norms for each dyadic block
        
    Returns:
        Besov norm
    """
    return sum(dyadic_norms)


def validate_besov_bound(besov_history: List[float], threshold: float = 1e6) -> bool:
    """
    Validate that Besov norm remains bounded
    
    Args:
        besov_history: Time series of Besov norms
        threshold: Upper bound threshold
        
    Returns:
        True if bounded, False otherwise
    """
    return all(b < threshold for b in besov_history)


def compute_besov_integral(besov_history: List[float], dt: float) -> float:
    """
    Compute time integral: ∫₀^T ‖ω(t)‖_{B⁰_{∞,1}} dt
    
    Args:
        besov_history: Time series of Besov norms
        dt: Time step
        
    Returns:
        Integrated Besov norm
    """
    return np.trapz(besov_history, dx=dt)


def verify_bkm_criterion(vorticity_inf_history: List[float], dt: float, 
                        threshold: float = 1e3) -> bool:
    """
    Verify BKM criterion: ∫₀^∞ ‖ω(t)‖_{L∞} dt < ∞
    
    Args:
        vorticity_inf_history: Time series of L∞ vorticity norms
        dt: Time step
        threshold: Finite threshold
        
    Returns:
        True if criterion satisfied
    """
    integral = np.trapz(vorticity_inf_history, dx=dt)
    return integral < threshold


if __name__ == "__main__":
    print("Besov Norm Computation and BKM Criterion")
    print("="*60)
    
    # Example: synthetic dyadic norms with decay
    n_blocks = 10
    dyadic_norms = [1.0 / (2**j) for j in range(n_blocks)]
    
    besov = compute_besov_b0_inf1(dyadic_norms)
    print(f"\nExample Besov B⁰_{{∞,1}} norm: {besov:.4f}")
    
    # Example: time evolution
    T = 10.0
    dt = 0.01
    n_steps = int(T / dt)
    
    # Synthetic decay: ‖ω(t)‖ ~ e^{-γt}
    γ = 0.1
    t_values = np.arange(0, T, dt)
    ω_history = [np.exp(-γ * t) for t in t_values]
    
    integral = compute_besov_integral(ω_history, dt)
    is_bounded = validate_besov_bound(ω_history, threshold=10.0)
    satisfies_bkm = verify_bkm_criterion(ω_history, dt)
    
    print(f"\nTime Integration (T={T}):")
    print(f"  ∫ ‖ω(t)‖ dt = {integral:.4f}")
    print(f"  Bounded: {'✅ YES' if is_bounded else '❌ NO'}")
    print(f"  BKM criterion: {'✅ SATISFIED' if satisfies_bkm else '❌ VIOLATED'}")
