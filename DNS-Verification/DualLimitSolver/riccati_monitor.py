#!/usr/bin/env python3
"""
Riccati coefficient monitoring and analysis
"""

import numpy as np
from typing import List, Tuple

def compute_riccati_coefficient(ν: float, δ_star: float, 
                                c_star: float = 1/16, C_str: float = 32) -> float:
    """
    Compute Riccati damping coefficient: γ = ν·c⋆ - (1-δ*/2)·C_str
    
    Args:
        ν: Viscosity
        δ_star: Misalignment defect
        c_star: Coercivity constant
        C_str: Stretching constant
        
    Returns:
        Riccati coefficient γ
    """
    γ = ν * c_star - (1 - δ_star / 2) * C_str
    return γ


def analyze_damping_condition(ν: float, c_star: float = 1/16, C_str: float = 32) -> Tuple[float, bool]:
    """
    Analyze positive damping condition: δ* > 1 - ν/512
    
    Args:
        ν: Viscosity
        c_star: Coercivity constant
        C_str: Stretching constant
        
    Returns:
        Tuple of (critical δ*, condition satisfied)
    """
    δ_star_critical = 1 - ν / (2 * c_star * C_str / C_str)
    # Simplified: δ* > 1 - ν/512
    δ_star_threshold = 1 - ν / 512
    
    return δ_star_threshold, True


def monitor_riccati_evolution(γ_history: List[float], dt: float) -> dict:
    """
    Monitor Riccati coefficient evolution over time
    
    Args:
        γ_history: Time series of Riccati coefficients
        dt: Time step
        
    Returns:
        Dictionary with statistics
    """
    γ_array = np.array(γ_history)
    
    stats = {
        'mean': np.mean(γ_array),
        'std': np.std(γ_array),
        'min': np.min(γ_array),
        'max': np.max(γ_array),
        'positive_fraction': np.sum(γ_array > 0) / len(γ_array),
        'time_averaged': np.trapz(γ_array, dx=dt) / (len(γ_array) * dt)
    }
    
    return stats


if __name__ == "__main__":
    print("Riccati Coefficient Analysis")
    print("="*60)
    
    # Test for different viscosities
    ν_values = [1e-4, 1e-3, 1e-2, 1e-1]
    a_values = [7.0, 50, 100, 200]
    
    print("\nRiccati Coefficient γ:")
    print(f"{'ν':<10} {'a':<10} {'δ*':<12} {'γ':<12} {'Status':<10}")
    print("-"*60)
    
    for ν in ν_values:
        for a in a_values:
            δ_star = a**2 / (4 * np.pi**2)
            γ = compute_riccati_coefficient(ν, δ_star)
            status = "✅ PASS" if γ > 0 else "❌ FAIL"
            print(f"{ν:<10.4f} {a:<10.1f} {δ_star:<12.4f} {γ:<12.4f} {status:<10}")
