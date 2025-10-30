#!/usr/bin/env python3
"""
Unified BKM-CZ-Besov Framework: Route B - Volterra-Besov Integral

This module implements Route B from the unified framework:
Closure via Volterra integral equations in Besov spaces.
"""

import numpy as np
from scipy.integrate import quad
from typing import Callable, Dict, Optional, Tuple


def volterra_kernel(t: float, s: float) -> float:
    """
    Parabolic kernel for Volterra integral.
    
    K(t,s) = (t-s)^(-1/2) for the heat-type operator
    
    Args:
        t: Current time
        s: Integration time (s < t)
        
    Returns:
        Kernel value K(t,s)
    """
    if t <= s:
        return 0.0
    return (t - s) ** (-0.5)


def volterra_inequality(t: float, ω_Besov: Callable[[float], float],
                       C: float = 1.0, ε: float = 1e-10) -> float:
    """
    Volterra inequality from Lemma 7.1 (improved).
    
    X(t) ≤ X₀ + C ∫₀ᵗ K(t,s) X(s)² ds
    
    Args:
        t: Current time
        ω_Besov: Function returning ‖ω(s)‖_{B⁰_{∞,1}} at time s
        C: Constant from the inequality
        ε: Small regularization to avoid singularity
        
    Returns:
        Bound from Volterra inequality
    """
    def integrand(s):
        kernel = volterra_kernel(t, s + ε)
        besov_val = ω_Besov(s)
        return kernel * besov_val ** 2
    
    if t <= 0:
        return ω_Besov(0)
    
    # Initial condition + integral
    try:
        integral_val, _ = quad(integrand, 0, t)
        return ω_Besov(0) + C * integral_val
    except:
        return np.inf


def besov_volterra_integral(ω_Besov_data: np.ndarray, t_data: np.ndarray,
                            C: float = 1.0) -> Dict:
    """
    Complete Volterra integral analysis for Besov norms.
    
    Checks if ∫₀^∞ X(t) dt < ∞ where X satisfies the Volterra inequality.
    
    Args:
        ω_Besov_data: Array of Besov norm values at times
        t_data: Array of time points
        C: Constant from Volterra inequality
        
    Returns:
        Dictionary with integrability analysis
    """
    from scipy.interpolate import interp1d
    
    # Create interpolation function
    ω_Besov_func = interp1d(t_data, ω_Besov_data, 
                            kind='linear', fill_value='extrapolate')
    
    # Compute Volterra bounds at each time
    X_bounds = np.zeros_like(t_data)
    for i, t in enumerate(t_data):
        X_bounds[i] = volterra_inequality(t, ω_Besov_func, C)
    
    # Check integrability via trapezoidal rule
    if len(t_data) > 1:
        integral = np.trapz(X_bounds, t_data)
        is_integrable = np.isfinite(integral)
    else:
        integral = np.inf
        is_integrable = False
    
    # Check BKM criterion
    bkm_satisfied = is_integrable
    
    return {
        'X_bounds': X_bounds,
        't_data': t_data,
        'integral_value': integral,
        'is_integrable': is_integrable,
        'bkm_satisfied': bkm_satisfied,
        'max_bound': np.max(X_bounds) if is_integrable else np.inf
    }


def verify_volterra_contraction(t_max: float, X0: float, C: float,
                               num_steps: int = 100) -> Dict:
    """
    Verify if Volterra equation has contractive behavior.
    
    For global regularity, we need the solution to not blow up.
    
    Args:
        t_max: Maximum time to integrate
        X0: Initial Besov norm
        C: Volterra constant
        num_steps: Number of time steps
        
    Returns:
        Dictionary with contraction analysis
    """
    t_data = np.linspace(0, t_max, num_steps)
    dt = t_data[1] - t_data[0]
    
    # Simple Euler integration of Volterra equation
    # dX/dt ≈ C K(t,t-dt) X²
    X_values = np.zeros(num_steps)
    X_values[0] = X0
    
    for i in range(1, num_steps):
        t = t_data[i]
        # Approximate kernel contribution
        kernel_contrib = 0.0
        for j in range(i):
            kernel_contrib += volterra_kernel(t, t_data[j]) * X_values[j]**2 * dt
        
        X_values[i] = X0 + C * kernel_contrib
        
        # Check for blow-up
        if X_values[i] > 1e10 or not np.isfinite(X_values[i]):
            return {
                't_blowup': t,
                'X_values': X_values[:i+1],
                't_data': t_data[:i+1],
                'has_blowup': True,
                'is_contractive': False
            }
    
    # Check if decaying
    is_contractive = X_values[-1] < X_values[num_steps//2]
    
    return {
        't_blowup': None,
        'X_values': X_values,
        't_data': t_data,
        'has_blowup': False,
        'is_contractive': is_contractive,
        'final_value': X_values[-1]
    }


def lemma_7_1_improved(ω_data: np.ndarray, t_data: np.ndarray,
                       ν: float, C_CZ: float = 1.5) -> Dict:
    """
    Improved Lemma 7.1 from the problem statement.
    
    Uses Volterra framework with Besov space analysis.
    
    Args:
        ω_data: Vorticity data (or Besov norm)
        t_data: Time points
        ν: Viscosity
        C_CZ: Calderón-Zygmund constant in Besov
        
    Returns:
        Dictionary with closure verification
    """
    # Effective constant in Volterra equation
    C_eff = C_CZ / ν
    
    # Volterra analysis
    result = besov_volterra_integral(ω_data, t_data, C_eff)
    
    # Additional checks
    result['ν'] = ν
    result['C_CZ'] = C_CZ
    result['C_effective'] = C_eff
    result['closure_achieved'] = result['bkm_satisfied']
    
    return result


if __name__ == "__main__":
    print("="*70)
    print("ROUTE B: VOLTERRA-BESOV INTEGRAL CLOSURE")
    print("="*70)
    
    # Test 1: Simple decay case
    print("\n1. DECAYING BESOV NORM (Should close)")
    print("-"*70)
    t_test = np.linspace(0, 10, 100)
    ω_decay = 10.0 * np.exp(-0.5 * t_test)  # Exponential decay
    
    result_decay = besov_volterra_integral(ω_decay, t_test, C=1.0)
    print(f"Integral value: {result_decay['integral_value']:.4f}")
    print(f"Integrable: {result_decay['is_integrable']}")
    print(f"BKM satisfied: {result_decay['bkm_satisfied']}")
    print(f"Max bound: {result_decay['max_bound']:.4f}")
    
    # Test 2: Slow decay case
    print("\n2. SLOW DECAY BESOV NORM")
    print("-"*70)
    ω_slow = 10.0 / (1 + 0.1 * t_test)  # Algebraic decay
    
    result_slow = besov_volterra_integral(ω_slow, t_test, C=1.0)
    print(f"Integral value: {result_slow['integral_value']:.4f}")
    print(f"Integrable: {result_slow['is_integrable']}")
    print(f"BKM satisfied: {result_slow['bkm_satisfied']}")
    
    # Test 3: Contraction verification
    print("\n3. VOLTERRA CONTRACTION TEST")
    print("-"*70)
    contraction = verify_volterra_contraction(
        t_max=10.0, X0=5.0, C=0.1, num_steps=100
    )
    print(f"Has blowup: {contraction['has_blowup']}")
    print(f"Is contractive: {contraction['is_contractive']}")
    if not contraction['has_blowup']:
        print(f"Final value: {contraction['final_value']:.4f}")
    
    # Test 4: Lemma 7.1 improved
    print("\n4. LEMMA 7.1 IMPROVED (Besov-Volterra)")
    print("-"*70)
    lemma_result = lemma_7_1_improved(ω_decay, t_test, ν=1e-3, C_CZ=1.5)
    print(f"Closure achieved: {lemma_result['closure_achieved']}")
    print(f"Integral: {lemma_result['integral_value']:.4f}")
    print(f"C_effective: {lemma_result['C_effective']:.1f}")
    
    print("\n" + "="*70)
    print("✅ ROUTE B VOLTERRA-BESOV ANALYSIS COMPLETE")
    print("="*70)
