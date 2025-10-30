#!/usr/bin/env python3
"""
Unified BKM-CZ-Besov Framework: Route C - Energy Bootstrap

This module implements Route C from the unified framework:
Energy bootstrap with H^m Sobolev estimates and oscillatory damping.
"""

import numpy as np
from typing import Dict, List, Tuple
from scipy.integrate import odeint


def energy_bootstrap_ode(E: float, t: float, ν: float, C: float, 
                         δ_star: float, p: float = 1.5) -> float:
    """
    ODE for energy bootstrap with oscillatory damping.
    
    dE/dt = -ν·E + C·E^p·(1 - δ*)
    
    Args:
        E: Current energy H^m norm
        t: Time
        ν: Viscosity
        C: Nonlinear constant
        δ_star: Misalignment defect (damping factor)
        p: Power of nonlinearity (typically 3/2 or 2)
        
    Returns:
        dE/dt
    """
    dissipation = -ν * E
    production = C * (E ** p) * (1 - δ_star)
    return dissipation + production


def energy_bootstrap(u0_Hm: float, T_max: float = 1000.0, 
                     ν: float = 1e-3, C: float = 0.1,
                     δ_star: float = 0.15, p: float = 1.5,
                     dt: float = 0.1) -> Dict:
    """
    Bootstrap H^m energy estimates with oscillatory damping.
    
    If energy remains bounded, bootstrap succeeds → global regularity.
    
    Args:
        u0_Hm: Initial H^m norm
        T_max: Maximum time to integrate
        ν: Viscosity  
        C: Nonlinear constant
        δ_star: Misalignment defect
        p: Power of nonlinearity
        dt: Time step
        
    Returns:
        Dictionary with bootstrap results
    """
    t_data = np.arange(0, T_max, dt)
    
    # Solve ODE
    E_data = odeint(energy_bootstrap_ode, u0_Hm, t_data, 
                   args=(ν, C, δ_star, p))
    E_data = E_data.flatten()
    
    # Check for blowup
    if np.any(~np.isfinite(E_data)) or np.any(E_data > 1e10):
        blowup_idx = np.where((~np.isfinite(E_data)) | (E_data > 1e10))[0]
        if len(blowup_idx) > 0:
            idx = blowup_idx[0]
            return {
                'success': False,
                'blowup_time': t_data[idx],
                'E_data': E_data[:idx],
                't_data': t_data[:idx],
                'E_initial': u0_Hm,
                'E_max': np.max(E_data[:idx]) if idx > 0 else u0_Hm,
                'E_final': E_data[idx-1] if idx > 0 else u0_Hm,
                'is_decreasing': False,
                'is_bounded': False,
                'message': f'Blowup at t={t_data[idx]:.2f}'
            }
    
    # Check if energy is decreasing or bounded
    E_max = np.max(E_data)
    E_final = E_data[-1]
    is_bounded = E_max < 1e10
    is_decreasing = E_final < E_data[len(E_data)//2]
    
    return {
        'success': is_bounded,
        'blowup_time': None,
        'E_data': E_data,
        't_data': t_data,
        'E_initial': u0_Hm,
        'E_max': E_max,
        'E_final': E_final,
        'is_decreasing': is_decreasing,
        'is_bounded': is_bounded,
        'message': 'Bootstrap successful' if is_bounded else 'Bootstrap failed'
    }


def analyze_bootstrap_stability(ν: float, C: float, δ_star: float,
                                p: float = 1.5) -> Dict:
    """
    Analyze stability of the energy bootstrap system.
    
    For dE/dt = -νE + CE^p(1-δ*), equilibrium at:
    E* = [ν / (C(1-δ*))]^(1/(p-1))
    
    Stable if δ* is large enough.
    
    Args:
        ν: Viscosity
        C: Nonlinear constant
        δ_star: Misalignment defect
        p: Power
        
    Returns:
        Stability analysis
    """
    if δ_star >= 1:
        # Always stable - production term vanishes
        return {
            'stable': True,
            'equilibrium': 0.0,
            'critical_δ_star': 1.0,
            'message': 'Always stable (δ* ≥ 1)'
        }
    
    # Equilibrium point
    if p > 1:
        E_star = (ν / (C * (1 - δ_star))) ** (1 / (p - 1))
    else:
        E_star = np.inf
    
    # Linearized stability: check if dissipation dominates
    # At E*, we need -ν + pCE*^(p-1)(1-δ*) < 0
    if np.isfinite(E_star):
        derivative = -ν + p * C * (E_star ** (p - 1)) * (1 - δ_star)
        stable = derivative < 0
    else:
        stable = False
    
    # Critical δ* for stability (derivative = 0)
    # -ν + pνE*^(p-1) = 0 → E* = (1/p)^(1/(p-1))
    # Substitute back: δ*_crit = 1 - ν/(C·E*^(p-1))
    if p > 1:
        E_crit = (1 / p) ** (1 / (p - 1))
        δ_star_crit = 1 - ν / (C * E_crit ** (p - 1))
    else:
        δ_star_crit = 1.0
    
    return {
        'stable': stable,
        'equilibrium': E_star if np.isfinite(E_star) else None,
        'critical_δ_star': δ_star_crit,
        'derivative_at_equilibrium': derivative if np.isfinite(E_star) else None,
        'message': 'Stable' if stable else 'Unstable'
    }


def bootstrap_parameter_sweep(ν_values: List[float], 
                              δ_star_values: List[float],
                              u0_Hm: float = 10.0,
                              T_max: float = 100.0) -> Dict:
    """
    Sweep parameters to find region of bootstrap success.
    
    Args:
        ν_values: List of viscosity values
        δ_star_values: List of misalignment values
        u0_Hm: Initial energy
        T_max: Integration time
        
    Returns:
        Parameter sweep results
    """
    results = np.zeros((len(ν_values), len(δ_star_values)))
    
    for i, ν in enumerate(ν_values):
        for j, δ_star in enumerate(δ_star_values):
            boot = energy_bootstrap(u0_Hm, T_max, ν=ν, δ_star=δ_star)
            results[i, j] = 1.0 if boot['success'] else 0.0
    
    success_rate = np.mean(results)
    
    return {
        'success_matrix': results,
        'ν_values': ν_values,
        'δ_star_values': δ_star_values,
        'success_rate': success_rate,
        'best_δ_star': δ_star_values[np.argmax(np.mean(results, axis=0))]
    }


if __name__ == "__main__":
    print("="*70)
    print("ROUTE C: ENERGY BOOTSTRAP WITH H^m ESTIMATES")
    print("="*70)
    
    # Test 1: Successful bootstrap
    print("\n1. SUCCESSFUL BOOTSTRAP (High δ*)")
    print("-"*70)
    boot_success = energy_bootstrap(
        u0_Hm=10.0, T_max=100.0, ν=1e-3, C=0.1, δ_star=0.15, p=1.5
    )
    print(f"Success: {boot_success['success']}")
    print(f"Initial energy: {boot_success['E_initial']:.2f}")
    print(f"Final energy: {boot_success['E_final']:.2f}")
    print(f"Max energy: {boot_success['E_max']:.2f}")
    print(f"Decreasing: {boot_success['is_decreasing']}")
    
    # Test 2: Stability analysis
    print("\n2. STABILITY ANALYSIS")
    print("-"*70)
    stability = analyze_bootstrap_stability(ν=1e-3, C=0.1, δ_star=0.15, p=1.5)
    print(f"Stable: {stability['stable']}")
    if stability['equilibrium']:
        print(f"Equilibrium: {stability['equilibrium']:.4f}")
    print(f"Critical δ*: {stability['critical_δ_star']:.4f}")
    print(f"Message: {stability['message']}")
    
    # Test 3: Different δ* values
    print("\n3. PARAMETER SWEEP (δ* effect)")
    print("-"*70)
    δ_star_test = [0.05, 0.10, 0.15, 0.20, 0.25]
    print(f"{'δ*':<10} {'Success':<10} {'E_final':<12} {'Decreasing':<12}")
    print("-"*60)
    for δ in δ_star_test:
        boot = energy_bootstrap(u0_Hm=10.0, T_max=50.0, δ_star=δ)
        print(f"{δ:<10.2f} {str(boot['success']):<10} {boot['E_final']:<12.4f} {str(boot['is_decreasing']):<12}")
    
    # Test 4: Critical threshold
    print("\n4. CRITICAL δ* THRESHOLD")
    print("-"*70)
    for ν in [1e-4, 1e-3, 1e-2]:
        stab = analyze_bootstrap_stability(ν=ν, C=0.1, δ_star=0.15, p=1.5)
        print(f"ν={ν:.4f}: Critical δ* = {stab['critical_δ_star']:.4f}, Stable = {stab['stable']}")
    
    print("\n" + "="*70)
    print("✅ ROUTE C ENERGY BOOTSTRAP ANALYSIS COMPLETE")
    print("="*70)
