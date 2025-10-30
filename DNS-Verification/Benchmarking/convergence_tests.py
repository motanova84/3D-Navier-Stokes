#!/usr/bin/env python3
"""
Convergence tests for dual-limit parameter sweep
"""

import numpy as np
import matplotlib.pyplot as plt
from typing import Dict, List

def test_frequency_convergence(f₀_values: List[float], results: Dict) -> Dict:
    """
    Test convergence as f₀ → ∞
    
    Args:
        f₀_values: List of base frequencies
        results: Verification results for each f₀
        
    Returns:
        Convergence analysis dictionary
    """
    analysis = {
        'f₀_values': f₀_values,
        'δ_convergence': [],
        'besov_convergence': [],
        'converged': False
    }
    
    # Extract δ values
    for f₀ in f₀_values:
        if f₀ in results:
            δ_final = results[f₀]['metrics']['δ_history'][-1] if results[f₀]['metrics']['δ_history'] else 0
            analysis['δ_convergence'].append(δ_final)
    
    # Check convergence
    if len(analysis['δ_convergence']) >= 2:
        variations = np.diff(analysis['δ_convergence'])
        analysis['converged'] = np.all(np.abs(variations) < 0.01)
    
    return analysis


def test_reynolds_scaling(Re_values: List[float]) -> Dict:
    """
    Test scaling with Reynolds number
    
    Args:
        Re_values: List of Reynolds numbers
        
    Returns:
        Scaling analysis
    """
    analysis = {
        'Re_values': Re_values,
        'dissipative_scales': [],
        'grid_requirements': []
    }
    
    for Re in Re_values:
        # Kolmogorov scale
        η = Re**(-3/4)
        analysis['dissipative_scales'].append(η)
        
        # Grid requirement N ≥ Re^{3/4}
        N_min = int(Re**(3/4))
        analysis['grid_requirements'].append(N_min)
    
    return analysis


def plot_convergence(analysis: Dict, output_file: str = "convergence.png"):
    """
    Plot convergence results
    
    Args:
        analysis: Convergence analysis dictionary
        output_file: Output file path
    """
    if 'f₀_values' in analysis and 'δ_convergence' in analysis:
        plt.figure(figsize=(10, 6))
        plt.semilogx(analysis['f₀_values'], analysis['δ_convergence'], 'o-')
        plt.xlabel('Base Frequency f₀ (Hz)')
        plt.ylabel('Misalignment Defect δ')
        plt.title('Convergence of δ(f₀) to δ*')
        plt.grid(True, alpha=0.3)
        plt.savefig(output_file)
        print(f"Convergence plot saved to {output_file}")


if __name__ == "__main__":
    print("Convergence Testing Framework")
    print("="*60)
    
    # Test Reynolds scaling
    Re_values = [100, 500, 1000]
    scaling = test_reynolds_scaling(Re_values)
    
    print("\nReynolds Number Scaling:")
    print(f"{'Re':<10} {'η (Kolmogorov)':<20} {'N_min':<10}")
    print("-"*40)
    for i, Re in enumerate(Re_values):
        print(f"{Re:<10} {scaling['dissipative_scales'][i]:<20.6f} {scaling['grid_requirements'][i]:<10}")
