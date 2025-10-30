#!/usr/bin/env python3
"""
Dyadic analysis tools for Littlewood-Paley decomposition
"""

import numpy as np
from scipy import fft
from typing import List, Dict

def compute_dyadic_spectrum(u_field: np.ndarray, dyadic_blocks: List[Dict]) -> Dict:
    """
    Compute energy spectrum by dyadic block
    
    Args:
        u_field: Velocity field (3, N, N, N)
        dyadic_blocks: List of dyadic block definitions
        
    Returns:
        Dictionary with dyadic energies
    """
    energies = []
    frequencies = []
    
    for block in dyadic_blocks:
        mask = block['mask']
        energy = 0
        
        for i in range(3):
            u_fft = fft.fftn(u_field[i])
            u_fft_masked = u_fft * mask
            energy += np.sum(np.abs(u_fft_masked)**2)
        
        energies.append(energy)
        frequencies.append(2**block['j'] if block['j'] >= 0 else 0.5)
    
    return {
        'frequencies': np.array(frequencies),
        'energies': np.array(energies)
    }


def compute_dissipative_threshold(ν: float, δ_star: float, c_BKM: float = 2.0, 
                                  c_B: float = 0.1) -> int:
    """
    Compute dissipative threshold j_d where dissipation dominates
    
    Args:
        ν: Viscosity
        δ_star: Misalignment defect
        c_BKM: Calderón-Zygmund constant
        c_B: Bernstein constant
        
    Returns:
        Dissipative threshold j_d
    """
    numerator = c_BKM * (1 - δ_star) * (1 + np.log(c_BKM / ν))
    denominator = ν * c_B
    
    if denominator > 0:
        j_d = np.ceil(np.log2(numerator / denominator) / 2)
        return int(max(0, j_d))
    else:
        return 0


def analyze_scale_by_scale(ω_field: np.ndarray, dyadic_blocks: List[Dict]) -> Dict:
    """
    Perform scale-by-scale analysis of vorticity
    
    Args:
        ω_field: Vorticity field (3, N, N, N)
        dyadic_blocks: List of dyadic blocks
        
    Returns:
        Dictionary with scale-dependent statistics
    """
    results = {
        'j_values': [],
        'l_infinity_norms': [],
        'l2_norms': [],
        'enstrophy': []
    }
    
    for block in dyadic_blocks:
        mask = block['mask']
        ω_block = np.zeros_like(ω_field)
        
        for i in range(3):
            ω_fft = fft.fftn(ω_field[i])
            ω_fft[~mask] = 0
            ω_block[i] = np.real(fft.ifftn(ω_fft))
        
        # Norms
        ω_mag = np.linalg.norm(ω_block, axis=0)
        l_inf = np.max(ω_mag)
        l2 = np.sqrt(np.mean(ω_mag**2))
        enstrophy = np.mean(ω_mag**2)
        
        results['j_values'].append(block['j'])
        results['l_infinity_norms'].append(l_inf)
        results['l2_norms'].append(l2)
        results['enstrophy'].append(enstrophy)
    
    return results


if __name__ == "__main__":
    # Example usage
    print("Dyadic Analysis Tools")
    print("="*60)
    
    # Test dissipative threshold calculation
    ν = 1e-3
    δ_star_values = [0.01, 0.5, 0.998, 1.0]
    
    print("\nDissipative Threshold j_d:")
    print(f"{'δ*':<10} {'j_d':<5}")
    print("-"*15)
    for δ_star in δ_star_values:
        j_d = compute_dissipative_threshold(ν, δ_star)
        print(f"{δ_star:<10.3f} {j_d:<5}")
