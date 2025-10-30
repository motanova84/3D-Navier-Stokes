#!/usr/bin/env python3
"""
Dyadic energy spectrum visualization
"""

import numpy as np
import matplotlib.pyplot as plt

def plot_dyadic_spectrum(frequencies: np.ndarray, energies: np.ndarray, 
                        output_file: str = "dyadic_spectrum.png"):
    """
    Plot dyadic energy spectrum
    
    Args:
        frequencies: Dyadic frequencies (2^j)
        energies: Energy in each dyadic block
        output_file: Output file path
    """
    plt.figure(figsize=(10, 6))
    
    plt.loglog(frequencies, energies, 'o-', linewidth=2, markersize=8)
    
    # Reference slopes
    k = frequencies[frequencies > 0]
    plt.loglog(k, k**(-5/3) * energies[1], '--', alpha=0.5, label='k^{-5/3} (Kolmogorov)')
    plt.loglog(k, k**(-3) * energies[1] * k[0]**3, '--', alpha=0.5, label='k^{-3} (Dissipation)')
    
    plt.xlabel('Frequency (2^j)')
    plt.ylabel('Energy')
    plt.title('Dyadic Energy Spectrum')
    plt.legend()
    plt.grid(True, alpha=0.3)
    
    plt.savefig(output_file, dpi=150)
    print(f"Dyadic spectrum saved to {output_file}")


if __name__ == "__main__":
    print("Dyadic Spectrum Visualization")
    print("="*60)
    
    # Example spectrum
    j_values = np.arange(0, 10)
    frequencies = 2.0**j_values
    energies = frequencies**(-5/3) * np.exp(-0.1 * j_values)
    
    plot_dyadic_spectrum(frequencies, energies, "example_spectrum.png")
