#!/usr/bin/env python3
"""
Riccati coefficient evolution visualization
"""

import numpy as np
import matplotlib.pyplot as plt

def plot_riccati_evolution(time: np.ndarray, γ_history: np.ndarray,
                          output_file: str = "riccati_evolution.png"):
    """
    Plot Riccati coefficient evolution over time
    
    Args:
        time: Time array
        γ_history: Riccati coefficient history
        output_file: Output file path
    """
    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(10, 8))
    
    # γ(t) evolution
    ax1.plot(time, γ_history, linewidth=2)
    ax1.axhline(y=0, color='r', linestyle='--', alpha=0.5, label='γ = 0')
    ax1.set_xlabel('Time')
    ax1.set_ylabel('Riccati Coefficient γ')
    ax1.set_title('Riccati Damping Coefficient Evolution')
    ax1.legend()
    ax1.grid(True, alpha=0.3)
    
    # Cumulative effect
    cumulative = np.cumsum(γ_history) * (time[1] - time[0])
    ax2.plot(time, cumulative, linewidth=2, color='green')
    ax2.set_xlabel('Time')
    ax2.set_ylabel('Cumulative ∫γ dt')
    ax2.set_title('Cumulative Damping Effect')
    ax2.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig(output_file, dpi=150)
    print(f"Riccati evolution plot saved to {output_file}")


if __name__ == "__main__":
    print("Riccati Evolution Visualization")
    print("="*60)
    
    # Example: damped oscillation
    t = np.linspace(0, 10, 1000)
    γ = 0.1 + 0.05 * np.sin(2 * np.pi * t) * np.exp(-0.1 * t)
    
    plot_riccati_evolution(t, γ, "example_riccati.png")
