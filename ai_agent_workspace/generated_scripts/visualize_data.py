
"""
Navier-Stokes Data Visualization Script

Auto-generated script for visualizing simulation data
Generated: 2025-10-30T23:19:01.751444
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from pathlib import Path


class DataVisualizer:
    """
    Visualizer for Navier-Stokes simulation data
    """

    def __init__(self, output_dir: str = "visualizations"):
        """
        Initialize visualizer

        Args:
            output_dir: Directory to save visualizations
        """
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(exist_ok=True, parents=True)

    def plot_velocity_field(self, u, v, w, output_file: str = "velocity_field.png"):
        """
        Plot 2D slice of velocity field

        Args:
            u, v, w: Velocity components
            output_file: Output filename
        """
        fig, axes = plt.subplots(1, 3, figsize=(15, 5))

        # Take middle slice
        mid = u.shape[2] // 2

        im1 = axes[0].imshow(u[:, :, mid], cmap='RdBu_r', origin='lower')
        axes[0].set_title('u velocity', fontsize=12, fontweight='bold')
        plt.colorbar(im1, ax=axes[0])

        im2 = axes[1].imshow(v[:, :, mid], cmap='RdBu_r', origin='lower')
        axes[1].set_title('v velocity', fontsize=12, fontweight='bold')
        plt.colorbar(im2, ax=axes[1])

        im3 = axes[2].imshow(w[:, :, mid], cmap='RdBu_r', origin='lower')
        axes[2].set_title('w velocity', fontsize=12, fontweight='bold')
        plt.colorbar(im3, ax=axes[2])

        plt.tight_layout()

        output_path = self.output_dir / output_file
        plt.savefig(output_path, dpi=300, bbox_inches='tight')
        plt.close()

        print(f"Velocity field saved to: {output_path}")

    def plot_vorticity_field(self, omega_x, omega_y, omega_z,
                            output_file: str = "vorticity_field.png"):
        """
        Plot 2D slice of vorticity field

        Args:
            omega_x, omega_y, omega_z: Vorticity components
            output_file: Output filename
        """
        fig, axes = plt.subplots(1, 3, figsize=(15, 5))

        # Take middle slice
        mid = omega_x.shape[2] // 2

        im1 = axes[0].imshow(omega_x[:, :, mid], cmap='seismic', origin='lower')
        axes[0].set_title('ωx vorticity', fontsize=12, fontweight='bold')
        plt.colorbar(im1, ax=axes[0])

        im2 = axes[1].imshow(omega_y[:, :, mid], cmap='seismic', origin='lower')
        axes[1].set_title('ωy vorticity', fontsize=12, fontweight='bold')
        plt.colorbar(im2, ax=axes[1])

        im3 = axes[2].imshow(omega_z[:, :, mid], cmap='seismic', origin='lower')
        axes[2].set_title('ωz vorticity', fontsize=12, fontweight='bold')
        plt.colorbar(im3, ax=axes[2])

        plt.tight_layout()

        output_path = self.output_dir / output_file
        plt.savefig(output_path, dpi=300, bbox_inches='tight')
        plt.close()

        print(f"Vorticity field saved to: {output_path}")

    def plot_energy_spectrum(self, energy_spectrum, k_bins,
                            output_file: str = "energy_spectrum.png"):
        """
        Plot energy spectrum

        Args:
            energy_spectrum: Energy at each wavenumber
            k_bins: Wavenumber bins
            output_file: Output filename
        """
        fig, ax = plt.subplots(figsize=(10, 6))

        ax.loglog(k_bins, energy_spectrum, 'bo-', linewidth=2, markersize=6)

        # Add k^(-5/3) reference line (Kolmogorov)
        k_ref = k_bins[k_bins > 0]
        ax.loglog(k_ref, k_ref**(-5/3) * energy_spectrum[len(k_bins)//2] / k_ref[len(k_ref)//2]**(-5/3),
                 'r--', linewidth=2, label='k^(-5/3) Kolmogorov')

        ax.set_xlabel('Wavenumber k', fontsize=12)
        ax.set_ylabel('Energy E(k)', fontsize=12)
        ax.set_title('Energy Spectrum', fontsize=14, fontweight='bold')
        ax.legend(fontsize=10)
        ax.grid(True, alpha=0.3, which='both')

        plt.tight_layout()

        output_path = self.output_dir / output_file
        plt.savefig(output_path, dpi=300, bbox_inches='tight')
        plt.close()

        print(f"Energy spectrum saved to: {output_path}")


def main():
    """Main execution function"""
    print("=" * 70)
    print("DATA VISUALIZATION")
    print("=" * 70)

    visualizer = DataVisualizer()

    # TODO: Load and visualize actual data
    print("\nVisualization template ready!")
    print("Add your data loading and visualization code.")


if __name__ == "__main__":
    main()
