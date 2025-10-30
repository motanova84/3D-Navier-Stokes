#!/usr/bin/env python3
"""
Visualization Module for Exhaustive Validation Results

Creates comprehensive plots and visualizations for parameter sweep analysis:
- δ* vs amplitude parameter
- Damping coefficient across parameter space
- Numerical stability regions
- Multi-parameter phase diagrams

Author: Enhanced validation visualization
"""

import numpy as np
import matplotlib
matplotlib.use('Agg')  # Non-interactive backend
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle
from matplotlib.colors import LinearSegmentedColormap
import json
import os
from typing import Dict, List, Optional

# Configure plotting style
plt.style.use('seaborn-v0_8-darkgrid')
FIGSIZE_LARGE = (14, 10)
FIGSIZE_MEDIUM = (12, 8)
FIGSIZE_SMALL = (10, 6)


class ValidationVisualizer:
    """
    Create comprehensive visualizations for validation results
    """
    
    def __init__(self, results: Optional[Dict] = None, 
                 results_file: str = None):
        """
        Initialize visualizer
        
        Args:
            results: Results dictionary from exhaustive validation
            results_file: Path to JSON file with results
        """
        if results is None and results_file is not None:
            with open(results_file, 'r') as f:
                results = json.load(f)
        
        self.results = results
        self.output_dir = "/home/runner/work/3D-Navier-Stokes/3D-Navier-Stokes/Results/Figures"
        os.makedirs(self.output_dir, exist_ok=True)
    
    def plot_delta_star_vs_amplitude(self, save: bool = True) -> str:
        """
        Plot δ* as a function of amplitude parameter a
        
        Highlights the threshold δ* = 0.998 and shows where a ≈ 200 falls
        
        Args:
            save: Whether to save the figure
            
        Returns:
            Path to saved figure
        """
        fig, ax = plt.subplots(figsize=FIGSIZE_MEDIUM)
        
        # Extract amplitude sweep results
        amplitude_sweep = self.results.get('amplitude_sweep', {})
        results = amplitude_sweep.get('results', [])
        
        if not results:
            print("Warning: No amplitude sweep results found")
            return None
        
        # Extract data
        a_values = [r['a'] for r in results]
        δ_values = [r['δ_star'] for r in results]
        closure_satisfied = [r['closure'] for r in results]
        
        # Plot δ* vs a
        colors = ['green' if c else 'red' for c in closure_satisfied]
        ax.scatter(a_values, δ_values, c=colors, s=50, alpha=0.6, 
                  label='Closure satisfied' if any(closure_satisfied) else None)
        
        # Add threshold line
        ax.axhline(y=0.998, color='blue', linestyle='--', linewidth=2, 
                  label='δ* threshold (0.998)')
        
        # Highlight a ≈ 200 region
        ax.axvspan(195, 205, alpha=0.2, color='orange', 
                  label='Recommended range (a ≈ 200)')
        
        # Find and mark a = 200
        a_200_results = [r for r in results if abs(r['a'] - 200.0) < 1.0]
        if a_200_results:
            r = a_200_results[0]
            ax.scatter([r['a']], [r['δ_star']], s=200, marker='*', 
                      color='gold', edgecolors='black', linewidths=2,
                      label=f'a = {r["a"]:.1f}, δ* = {r["δ_star"]:.1f}',
                      zorder=10)
        
        ax.set_xlabel('Amplitude Parameter (a)', fontsize=12, fontweight='bold')
        ax.set_ylabel('Misalignment Defect (δ*)', fontsize=12, fontweight='bold')
        ax.set_title('δ* vs Amplitude Parameter\n(Validation for Clay Millennium Problem)', 
                    fontsize=14, fontweight='bold')
        ax.set_xscale('log')
        ax.set_yscale('log')
        ax.grid(True, alpha=0.3)
        ax.legend(loc='best', fontsize=10)
        
        # Add annotation for key finding
        ax.text(0.05, 0.95, 
                f'✓ δ* exceeds threshold for a ≳ {min([r["a"] for r in results if r["δ_star_exceeds_threshold"]]):.1f}',
                transform=ax.transAxes, fontsize=11,
                verticalalignment='top',
                bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.8))
        
        plt.tight_layout()
        
        if save:
            output_path = os.path.join(self.output_dir, 'delta_star_vs_amplitude.png')
            plt.savefig(output_path, dpi=300, bbox_inches='tight')
            print(f"✓ Saved: {output_path}")
            plt.close()
            return output_path
        
        return None
    
    def plot_damping_coefficient(self, save: bool = True) -> str:
        """
        Plot damping coefficient as function of amplitude
        
        Args:
            save: Whether to save the figure
            
        Returns:
            Path to saved figure
        """
        fig, ax = plt.subplots(figsize=FIGSIZE_MEDIUM)
        
        # Extract amplitude sweep results
        amplitude_sweep = self.results.get('amplitude_sweep', {})
        results = amplitude_sweep.get('results', [])
        
        if not results:
            print("Warning: No amplitude sweep results found")
            return None
        
        # Extract data
        a_values = [r['a'] for r in results]
        damping_values = [r['damping'] for r in results]
        stable = [r['numerical_stability'] for r in results]
        
        # Plot damping vs a
        colors = ['green' if s else 'orange' for s in stable]
        ax.scatter(a_values, damping_values, c=colors, s=50, alpha=0.6)
        
        # Add zero line
        ax.axhline(y=0, color='red', linestyle='--', linewidth=2, 
                  label='Δ = 0 (critical threshold)')
        
        # Highlight a ≈ 200 region
        ax.axvspan(195, 205, alpha=0.2, color='orange', 
                  label='Recommended range (a ≈ 200)')
        
        # Find and mark a = 200
        a_200_results = [r for r in results if abs(r['a'] - 200.0) < 1.0]
        if a_200_results:
            r = a_200_results[0]
            ax.scatter([r['a']], [r['damping']], s=200, marker='*', 
                      color='gold', edgecolors='black', linewidths=2,
                      label=f'a = {r["a"]:.1f}, Δ = {r["damping"]:.1f}',
                      zorder=10)
        
        ax.set_xlabel('Amplitude Parameter (a)', fontsize=12, fontweight='bold')
        ax.set_ylabel('Damping Coefficient (Δ)', fontsize=12, fontweight='bold')
        ax.set_title('Damping Coefficient vs Amplitude Parameter\n(Positive Δ required for closure)', 
                    fontsize=14, fontweight='bold')
        ax.set_xscale('log')
        ax.grid(True, alpha=0.3)
        ax.legend(loc='best', fontsize=10)
        
        # Add shaded region for positive damping
        y_max = max(damping_values) * 1.1
        ax.fill_between([min(a_values), max(a_values)], 0, y_max, 
                        alpha=0.1, color='green', label='Positive damping region')
        
        plt.tight_layout()
        
        if save:
            output_path = os.path.join(self.output_dir, 'damping_coefficient.png')
            plt.savefig(output_path, dpi=300, bbox_inches='tight')
            print(f"✓ Saved: {output_path}")
            plt.close()
            return output_path
        
        return None
    
    def plot_stability_regions(self, save: bool = True) -> str:
        """
        Plot numerical stability regions in parameter space
        
        Args:
            save: Whether to save the figure
            
        Returns:
            Path to saved figure
        """
        fig, ax = plt.subplots(figsize=FIGSIZE_MEDIUM)
        
        # Extract amplitude sweep results
        amplitude_sweep = self.results.get('amplitude_sweep', {})
        results = amplitude_sweep.get('results', [])
        
        if not results:
            print("Warning: No amplitude sweep results found")
            return None
        
        # Extract data
        a_values = [r['a'] for r in results]
        δ_values = [r['δ_star'] for r in results]
        stable = [r['numerical_stability'] for r in results]
        closure = [r['closure'] for r in results]
        
        # Create stability categories
        categories = []
        for s, c in zip(stable, closure):
            if s and c:
                categories.append('Stable & Closure')
            elif s and not c:
                categories.append('Stable, No Closure')
            elif not s and c:
                categories.append('Unstable, Has Closure')
            else:
                categories.append('Unstable, No Closure')
        
        # Color mapping
        color_map = {
            'Stable & Closure': 'green',
            'Stable, No Closure': 'yellow',
            'Unstable, Has Closure': 'orange',
            'Unstable, No Closure': 'red'
        }
        
        colors = [color_map[cat] for cat in categories]
        
        # Plot
        for cat in color_map.keys():
            mask = [c == cat for c in categories]
            if any(mask):
                a_cat = [a for a, m in zip(a_values, mask) if m]
                δ_cat = [d for d, m in zip(δ_values, mask) if m]
                ax.scatter(a_cat, δ_cat, c=color_map[cat], s=50, 
                          alpha=0.6, label=cat)
        
        # Highlight a ≈ 200 region
        ax.axvline(x=200, color='blue', linestyle='--', linewidth=2, 
                  alpha=0.5, label='a = 200')
        
        ax.set_xlabel('Amplitude Parameter (a)', fontsize=12, fontweight='bold')
        ax.set_ylabel('Misalignment Defect (δ*)', fontsize=12, fontweight='bold')
        ax.set_title('Stability Regions in (a, δ*) Parameter Space', 
                    fontsize=14, fontweight='bold')
        ax.set_xscale('log')
        ax.set_yscale('log')
        ax.grid(True, alpha=0.3)
        ax.legend(loc='best', fontsize=9)
        
        plt.tight_layout()
        
        if save:
            output_path = os.path.join(self.output_dir, 'stability_regions.png')
            plt.savefig(output_path, dpi=300, bbox_inches='tight')
            print(f"✓ Saved: {output_path}")
            plt.close()
            return output_path
        
        return None
    
    def plot_multi_parameter_heatmap(self, save: bool = True) -> str:
        """
        Create heatmap showing damping across (a, ν) space
        
        Args:
            save: Whether to save the figure
            
        Returns:
            Path to saved figure
        """
        fig, ax = plt.subplots(figsize=FIGSIZE_LARGE)
        
        # Extract multi-parameter sweep results
        multi_sweep = self.results.get('multi_parameter_sweep', {})
        results = multi_sweep.get('results', [])
        
        if not results:
            print("Warning: No multi-parameter sweep results found")
            return None
        
        # Create grid for a specific α and f0 (use first values)
        α_fixed = results[0]['α']
        f0_fixed = results[0]['f0']
        
        # Filter results for fixed α and f0
        filtered = [r for r in results if r['α'] == α_fixed and r['f0'] == f0_fixed]
        
        if not filtered:
            print("Warning: No data for heatmap")
            return None
        
        # Extract unique values
        a_vals = sorted(list(set([r['a'] for r in filtered])))
        ν_vals = sorted(list(set([r['ν'] for r in filtered])))
        
        # Create grid
        damping_grid = np.zeros((len(ν_vals), len(a_vals)))
        
        for r in filtered:
            i = ν_vals.index(r['ν'])
            j = a_vals.index(r['a'])
            damping_grid[i, j] = r['damping']
        
        # Create heatmap
        im = ax.imshow(damping_grid, cmap='RdYlGn', aspect='auto',
                      extent=[min(a_vals), max(a_vals), min(ν_vals), max(ν_vals)],
                      origin='lower')
        
        # Add colorbar
        cbar = plt.colorbar(im, ax=ax)
        cbar.set_label('Damping Coefficient (Δ)', fontsize=11, fontweight='bold')
        
        # Add contour for Δ = 0
        contours = ax.contour(a_vals, ν_vals, damping_grid, levels=[0], 
                             colors='red', linewidths=2, linestyles='--')
        ax.clabel(contours, inline=True, fontsize=10)
        
        # Mark a = 200
        ax.axvline(x=200, color='blue', linestyle='--', linewidth=2, 
                  alpha=0.7, label='a = 200')
        
        ax.set_xlabel('Amplitude Parameter (a)', fontsize=12, fontweight='bold')
        ax.set_ylabel('Viscosity (ν)', fontsize=12, fontweight='bold')
        ax.set_title(f'Damping Coefficient Heatmap (α = {α_fixed}, f₀ = {f0_fixed} Hz)', 
                    fontsize=14, fontweight='bold')
        ax.set_yscale('log')
        ax.legend(loc='best', fontsize=10)
        
        plt.tight_layout()
        
        if save:
            output_path = os.path.join(self.output_dir, 'multi_parameter_heatmap.png')
            plt.savefig(output_path, dpi=300, bbox_inches='tight')
            print(f"✓ Saved: {output_path}")
            plt.close()
            return output_path
        
        return None
    
    def plot_edge_cases_summary(self, save: bool = True) -> str:
        """
        Create summary plot of edge cases
        
        Args:
            save: Whether to save the figure
            
        Returns:
            Path to saved figure
        """
        fig, axes = plt.subplots(2, 2, figsize=FIGSIZE_LARGE)
        
        # Extract edge cases
        edge_cases = self.results.get('edge_cases', {}).get('edge_cases', [])
        
        if not edge_cases:
            print("Warning: No edge cases found")
            return None
        
        # Plot 1: δ* for each case
        ax = axes[0, 0]
        case_names = [case['name'][:30] for case in edge_cases]
        δ_values = [case['result']['δ_star'] for case in edge_cases]
        colors = ['green' if case['result']['closure'] else 'red' 
                 for case in edge_cases]
        
        bars = ax.barh(range(len(case_names)), δ_values, color=colors, alpha=0.7)
        ax.set_yticks(range(len(case_names)))
        ax.set_yticklabels(case_names, fontsize=8)
        ax.set_xlabel('δ*', fontsize=10, fontweight='bold')
        ax.set_title('Misalignment Defect (δ*)', fontsize=11, fontweight='bold')
        ax.set_xscale('log')
        ax.grid(True, alpha=0.3, axis='x')
        ax.axvline(x=0.998, color='blue', linestyle='--', linewidth=2, alpha=0.5)
        
        # Plot 2: Damping coefficient
        ax = axes[0, 1]
        damping_values = [case['result']['damping'] for case in edge_cases]
        colors = ['green' if d > 0 else 'red' for d in damping_values]
        
        bars = ax.barh(range(len(case_names)), damping_values, color=colors, alpha=0.7)
        ax.set_yticks(range(len(case_names)))
        ax.set_yticklabels(case_names, fontsize=8)
        ax.set_xlabel('Δ', fontsize=10, fontweight='bold')
        ax.set_title('Damping Coefficient (Δ)', fontsize=11, fontweight='bold')
        ax.grid(True, alpha=0.3, axis='x')
        ax.axvline(x=0, color='blue', linestyle='--', linewidth=2, alpha=0.5)
        
        # Plot 3: Numerical stability
        ax = axes[1, 0]
        stability_status = []
        for case in edge_cases:
            stability = case.get('stability', {})
            if isinstance(stability, dict):
                stability_status.append('Stable' if stability.get('is_stable', True) else 'Unstable')
            else:
                stability_status.append('Unknown')
        
        stable_count = stability_status.count('Stable')
        unstable_count = stability_status.count('Unstable')
        
        ax.pie([stable_count, unstable_count], 
               labels=['Stable', 'Unstable'],
               colors=['green', 'red'],
               autopct='%1.1f%%',
               startangle=90)
        ax.set_title('Numerical Stability', fontsize=11, fontweight='bold')
        
        # Plot 4: Closure satisfaction
        ax = axes[1, 1]
        closure_status = [case['result']['closure'] for case in edge_cases]
        satisfied = closure_status.count(True)
        not_satisfied = closure_status.count(False)
        
        ax.pie([satisfied, not_satisfied],
               labels=['Closure Satisfied', 'No Closure'],
               colors=['green', 'red'],
               autopct='%1.1f%%',
               startangle=90)
        ax.set_title('Closure Condition', fontsize=11, fontweight='bold')
        
        plt.suptitle('Edge Cases Summary', fontsize=14, fontweight='bold')
        plt.tight_layout()
        
        if save:
            output_path = os.path.join(self.output_dir, 'edge_cases_summary.png')
            plt.savefig(output_path, dpi=300, bbox_inches='tight')
            print(f"✓ Saved: {output_path}")
            plt.close()
            return output_path
        
        return None
    
    def generate_all_plots(self) -> List[str]:
        """
        Generate all visualization plots
        
        Returns:
            List of paths to saved figures
        """
        print("\n" + "="*70)
        print("GENERATING VISUALIZATION PLOTS")
        print("="*70)
        
        saved_files = []
        
        # Plot 1: δ* vs amplitude
        print("\n1. Plotting δ* vs amplitude...")
        path = self.plot_delta_star_vs_amplitude()
        if path:
            saved_files.append(path)
        
        # Plot 2: Damping coefficient
        print("\n2. Plotting damping coefficient...")
        path = self.plot_damping_coefficient()
        if path:
            saved_files.append(path)
        
        # Plot 3: Stability regions
        print("\n3. Plotting stability regions...")
        path = self.plot_stability_regions()
        if path:
            saved_files.append(path)
        
        # Plot 4: Multi-parameter heatmap
        print("\n4. Plotting multi-parameter heatmap...")
        path = self.plot_multi_parameter_heatmap()
        if path:
            saved_files.append(path)
        
        # Plot 5: Edge cases summary
        print("\n5. Plotting edge cases summary...")
        path = self.plot_edge_cases_summary()
        if path:
            saved_files.append(path)
        
        print("\n" + "="*70)
        print(f"VISUALIZATION COMPLETE - {len(saved_files)} plots generated")
        print("="*70)
        
        return saved_files


def main():
    """
    Main entry point for visualization
    """
    # Load results
    results_file = "/home/runner/work/3D-Navier-Stokes/3D-Navier-Stokes/Results/validation_results.json"
    
    if not os.path.exists(results_file):
        print(f"Error: Results file not found: {results_file}")
        print("Please run exhaustive_validation.py first to generate results.")
        return
    
    # Create visualizer
    visualizer = ValidationVisualizer(results_file=results_file)
    
    # Generate all plots
    saved_files = visualizer.generate_all_plots()
    
    print("\n✓ All visualizations saved to:")
    for f in saved_files:
        print(f"  - {f}")
    
    return saved_files


if __name__ == "__main__":
    saved_files = main()
