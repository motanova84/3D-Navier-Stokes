"""
Equation Visualizer Module

Visualizes mathematical equations and their relationships
"""

try:
    import matplotlib.pyplot as plt
    import matplotlib.patches as mpatches
    from matplotlib.patches import FancyBboxPatch, FancyArrowPatch
    MATPLOTLIB_AVAILABLE = True
except ImportError:
    MATPLOTLIB_AVAILABLE = False
    plt = None
    mpatches = None
    FancyBboxPatch = None
    FancyArrowPatch = None

import numpy as np
from typing import List, Dict, Optional, Tuple
from pathlib import Path
import warnings


def require_matplotlib(func):
    """Decorator to check if matplotlib is available"""
    def wrapper(*args, **kwargs):
        if not MATPLOTLIB_AVAILABLE:
            print(f"Skipping {func.__name__}: matplotlib is not installed")
            print("Install with: pip install matplotlib")
            return None
        return func(*args, **kwargs)
    return wrapper


class EquationVisualizer:
    """
    Visualizer for mathematical equations and relationships
    in the Navier-Stokes framework
    """
    
    def __init__(self, output_dir: str = "visualizations"):
        """
        Initialize the visualizer
        
        Args:
            output_dir: Directory to save visualizations
        """
        if not MATPLOTLIB_AVAILABLE:
            warnings.warn(
                "matplotlib is not installed. Visualization features will be limited. "
                "Install with: pip install matplotlib"
            )
        
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(exist_ok=True, parents=True)
        
        # Color scheme for categories
        self.category_colors = {
            'fundamental': '#2E86AB',
            'estimate': '#A23B72',
            'criterion': '#F18F01',
            'physical': '#C73E1D',
            'mathematical': '#6A994E',
            'qcal': '#BC4B51',
            'general': '#8B8B8B',
        }
    
    @require_matplotlib
    def visualize_equation_network(self, memory, output_file: str = "equation_network.png"):
        """
        Visualize the network of equations and their relationships
        
        Args:
            memory: MathematicalMemory instance
            output_file: Output filename
        """
        fig, ax = plt.subplots(figsize=(14, 10))
        ax.set_xlim(0, 10)
        ax.set_ylim(0, 10)
        ax.axis('off')
        
        # Get all equations
        equations = memory.knowledge_base['equations']
        
        # Position equations in a grid
        n_equations = len(equations)
        n_cols = int(np.ceil(np.sqrt(n_equations)))
        n_rows = int(np.ceil(n_equations / n_cols))
        
        positions = {}
        idx = 0
        for i in range(n_rows):
            for j in range(n_cols):
                if idx >= n_equations:
                    break
                x = 1 + j * (8 / max(n_cols - 1, 1))
                y = 9 - i * (8 / max(n_rows - 1, 1))
                eq_id = list(equations.keys())[idx]
                positions[eq_id] = (x, y)
                idx += 1
        
        # Draw equation boxes
        for eq_id, eq_data in equations.items():
            if eq_id not in positions:
                continue
            
            x, y = positions[eq_id]
            category = eq_data.get('category', 'general')
            color = self.category_colors.get(category, '#8B8B8B')
            
            # Create box
            box = FancyBboxPatch(
                (x - 0.4, y - 0.2), 0.8, 0.4,
                boxstyle="round,pad=0.05",
                facecolor=color,
                edgecolor='black',
                alpha=0.7,
                linewidth=2
            )
            ax.add_patch(box)
            
            # Add text
            name = eq_data['name']
            if len(name) > 15:
                name = name[:12] + "..."
            
            ax.text(x, y, name, ha='center', va='center',
                   fontsize=8, fontweight='bold', color='white')
        
        # Draw relationships
        relationships = memory.knowledge_base.get('relationships', [])
        for rel in relationships:
            from_id = rel['from']
            to_id = rel['to']
            
            if from_id in positions and to_id in positions:
                x1, y1 = positions[from_id]
                x2, y2 = positions[to_id]
                
                arrow = FancyArrowPatch(
                    (x1, y1), (x2, y2),
                    arrowstyle='->',
                    color='gray',
                    alpha=0.5,
                    linewidth=1.5,
                    connectionstyle="arc3,rad=0.2"
                )
                ax.add_patch(arrow)
        
        # Add legend
        legend_elements = [
            mpatches.Patch(facecolor=color, edgecolor='black', label=cat.capitalize())
            for cat, color in self.category_colors.items()
        ]
        ax.legend(handles=legend_elements, loc='upper left', fontsize=9)
        
        plt.title("Navier-Stokes Equation Network", fontsize=16, fontweight='bold')
        plt.tight_layout()
        
        output_path = self.output_dir / output_file
        plt.savefig(output_path, dpi=300, bbox_inches='tight')
        plt.close()
        
        print(f"Equation network saved to: {output_path}")
        return str(output_path)
    
    @require_matplotlib
    def visualize_category_distribution(self, memory, 
                                       output_file: str = "category_distribution.png"):
        """
        Visualize the distribution of equations by category
        
        Args:
            memory: MathematicalMemory instance
            output_file: Output filename
        """
        summary = memory.get_summary()
        
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))
        
        # Equations by category
        eq_categories = summary['equations_by_category']
        if eq_categories:
            categories = list(eq_categories.keys())
            counts = list(eq_categories.values())
            colors = [self.category_colors.get(cat, '#8B8B8B') for cat in categories]
            
            ax1.barh(categories, counts, color=colors, alpha=0.7, edgecolor='black')
            ax1.set_xlabel('Count', fontsize=12)
            ax1.set_title('Equations by Category', fontsize=14, fontweight='bold')
            ax1.grid(axis='x', alpha=0.3)
        
        # Constants by category
        const_categories = summary['constants_by_category']
        if const_categories:
            categories = list(const_categories.keys())
            counts = list(const_categories.values())
            colors = [self.category_colors.get(cat, '#8B8B8B') for cat in categories]
            
            ax2.barh(categories, counts, color=colors, alpha=0.7, edgecolor='black')
            ax2.set_xlabel('Count', fontsize=12)
            ax2.set_title('Constants by Category', fontsize=14, fontweight='bold')
            ax2.grid(axis='x', alpha=0.3)
        
        plt.tight_layout()
        
        output_path = self.output_dir / output_file
        plt.savefig(output_path, dpi=300, bbox_inches='tight')
        plt.close()
        
        print(f"Category distribution saved to: {output_path}")
        return str(output_path)
    
    @require_matplotlib
    def visualize_equation_details(self, equation_data: Dict, 
                                   output_file: str = "equation_details.png"):
        """
        Visualize details of a specific equation
        
        Args:
            equation_data: Dictionary with equation information
            output_file: Output filename
        """
        fig, ax = plt.subplots(figsize=(12, 8))
        ax.set_xlim(0, 10)
        ax.set_ylim(0, 10)
        ax.axis('off')
        
        # Title
        name = equation_data.get('name', 'Equation')
        ax.text(5, 9, name, ha='center', va='top', 
               fontsize=18, fontweight='bold')
        
        # Formula box
        formula = equation_data.get('formula', '')
        formula_box = FancyBboxPatch(
            (1, 6.5), 8, 1.5,
            boxstyle="round,pad=0.1",
            facecolor='lightblue',
            edgecolor='black',
            linewidth=2
        )
        ax.add_patch(formula_box)
        ax.text(5, 7.25, formula, ha='center', va='center',
               fontsize=14, family='monospace', wrap=True)
        
        # Description
        description = equation_data.get('description', '')
        ax.text(5, 5.8, 'Description:', ha='center', va='top',
               fontsize=12, fontweight='bold')
        
        # Wrap description text
        words = description.split()
        lines = []
        current_line = []
        for word in words:
            current_line.append(word)
            if len(' '.join(current_line)) > 60:
                lines.append(' '.join(current_line[:-1]))
                current_line = [word]
        if current_line:
            lines.append(' '.join(current_line))
        
        y_pos = 5.3
        for line in lines[:5]:  # Max 5 lines
            ax.text(5, y_pos, line, ha='center', va='top', fontsize=10)
            y_pos -= 0.3
        
        # Category and metadata
        category = equation_data.get('category', 'general')
        color = self.category_colors.get(category, '#8B8B8B')
        
        category_box = FancyBboxPatch(
            (3.5, 3), 3, 0.5,
            boxstyle="round,pad=0.05",
            facecolor=color,
            edgecolor='black',
            alpha=0.7
        )
        ax.add_patch(category_box)
        ax.text(5, 3.25, f"Category: {category.capitalize()}", 
               ha='center', va='center', fontsize=11, color='white', fontweight='bold')
        
        # Additional info
        info_y = 2.2
        if equation_data.get('operators'):
            operators = ', '.join(equation_data['operators'])
            ax.text(5, info_y, f"Operators: {operators}", 
                   ha='center', va='top', fontsize=9)
            info_y -= 0.4
        
        if equation_data.get('norms'):
            norms = ', '.join(equation_data['norms'][:5])  # Max 5 norms
            ax.text(5, info_y, f"Norms: {norms}", 
                   ha='center', va='top', fontsize=9)
            info_y -= 0.4
        
        if equation_data.get('constants'):
            constants = ', '.join(equation_data['constants'][:5])
            ax.text(5, info_y, f"Constants: {constants}", 
                   ha='center', va='top', fontsize=9)
        
        plt.tight_layout()
        
        output_path = self.output_dir / output_file
        plt.savefig(output_path, dpi=300, bbox_inches='tight')
        plt.close()
        
        print(f"Equation details saved to: {output_path}")
        return str(output_path)
    
    @require_matplotlib
    def visualize_proof_structure(self, memory, 
                                  output_file: str = "proof_structure.png"):
        """
        Visualize the structure of the proof strategy
        
        Args:
            memory: MathematicalMemory instance
            output_file: Output filename
        """
        fig, ax = plt.subplots(figsize=(14, 10))
        ax.set_xlim(0, 10)
        ax.set_ylim(0, 10)
        ax.axis('off')
        
        # Title
        ax.text(5, 9.5, "Navier-Stokes Global Regularity Proof Structure", 
               ha='center', va='top', fontsize=16, fontweight='bold')
        
        # Define proof steps with positions
        steps = [
            {"name": "Initial Data", "y": 8.5, "color": "#2E86AB"},
            {"name": "Littlewood-Paley\nDecomposition", "y": 7.5, "color": "#6A994E"},
            {"name": "Riccati Coefficient\nAnalysis", "y": 6.5, "color": "#A23B72"},
            {"name": "Dissipative Scale\nIdentification", "y": 5.5, "color": "#BC4B51"},
            {"name": "Osgood Inequality\nApplication", "y": 4.5, "color": "#F18F01"},
            {"name": "Besov Norm\nIntegrability", "y": 3.5, "color": "#2E86AB"},
            {"name": "BKM Criterion", "y": 2.5, "color": "#C73E1D"},
            {"name": "Global Regularity", "y": 1.5, "color": "#6A994E"},
        ]
        
        # Draw steps
        for i, step in enumerate(steps):
            box = FancyBboxPatch(
                (3, step["y"] - 0.3), 4, 0.6,
                boxstyle="round,pad=0.08",
                facecolor=step["color"],
                edgecolor='black',
                alpha=0.7,
                linewidth=2
            )
            ax.add_patch(box)
            
            ax.text(5, step["y"], step["name"], 
                   ha='center', va='center', fontsize=10, 
                   color='white', fontweight='bold')
            
            # Draw arrows between steps
            if i < len(steps) - 1:
                arrow = FancyArrowPatch(
                    (5, step["y"] - 0.35), (5, steps[i+1]["y"] + 0.35),
                    arrowstyle='->',
                    color='black',
                    linewidth=2,
                    mutation_scale=20
                )
                ax.add_patch(arrow)
        
        plt.tight_layout()
        
        output_path = self.output_dir / output_file
        plt.savefig(output_path, dpi=300, bbox_inches='tight')
        plt.close()
        
        print(f"Proof structure saved to: {output_path}")
        return str(output_path)
    
    @require_matplotlib
    def create_summary_report(self, memory, 
                            output_file: str = "summary_report.png"):
        """
        Create a visual summary report
        
        Args:
            memory: MathematicalMemory instance
            output_file: Output filename
        """
        summary = memory.get_summary()
        
        fig = plt.figure(figsize=(16, 10))
        
        # Create grid
        gs = fig.add_gridspec(3, 2, hspace=0.3, wspace=0.3)
        
        # Title
        fig.suptitle("Mathematical Knowledge Base Summary Report", 
                    fontsize=18, fontweight='bold')
        
        # Overall statistics
        ax1 = fig.add_subplot(gs[0, :])
        ax1.axis('off')
        stats_text = f"""
        Total Equations: {summary['total_equations']}  |  
        Total Constants: {summary['total_constants']}  |  
        Total Theorems: {summary['total_theorems']}  |  
        Total Relationships: {summary['total_relationships']}
        """
        ax1.text(0.5, 0.5, stats_text, ha='center', va='center',
                fontsize=14, bbox=dict(boxstyle='round', facecolor='lightgray', alpha=0.5))
        
        # Equations by category (pie chart)
        ax2 = fig.add_subplot(gs[1, 0])
        eq_categories = summary['equations_by_category']
        if eq_categories:
            labels = list(eq_categories.keys())
            sizes = list(eq_categories.values())
            colors = [self.category_colors.get(cat, '#8B8B8B') for cat in labels]
            
            ax2.pie(sizes, labels=labels, colors=colors, autopct='%1.1f%%',
                   startangle=90, textprops={'fontsize': 9})
            ax2.set_title('Equations by Category', fontsize=12, fontweight='bold')
        
        # Constants by category (pie chart)
        ax3 = fig.add_subplot(gs[1, 1])
        const_categories = summary['constants_by_category']
        if const_categories:
            labels = list(const_categories.keys())
            sizes = list(const_categories.values())
            colors = [self.category_colors.get(cat, '#8B8B8B') for cat in labels]
            
            ax3.pie(sizes, labels=labels, colors=colors, autopct='%1.1f%%',
                   startangle=90, textprops={'fontsize': 9})
            ax3.set_title('Constants by Category', fontsize=12, fontweight='bold')
        
        # Key operators and constants
        ax4 = fig.add_subplot(gs[2, :])
        ax4.axis('off')
        
        operators = summary.get('unique_operators', [])
        constants = summary.get('unique_constants', [])
        spaces = summary.get('unique_spaces', [])
        
        info_text = f"""
        Unique Operators: {', '.join(operators[:10]) if operators else 'None'}
        
        Unique Constants: {', '.join(constants[:10]) if constants else 'None'}
        
        Function Spaces: {', '.join(spaces[:10]) if spaces else 'None'}
        """
        
        ax4.text(0.05, 0.5, info_text, ha='left', va='center',
                fontsize=10, family='monospace',
                bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.5))
        
        output_path = self.output_dir / output_file
        plt.savefig(output_path, dpi=300, bbox_inches='tight')
        plt.close()
        
        print(f"Summary report saved to: {output_path}")
        return str(output_path)
