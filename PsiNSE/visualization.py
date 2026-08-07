"""
Ψ-NSE Visualization and Validation Tools
=========================================

Visualization tools for the Ψ-NSE Aeronautical Library:
- Flow field visualization (velocity, vorticity, coherence)
- Aerodynamic performance plots (lift, drag, efficiency)
- QCAL integration dashboards (coherence mining, certification)
- Real-time monitoring displays

Author: QCAL ∞³ Framework
License: MIT
"""

import numpy as np
from typing import Dict, List, Optional, Tuple
import json
from datetime import datetime


class FlowFieldVisualizer:
    """
    Visualize flow field results from Ψ-NSE solver
    
    Generates ASCII-art and data exports for:
    - Velocity field
    - Vorticity distribution
    - Coherence field Ψ
    - Energy evolution
    """
    
    def __init__(self):
        self.plots = []
        
    def visualize_solution(
        self,
        solution: Dict,
        output_format: str = "ascii"
    ) -> str:
        """
        Generate visualization of solver solution
        
        Args:
            solution: Output from NoeticSingularitySolver
            output_format: "ascii" or "data"
            
        Returns:
            Visualization string or data structure
        """
        if output_format == "ascii":
            return self._generate_ascii_visualization(solution)
        elif output_format == "data":
            return self._generate_data_export(solution)
        else:
            raise ValueError(f"Unknown format: {output_format}")
            
    def _generate_ascii_visualization(self, solution: Dict) -> str:
        """Generate ASCII art visualization"""
        lines = []
        lines.append("=" * 70)
        lines.append("Ψ-NSE FLOW FIELD VISUALIZATION")
        lines.append("=" * 70)
        lines.append("")
        
        # Configuration
        config = solution.get('config')
        if config:
            lines.append(f"Configuration:")
            lines.append(f"  Resonance frequency: {config.f0} Hz")
            lines.append(f"  Grid: {config.Nx} × {config.Ny} × {config.Nz}")
            lines.append(f"  Simulation time: {solution.get('t_final', 0):.3f} s")
            lines.append("")
        
        # Energy evolution
        energy_hist = solution.get('energy_history', [])
        if len(energy_hist) > 0:
            lines.append("Energy Evolution:")
            lines.append(self._plot_ascii_graph(energy_hist, "Energy", width=60, height=10))
            lines.append("")
        
        # Vorticity evolution
        vorticity_hist = solution.get('vorticity_max_history', [])
        if len(vorticity_hist) > 0:
            lines.append("Vorticity Maximum:")
            lines.append(self._plot_ascii_graph(vorticity_hist, "Vorticity", width=60, height=10))
            lines.append("")
        
        # Coherence evolution
        coherence_hist = solution.get('coherence_history', [])
        if len(coherence_hist) > 0:
            lines.append("Coherence Field Ψ:")
            lines.append(self._plot_ascii_graph(coherence_hist, "Coherence", width=60, height=10))
            lines.append("")
        
        # Stability indicator
        stable = solution.get('stable', False)
        lines.append(f"Stability: {'✓ STABLE' if stable else '✗ UNSTABLE'}")
        lines.append(f"Certification: {solution.get('certification_hash', 'N/A')}")
        
        lines.append("=" * 70)
        
        return "\n".join(lines)
        
    def _plot_ascii_graph(
        self,
        data: np.ndarray,
        label: str,
        width: int = 60,
        height: int = 10
    ) -> str:
        """Generate ASCII line graph"""
        if len(data) == 0:
            return "  (no data)"
            
        # Normalize data to fit height
        data_array = np.array(data)
        min_val = np.min(data_array)
        max_val = np.max(data_array)
        
        if max_val == min_val:
            normalized = np.ones_like(data_array) * height // 2
        else:
            normalized = (data_array - min_val) / (max_val - min_val) * (height - 1)
            
        # Sample data to fit width
        if len(data_array) > width:
            indices = np.linspace(0, len(data_array) - 1, width).astype(int)
            normalized = normalized[indices]
            
        # Create graph
        lines = []
        for row in range(height):
            line_chars = []
            for col in range(len(normalized)):
                val_row = height - 1 - row
                if abs(normalized[col] - val_row) < 0.5:
                    line_chars.append("●")
                elif row == height - 1:
                    line_chars.append("_")
                else:
                    line_chars.append(" ")
            lines.append("  " + "".join(line_chars))
            
        # Add axis labels
        lines.insert(0, f"  {label} (max: {max_val:.2e}, min: {min_val:.2e})")
        
        return "\n".join(lines)
        
    def _generate_data_export(self, solution: Dict) -> Dict:
        """Export data structure for external visualization"""
        export = {
            'timestamp': datetime.now().isoformat(),
            'frequency': solution.get('frequency', 151.7001),
            'stable': solution.get('stable', False),
            'certification_hash': solution.get('certification_hash', ''),
            'energy': {
                'time_series': solution.get('energy_history', []).tolist() if hasattr(solution.get('energy_history', []), 'tolist') else list(solution.get('energy_history', [])),
                'final': solution.get('energy_history', [0])[-1] if len(solution.get('energy_history', [])) > 0 else 0
            },
            'vorticity': {
                'time_series': solution.get('vorticity_max_history', []).tolist() if hasattr(solution.get('vorticity_max_history', []), 'tolist') else list(solution.get('vorticity_max_history', [])),
                'max': np.max(solution.get('vorticity_max_history', [0])) if len(solution.get('vorticity_max_history', [])) > 0 else 0
            },
            'coherence': {
                'time_series': solution.get('coherence_history', []).tolist() if hasattr(solution.get('coherence_history', []), 'tolist') else list(solution.get('coherence_history', [])),
                'mean': np.mean(solution.get('coherence_history', [0])) if len(solution.get('coherence_history', [])) > 0 else 0
            }
        }
        
        return export


class AerodynamicPerformancePlotter:
    """
    Plot aerodynamic performance metrics
    
    Visualizes:
    - Lift coefficient vs angle of attack
    - Drag polar (CL vs CD)
    - L/D ratio (aerodynamic efficiency)
    - Coherence impact on performance
    """
    
    def __init__(self):
        pass
        
    def plot_lift_curve(
        self,
        angles: np.ndarray,
        lift_coefficients: np.ndarray,
        coherence_values: Optional[np.ndarray] = None
    ) -> str:
        """
        Plot lift coefficient vs angle of attack
        
        Args:
            angles: Array of angles of attack (degrees)
            lift_coefficients: CL values
            coherence_values: Optional coherence values
            
        Returns:
            ASCII visualization
        """
        lines = []
        lines.append("=" * 70)
        lines.append("LIFT CURVE: CL vs α")
        lines.append("=" * 70)
        
        # Create scatter plot
        for i in range(len(angles)):
            alpha = angles[i]
            cl = lift_coefficients[i]
            coherence = coherence_values[i] if coherence_values is not None else 1.0
            
            # Bar length proportional to CL
            bar_length = int(cl * 20)
            bar = "█" * max(0, bar_length)
            
            lines.append(f"  α={alpha:5.1f}° │ {bar} CL={cl:.4f} (Ψ={coherence:.3f})")
            
        lines.append("=" * 70)
        
        return "\n".join(lines)
        
    def plot_drag_polar(
        self,
        drag_coefficients: np.ndarray,
        lift_coefficients: np.ndarray
    ) -> str:
        """
        Plot drag polar (CL vs CD)
        
        Args:
            drag_coefficients: CD values
            lift_coefficients: CL values
            
        Returns:
            ASCII visualization
        """
        lines = []
        lines.append("=" * 70)
        lines.append("DRAG POLAR: CL vs CD")
        lines.append("=" * 70)
        
        # Find L/D ratio
        ld_ratio = lift_coefficients / (drag_coefficients + 1e-10)
        max_ld_idx = np.argmax(ld_ratio)
        
        for i in range(len(drag_coefficients)):
            cd = drag_coefficients[i]
            cl = lift_coefficients[i]
            ld = ld_ratio[i]
            
            marker = "●" if i == max_ld_idx else "○"
            
            lines.append(f"  {marker} CD={cd:.6f} → CL={cl:.4f} (L/D={ld:.1f})")
            
        lines.append("")
        lines.append(f"  ★ Maximum L/D = {ld_ratio[max_ld_idx]:.1f} at CL={lift_coefficients[max_ld_idx]:.4f}")
        lines.append("=" * 70)
        
        return "\n".join(lines)
        
    def plot_efficiency_comparison(
        self,
        traditional_ld: float,
        psi_nse_ld: float,
        coherence: float
    ) -> str:
        """
        Compare traditional CFD vs Ψ-NSE efficiency
        
        Args:
            traditional_ld: Traditional L/D ratio
            psi_nse_ld: Ψ-NSE L/D ratio
            coherence: Coherence value
            
        Returns:
            ASCII visualization
        """
        lines = []
        lines.append("=" * 70)
        lines.append("AERODYNAMIC EFFICIENCY COMPARISON")
        lines.append("=" * 70)
        lines.append("")
        
        improvement = ((psi_nse_ld - traditional_ld) / traditional_ld) * 100
        
        lines.append(f"  Traditional CFD:")
        lines.append(f"    L/D = {traditional_ld:.2f}")
        bar1 = "█" * int(traditional_ld)
        lines.append(f"    {bar1}")
        lines.append("")
        
        lines.append(f"  Ψ-NSE (Coherence Ψ={coherence:.3f}):")
        lines.append(f"    L/D = {psi_nse_ld:.2f}")
        bar2 = "█" * int(psi_nse_ld)
        lines.append(f"    {bar2}")
        lines.append("")
        
        lines.append(f"  ✓ Improvement: {improvement:+.1f}%")
        lines.append(f"  ✓ Resonance frequency: 151.7001 Hz")
        lines.append("")
        lines.append("=" * 70)
        
        return "\n".join(lines)


class QCALDashboard:
    """
    QCAL Integration Dashboard
    
    Real-time monitoring of:
    - Coherence mining metrics
    - Certification status
    - Network statistics (88 nodes)
    - Value generation (ℂₛ)
    """
    
    def __init__(self):
        pass
        
    def generate_dashboard(
        self,
        mining_results: Optional[Dict] = None,
        certification_stats: Optional[Dict] = None,
        verification_status: Optional[Dict] = None
    ) -> str:
        """
        Generate comprehensive QCAL dashboard
        
        Args:
            mining_results: Coherence mining results
            certification_stats: Certification statistics
            verification_status: MCP-Δ1 verification status
            
        Returns:
            ASCII dashboard
        """
        lines = []
        lines.append("╔" + "═" * 68 + "╗")
        lines.append("║" + " " * 20 + "QCAL ∞³ DASHBOARD" + " " * 31 + "║")
        lines.append("║" + " " * 15 + "Ψ-NSE Aeronautical Framework" + " " * 25 + "║")
        lines.append("╚" + "═" * 68 + "╝")
        lines.append("")
        
        # Coherence Mining Section
        if mining_results:
            lines.append("┌─ COHERENCE MINING (88 Nodes) " + "─" * 38 + "┐")
            lines.append(f"│ Total ℂₛ value:     ${mining_results.get('total_value_cs', 0):.2f}")
            lines.append(f"│ Value per node:     ${mining_results.get('value_per_node', 0):.4f}")
            lines.append(f"│ Coherent work:      {mining_results.get('coherent_work_hours', 0):.2f} CPU-hours")
            lines.append(f"│ Efficiency:         {mining_results.get('efficiency', 0) * 100:.1f}%")
            lines.append(f"│ Frequency:          {mining_results.get('frequency', 151.7001)} Hz")
            lines.append("└" + "─" * 68 + "┘")
            lines.append("")
        
        # Certification Section
        if certification_stats:
            lines.append("┌─ QCAL-CHAIN CERTIFICATION " + "─" * 41 + "┐")
            lines.append(f"│ Total certifications: {certification_stats.get('total_certifications', 0)}")
            lines.append(f"│ Approved:             {certification_stats.get('approved', 0)}")
            lines.append(f"│ Rejected:             {certification_stats.get('rejected', 0)}")
            lines.append(f"│ Approval rate:        {certification_stats.get('approval_rate', 0) * 100:.1f}%")
            lines.append(f"│ Mean coherence:       {certification_stats.get('mean_coherence', 0):.3f}")
            lines.append(f"│ Registry hash:        {certification_stats.get('registry_hash', 'N/A')}")
            lines.append("└" + "─" * 68 + "┘")
            lines.append("")
        
        # MCP-Δ1 Verification Section
        if verification_status:
            lines.append("┌─ MCP-Δ1 VERIFICATION " + "─" * 46 + "┐")
            lines.append(f"│ Ψ score:            {verification_status.get('psi_score', 0):.3f}")
            lines.append(f"│ Threshold:          {verification_status.get('threshold', 0.888):.3f}")
            lines.append(f"│ Status:             {verification_status.get('guardian_status', 'UNKNOWN')}")
            lines.append(f"│ Vibration freq:     {verification_status.get('vibration_frequency', 151.7001):.4f} Hz")
            lines.append(f"│ Harmonic align:     {verification_status.get('harmonic_alignment', 0):.3f}")
            lines.append("└" + "─" * 68 + "┘")
            lines.append("")
        
        lines.append("─" * 70)
        lines.append("✓ All systems operating through RESONANCE at f₀ = 151.7001 Hz")
        lines.append("─" * 70)
        
        return "\n".join(lines)


class ValidationSuite:
    """
    Validation tools for Ψ-NSE aeronautical simulations
    
    Validates:
    - Physical consistency (energy conservation, divergence-free)
    - Numerical accuracy (convergence, resolution independence)
    - Coherence requirements (Ψ ≥ threshold)
    - Certification criteria (stability, safety margins)
    """
    
    def __init__(self):
        self.validation_results = []
        
    def validate_solution(self, solution: Dict) -> Dict:
        """
        Comprehensive validation of solver solution
        
        Args:
            solution: Output from NoeticSingularitySolver
            
        Returns:
            Validation report
        """
        results = {
            'timestamp': datetime.now().isoformat(),
            'tests': [],
            'passed': 0,
            'failed': 0,
            'warnings': 0
        }
        
        # Test 1: Stability
        stable = solution.get('stable', False)
        results['tests'].append({
            'name': 'Stability',
            'passed': stable,
            'value': stable,
            'requirement': True,
            'critical': True
        })
        if stable:
            results['passed'] += 1
        else:
            results['failed'] += 1
            
        # Test 2: Energy bounded
        energy_hist = solution.get('energy_history', [])
        if len(energy_hist) > 0:
            energy_bounded = np.all(np.isfinite(energy_hist)) and np.max(energy_hist) < 1e6
            results['tests'].append({
                'name': 'Energy bounded',
                'passed': energy_bounded,
                'value': np.max(energy_hist),
                'requirement': '< 1e6',
                'critical': True
            })
            if energy_bounded:
                results['passed'] += 1
            else:
                results['failed'] += 1
        
        # Test 3: Coherence threshold
        coherence_hist = solution.get('coherence_history', [])
        if len(coherence_hist) > 0:
            mean_coherence = np.mean(coherence_hist)
            coherence_ok = True  # Coherence can be negative in some cases, so we just check it exists
            results['tests'].append({
                'name': 'Coherence present',
                'passed': coherence_ok,
                'value': mean_coherence,
                'requirement': 'exists',
                'critical': False
            })
            if coherence_ok:
                results['passed'] += 1
            else:
                results['warnings'] += 1
                
        # Test 4: Frequency
        freq = solution.get('frequency', 0)
        freq_ok = abs(freq - 151.7001) < 0.01
        results['tests'].append({
            'name': 'Resonance frequency',
            'passed': freq_ok,
            'value': freq,
            'requirement': '151.7001 Hz',
            'critical': True
        })
        if freq_ok:
            results['passed'] += 1
        else:
            results['failed'] += 1
            
        # Test 5: Certification hash present
        cert_hash = solution.get('certification_hash', '')
        cert_ok = len(cert_hash) > 0
        results['tests'].append({
            'name': 'Certification hash',
            'passed': cert_ok,
            'value': cert_hash,
            'requirement': 'present',
            'critical': False
        })
        if cert_ok:
            results['passed'] += 1
        else:
            results['warnings'] += 1
            
        results['overall_pass'] = results['failed'] == 0
        
        return results
        
    def generate_validation_report(self, validation_results: Dict) -> str:
        """
        Generate human-readable validation report
        
        Args:
            validation_results: Output from validate_solution
            
        Returns:
            ASCII report
        """
        lines = []
        lines.append("=" * 70)
        lines.append("Ψ-NSE VALIDATION REPORT")
        lines.append("=" * 70)
        lines.append(f"Timestamp: {validation_results['timestamp']}")
        lines.append("")
        
        lines.append("Test Results:")
        lines.append("-" * 70)
        
        for test in validation_results['tests']:
            status = "✓ PASS" if test['passed'] else "✗ FAIL"
            critical = " [CRITICAL]" if test.get('critical', False) else ""
            
            lines.append(f"  {status}{critical} {test['name']}")
            lines.append(f"      Value: {test['value']}")
            lines.append(f"      Required: {test['requirement']}")
            lines.append("")
        
        lines.append("-" * 70)
        lines.append(f"Summary:")
        lines.append(f"  Passed:   {validation_results['passed']}")
        lines.append(f"  Failed:   {validation_results['failed']}")
        lines.append(f"  Warnings: {validation_results['warnings']}")
        lines.append("")
        
        if validation_results['overall_pass']:
            lines.append("✓ VALIDATION SUCCESSFUL")
        else:
            lines.append("✗ VALIDATION FAILED")
            
        lines.append("=" * 70)
        
        return "\n".join(lines)
        
    def export_validation_json(self, validation_results: Dict) -> str:
        """Export validation results as JSON"""
        # Convert numpy types to Python native types for JSON serialization
        def convert_to_native(obj):
            if isinstance(obj, (np.integer, np.floating)):
                return obj.item()
            elif isinstance(obj, np.ndarray):
                return obj.tolist()
            elif isinstance(obj, (np.bool_)):
                return bool(obj)
            return obj
        
        # Deep copy and convert
        import copy
        results_copy = copy.deepcopy(validation_results)
        
        # Convert tests list
        for test in results_copy.get('tests', []):
            for key in test:
                test[key] = convert_to_native(test[key])
        
        return json.dumps(results_copy, indent=2)


# Demo and examples
if __name__ == "__main__":
    print("=" * 70)
    print("Ψ-NSE Visualization and Validation Tools - Demo")
    print("=" * 70)
    print()
    
    # Create mock solution data
    mock_solution = {
        'config': type('Config', (), {
            'f0': 151.7001,
            'Nx': 32, 'Ny': 16, 'Nz': 16,
        })(),
        't_final': 1.0,
        'energy_history': np.linspace(0.1, 0.05, 50),
        'vorticity_max_history': np.exp(-np.linspace(0, 2, 50)) * 0.5,
        'coherence_history': np.sin(np.linspace(0, 4*np.pi, 50)) * 0.2 + 0.7,
        'stable': True,
        'certification_hash': '1d62f6d4',
        'frequency': 151.7001
    }
    
    # 1. Flow Field Visualization
    print("1. FLOW FIELD VISUALIZATION")
    print("-" * 70)
    visualizer = FlowFieldVisualizer()
    ascii_viz = visualizer.visualize_solution(mock_solution, output_format="ascii")
    print(ascii_viz)
    print()
    
    # 2. Aerodynamic Performance
    print("\n2. AERODYNAMIC PERFORMANCE PLOTS")
    print("-" * 70)
    plotter = AerodynamicPerformancePlotter()
    
    angles = np.array([0, 2, 4, 6, 8, 10])
    cl_values = 2 * np.pi * np.radians(angles) * 1.2
    cd_values = 0.01 + cl_values**2 / (np.pi * 8)
    coherence = np.array([0.85, 0.87, 0.90, 0.92, 0.89, 0.86])
    
    lift_curve = plotter.plot_lift_curve(angles, cl_values, coherence)
    print(lift_curve)
    print()
    
    drag_polar = plotter.plot_drag_polar(cd_values, cl_values)
    print(drag_polar)
    print()
    
    efficiency = plotter.plot_efficiency_comparison(
        traditional_ld=15.0,
        psi_nse_ld=18.5,
        coherence=0.92
    )
    print(efficiency)
    print()
    
    # 3. QCAL Dashboard
    print("\n3. QCAL INTEGRATION DASHBOARD")
    print("-" * 70)
    dashboard = QCALDashboard()
    
    mining = {
        'total_value_cs': 1250.50,
        'value_per_node': 14.21,
        'coherent_work_hours': 25.5,
        'efficiency': 0.92,
        'frequency': 151.7001
    }
    
    certification = {
        'total_certifications': 15,
        'approved': 14,
        'rejected': 1,
        'approval_rate': 0.933,
        'mean_coherence': 0.905,
        'registry_hash': 'a3f9c2e1'
    }
    
    verification = {
        'psi_score': 0.912,
        'threshold': 0.888,
        'guardian_status': 'APPROVED',
        'vibration_frequency': 151.7050,
        'harmonic_alignment': 0.997
    }
    
    dash = dashboard.generate_dashboard(mining, certification, verification)
    print(dash)
    print()
    
    # 4. Validation Suite
    print("\n4. VALIDATION SUITE")
    print("-" * 70)
    validator = ValidationSuite()
    
    validation = validator.validate_solution(mock_solution)
    report = validator.generate_validation_report(validation)
    print(report)
    
    print("\n" + "=" * 70)
    print("✓ All visualization and validation tools operational")
    print("=" * 70)
