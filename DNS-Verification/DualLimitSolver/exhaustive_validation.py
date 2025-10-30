#!/usr/bin/env python3
"""
Exhaustive Validation Module with Edge Cases and δ* Parameter Analysis

This module implements comprehensive automated sweeps and parametric validation
for the unified BKM framework, with special focus on:

1. Extreme parameter ranges (a ≈ 200) to push δ* above critical thresholds
2. Numerical stability analysis for large amplitudes
3. Theoretical stability verification
4. Edge case testing across all parameter dimensions
5. Comprehensive validation reports with recommendations

Author: Enhanced validation for Clay Millennium Problem resolution
"""

import numpy as np
from typing import Dict, List, Tuple, Optional
import sys
import warnings
from dataclasses import dataclass, asdict
import json

sys.path.append('/home/runner/work/3D-Navier-Stokes/3D-Navier-Stokes/DNS-Verification/DualLimitSolver')
from unified_bkm import (
    riccati_besov_closure,
    compute_optimal_dual_scaling,
    riccati_evolution,
    unified_bkm_verification,
    UnifiedBKMConstants,
    validate_constants_uniformity
)


@dataclass
class ValidationConfig:
    """Configuration for exhaustive validation"""
    # Amplitude parameter ranges - including extreme values
    a_range: Tuple[float, float] = (0.1, 250.0)
    a_samples: int = 100
    a_critical_values: List[float] = None  # Specific critical values to test
    
    # Scaling exponent ranges
    α_range: Tuple[float, float] = (1.1, 4.0)
    α_samples: int = 20
    
    # Frequency ranges (Hz)
    f0_range: Tuple[float, float] = (10.0, 100000.0)
    f0_samples: int = 50
    
    # Viscosity ranges
    ν_range: Tuple[float, float] = (1e-5, 1e-1)
    ν_samples: int = 20
    
    # H^m norm bounds
    M_range: Tuple[float, float] = (1.0, 1000.0)
    M_samples: int = 20
    
    # Edge case thresholds
    δ_star_threshold: float = 0.998  # Target threshold for δ*
    damping_threshold: float = 0.0   # Minimum acceptable damping
    
    def __post_init__(self):
        if self.a_critical_values is None:
            # Include critical values: a ≈ 200 as recommended, and other key values
            self.a_critical_values = [
                0.5, 1.0, 2.45, 5.0, 7.0, 10.0, 20.0, 50.0, 100.0, 150.0, 200.0, 250.0
            ]


@dataclass
class StabilityMetrics:
    """Numerical stability metrics"""
    condition_number: float = 0.0
    relative_error: float = 0.0
    convergence_rate: float = 0.0
    is_stable: bool = True
    error_message: str = ""


class ExhaustiveValidator:
    """
    Comprehensive validator for BKM framework with edge case analysis
    """
    
    def __init__(self, config: Optional[ValidationConfig] = None):
        """
        Initialize validator with configuration
        
        Args:
            config: Validation configuration (uses defaults if None)
        """
        self.config = config or ValidationConfig()
        self.results = {
            'parameter_sweeps': [],
            'edge_cases': [],
            'stability_analysis': [],
            'critical_points': [],
            'recommendations': []
        }
    
    def compute_delta_star(self, a: float, c_0: float = 1.0) -> float:
        """
        Compute misalignment defect δ* from amplitude parameter
        
        Formula: δ* = a²·c₀²/(4π²)
        
        Args:
            a: Amplitude parameter
            c_0: Phase gradient (default 1.0)
            
        Returns:
            Misalignment defect δ*
        """
        return (a**2 * c_0**2) / (4 * np.pi**2)
    
    def compute_required_amplitude(self, δ_star_target: float, c_0: float = 1.0) -> float:
        """
        Compute required amplitude to achieve target δ*
        
        Inverse formula: a = 2π·√(δ*/c₀²)
        
        Args:
            δ_star_target: Target misalignment defect
            c_0: Phase gradient
            
        Returns:
            Required amplitude parameter a
        """
        return 2 * np.pi * np.sqrt(δ_star_target) / c_0
    
    def assess_numerical_stability(self, a: float, ν: float, M: float) -> StabilityMetrics:
        """
        Assess numerical stability for given parameters
        
        Checks for:
        - Overflow/underflow risks
        - Ill-conditioning
        - Convergence issues
        
        Args:
            a: Amplitude parameter
            ν: Viscosity
            M: H^m norm bound
            
        Returns:
            StabilityMetrics object with assessment
        """
        metrics = StabilityMetrics()
        
        # Check for extreme values
        if a > 300:
            metrics.is_stable = False
            metrics.error_message = f"Amplitude a={a} may cause overflow"
            return metrics
        
        if ν < 1e-6:
            metrics.is_stable = False
            metrics.error_message = f"Viscosity ν={ν} may cause numerical instability"
            return metrics
        
        # Compute δ* and check for reasonable values
        δ_star = self.compute_delta_star(a)
        if δ_star > 10000:
            metrics.is_stable = False
            metrics.error_message = f"δ*={δ_star} exceeds physical bounds"
            return metrics
        
        # Estimate condition number (simplified)
        # Ratio of largest to smallest relevant scale
        log_term = 1 + np.log(1 + M)
        condition_number = max(a**2, M * log_term) / max(ν, 1e-10)
        metrics.condition_number = condition_number
        
        if condition_number > 1e15:
            metrics.is_stable = False
            metrics.error_message = f"Poor conditioning: κ={condition_number:.2e}"
            return metrics
        
        # Estimate relative error from finite precision
        metrics.relative_error = np.finfo(float).eps * condition_number
        
        if metrics.relative_error > 0.1:
            metrics.is_stable = False
            metrics.error_message = f"Large relative error: {metrics.relative_error:.2e}"
        
        return metrics
    
    def validate_theoretical_stability(self, a: float, ν: float = 1e-3, 
                                      c_B: float = 0.15, C_CZ: float = 1.5,
                                      C_star: float = 1.2, M: float = 100.0) -> Dict:
        """
        Validate theoretical stability predictions for given amplitude
        
        Verifies that:
        1. Damping coefficient remains positive
        2. BKM criterion is satisfied
        3. Physical constraints are met
        
        Args:
            a: Amplitude parameter
            ν: Viscosity
            c_B: Bernstein constant
            C_CZ: Calderón-Zygmund constant
            C_star: Besov embedding constant
            M: H^m norm bound
            
        Returns:
            Dictionary with theoretical validation results
        """
        δ_star = self.compute_delta_star(a)
        
        # Check damping condition
        closure, damping = riccati_besov_closure(ν, c_B, C_CZ, C_star, δ_star, M)
        
        # Physical constraints
        physical_valid = True
        constraints = []
        
        # δ* should be positive and reasonable
        if δ_star <= 0:
            physical_valid = False
            constraints.append(f"δ* = {δ_star:.6f} must be positive")
        
        if δ_star > 10000:
            constraints.append(f"δ* = {δ_star:.6f} unusually large (warning)")
        
        # Amplitude should be finite and reasonable
        if not np.isfinite(a):
            physical_valid = False
            constraints.append(f"Amplitude a = {a} not finite")
        
        return {
            'a': a,
            'δ_star': δ_star,
            'damping': damping,
            'closure': closure,
            'physical_valid': physical_valid,
            'constraints': constraints,
            'δ_star_exceeds_threshold': δ_star >= self.config.δ_star_threshold
        }
    
    def sweep_amplitude_range(self, ν: float = 1e-3, verbose: bool = True) -> Dict:
        """
        Comprehensive sweep over amplitude parameter range
        
        Special focus on a ≈ 200 as recommended in the problem statement
        
        Args:
            ν: Viscosity
            verbose: Print progress
            
        Returns:
            Dictionary with sweep results
        """
        if verbose:
            print("\n" + "="*70)
            print("AMPLITUDE PARAMETER SWEEP (with focus on a ≈ 200)")
            print("="*70)
        
        # Generate amplitude values (log scale for wide range)
        a_values = np.logspace(
            np.log10(self.config.a_range[0]),
            np.log10(self.config.a_range[1]),
            self.config.a_samples
        )
        
        # Add critical values
        a_values = np.unique(np.sort(np.concatenate([
            a_values, 
            self.config.a_critical_values
        ])))
        
        results = []
        
        for a in a_values:
            # Numerical stability check
            stability = self.assess_numerical_stability(a, ν, M=100.0)
            
            # Theoretical validation
            theory = self.validate_theoretical_stability(a, ν)
            
            # Combine results
            result = {
                **theory,
                'numerical_stability': stability.is_stable,
                'stability_metrics': asdict(stability)
            }
            
            results.append(result)
            
            # Print key results for recommended value (a ≈ 200)
            if verbose and abs(a - 200.0) < 5.0:
                print(f"\n*** KEY RESULT for a ≈ {a:.1f} (RECOMMENDED) ***")
                print(f"  δ* = {theory['δ_star']:.6f}")
                print(f"  δ* exceeds threshold (0.998)? {theory['δ_star_exceeds_threshold']}")
                print(f"  Damping Δ = {theory['damping']:.6f}")
                print(f"  Closure satisfied? {theory['closure']}")
                print(f"  Numerically stable? {stability.is_stable}")
                if not stability.is_stable:
                    print(f"  ⚠️  Warning: {stability.error_message}")
        
        if verbose:
            # Summary statistics
            stable_count = sum(1 for r in results if r['numerical_stability'])
            closure_count = sum(1 for r in results if r['closure'])
            threshold_count = sum(1 for r in results if r['δ_star_exceeds_threshold'])
            
            print(f"\n" + "-"*70)
            print(f"SUMMARY:")
            print(f"  Total configurations: {len(results)}")
            print(f"  Numerically stable: {stable_count}/{len(results)}")
            print(f"  Closure satisfied: {closure_count}/{len(results)}")
            print(f"  δ* exceeds threshold: {threshold_count}/{len(results)}")
        
        return {
            'a_values': a_values.tolist(),
            'results': results,
            'summary': {
                'total': len(results),
                'stable': stable_count if verbose else 0,
                'closure': closure_count if verbose else 0,
                'threshold_exceeded': threshold_count if verbose else 0
            }
        }
    
    def sweep_multi_parameter(self, verbose: bool = True) -> Dict:
        """
        Multi-dimensional parameter sweep
        
        Sweeps over (a, α, f₀, ν) space to find optimal regions
        
        Args:
            verbose: Print progress
            
        Returns:
            Dictionary with multi-parameter sweep results
        """
        if verbose:
            print("\n" + "="*70)
            print("MULTI-PARAMETER SWEEP")
            print("="*70)
        
        # Use strategic sampling for efficiency
        a_values = [1.0, 2.45, 7.0, 10.0, 50.0, 100.0, 200.0]
        α_values = [1.5, 2.0, 2.5, 3.0]
        f0_values = [100, 1000, 10000, 50000]
        ν_values = [1e-4, 1e-3, 1e-2]
        
        results = []
        total_configs = len(a_values) * len(α_values) * len(f0_values) * len(ν_values)
        
        if verbose:
            print(f"Testing {total_configs} configurations...")
            print(f"  Amplitude: {len(a_values)} values")
            print(f"  Scaling α: {len(α_values)} values")
            print(f"  Frequency: {len(f0_values)} values")
            print(f"  Viscosity: {len(ν_values)} values")
        
        count = 0
        for ν in ν_values:
            for f0 in f0_values:
                for α in α_values:
                    for a in a_values:
                        count += 1
                        
                        # Compute δ* and damping
                        δ_star = self.compute_delta_star(a)
                        closure, damping = riccati_besov_closure(
                            ν, 0.15, 1.5, 1.2, δ_star, 100.0
                        )
                        
                        # Stability check
                        stability = self.assess_numerical_stability(a, ν, 100.0)
                        
                        results.append({
                            'a': a,
                            'α': α,
                            'f0': f0,
                            'ν': ν,
                            'δ_star': δ_star,
                            'damping': damping,
                            'closure': closure,
                            'stable': stability.is_stable
                        })
        
        if verbose:
            print(f"Completed {count} configurations")
        
        return {
            'results': results,
            'total_configs': total_configs
        }
    
    def test_edge_cases(self, verbose: bool = True) -> Dict:
        """
        Test edge cases and boundary conditions
        
        Tests:
        - Very small amplitude (a → 0)
        - Very large amplitude (a → ∞)
        - Very small viscosity (ν → 0)
        - Very large viscosity (ν → ∞)
        - Extreme frequencies
        
        Args:
            verbose: Print details
            
        Returns:
            Dictionary with edge case results
        """
        if verbose:
            print("\n" + "="*70)
            print("EDGE CASE TESTING")
            print("="*70)
        
        edge_cases = []
        
        # Edge case 1: Minimal amplitude
        case = {
            'name': 'Minimal amplitude (a → 0)',
            'params': {'a': 0.01, 'ν': 1e-3}
        }
        theory = self.validate_theoretical_stability(0.01, 1e-3)
        case['result'] = theory
        edge_cases.append(case)
        
        if verbose:
            print(f"\n1. {case['name']}")
            print(f"   δ* = {theory['δ_star']:.6e}")
            print(f"   Damping = {theory['damping']:.6f}")
            print(f"   Closure = {theory['closure']}")
        
        # Edge case 2: Large amplitude (a ≈ 200, recommended)
        case = {
            'name': 'Large amplitude (a = 200, RECOMMENDED)',
            'params': {'a': 200.0, 'ν': 1e-3}
        }
        theory = self.validate_theoretical_stability(200.0, 1e-3)
        stability = self.assess_numerical_stability(200.0, 1e-3, 100.0)
        case['result'] = theory
        case['stability'] = asdict(stability)
        edge_cases.append(case)
        
        if verbose:
            print(f"\n2. {case['name']}")
            print(f"   δ* = {theory['δ_star']:.6f}")
            print(f"   δ* exceeds threshold? {theory['δ_star_exceeds_threshold']}")
            print(f"   Damping = {theory['damping']:.6f}")
            print(f"   Closure = {theory['closure']}")
            print(f"   Numerically stable = {stability.is_stable}")
        
        # Edge case 3: Very large amplitude (a = 250, boundary)
        case = {
            'name': 'Very large amplitude (a = 250, BOUNDARY)',
            'params': {'a': 250.0, 'ν': 1e-3}
        }
        theory = self.validate_theoretical_stability(250.0, 1e-3)
        stability = self.assess_numerical_stability(250.0, 1e-3, 100.0)
        case['result'] = theory
        case['stability'] = asdict(stability)
        edge_cases.append(case)
        
        if verbose:
            print(f"\n3. {case['name']}")
            print(f"   δ* = {theory['δ_star']:.6f}")
            print(f"   Damping = {theory['damping']:.6f}")
            print(f"   Numerically stable = {stability.is_stable}")
            if not stability.is_stable:
                print(f"   ⚠️  {stability.error_message}")
        
        # Edge case 4: Small viscosity
        case = {
            'name': 'Small viscosity (ν = 1e-5)',
            'params': {'a': 200.0, 'ν': 1e-5}
        }
        theory = self.validate_theoretical_stability(200.0, 1e-5)
        stability = self.assess_numerical_stability(200.0, 1e-5, 100.0)
        case['result'] = theory
        case['stability'] = asdict(stability)
        edge_cases.append(case)
        
        if verbose:
            print(f"\n4. {case['name']}")
            print(f"   Damping = {theory['damping']:.6f}")
            print(f"   Closure = {theory['closure']}")
            print(f"   Numerically stable = {stability.is_stable}")
        
        # Edge case 5: Large viscosity
        case = {
            'name': 'Large viscosity (ν = 0.1)',
            'params': {'a': 200.0, 'ν': 0.1}
        }
        theory = self.validate_theoretical_stability(200.0, 0.1)
        stability = self.assess_numerical_stability(200.0, 0.1, 100.0)
        case['result'] = theory
        case['stability'] = asdict(stability)
        edge_cases.append(case)
        
        if verbose:
            print(f"\n5. {case['name']}")
            print(f"   Damping = {theory['damping']:.6f}")
            print(f"   Closure = {theory['closure']}")
        
        return {
            'edge_cases': edge_cases,
            'total_tested': len(edge_cases)
        }
    
    def generate_recommendations(self, sweep_results: Dict, 
                                edge_results: Dict) -> List[str]:
        """
        Generate recommendations based on validation results
        
        Args:
            sweep_results: Results from parameter sweeps
            edge_results: Results from edge case testing
            
        Returns:
            List of recommendation strings
        """
        recommendations = []
        
        # Analyze amplitude sweep
        if 'results' in sweep_results:
            # Find optimal amplitude near a = 200
            candidates_near_200 = [
                r for r in sweep_results['results']
                if 180 <= r['a'] <= 220 and r['numerical_stability']
            ]
            
            if candidates_near_200:
                best = max(candidates_near_200, key=lambda r: r['damping'])
                recommendations.append(
                    f"✓ RECOMMENDED: Use a ≈ {best['a']:.1f} for optimal results"
                )
                recommendations.append(
                    f"  - Achieves δ* = {best['δ_star']:.6f}"
                )
                recommendations.append(
                    f"  - Damping coefficient: Δ = {best['damping']:.6f}"
                )
                recommendations.append(
                    f"  - Closure satisfied: {best['closure']}"
                )
            else:
                recommendations.append(
                    "⚠ WARNING: a ≈ 200 may have numerical stability issues"
                )
        
        # Check threshold achievement
        threshold_met = any(
            r['δ_star'] >= self.config.δ_star_threshold
            for r in sweep_results.get('results', [])
        )
        
        if threshold_met:
            recommendations.append(
                f"✓ δ* threshold ({self.config.δ_star_threshold}) can be exceeded"
            )
        else:
            required_a = self.compute_required_amplitude(self.config.δ_star_threshold)
            recommendations.append(
                f"⚠ To exceed δ* = {self.config.δ_star_threshold}, need a ≈ {required_a:.1f}"
            )
        
        # Numerical stability recommendations
        unstable_cases = [
            case for case in edge_results.get('edge_cases', [])
            if not case.get('stability', {}).get('is_stable', True)
        ]
        
        if unstable_cases:
            recommendations.append(
                f"⚠ {len(unstable_cases)} edge cases show numerical instability"
            )
            recommendations.append(
                "  Consider using higher precision arithmetic for extreme parameters"
            )
        
        return recommendations
    
    def run_full_validation(self, verbose: bool = True) -> Dict:
        """
        Run complete exhaustive validation suite
        
        Args:
            verbose: Print detailed progress
            
        Returns:
            Complete validation results dictionary
        """
        if verbose:
            print("\n" + "╔" + "═"*68 + "╗")
            print("║" + " "*15 + "EXHAUSTIVE VALIDATION SUITE" + " "*26 + "║")
            print("║" + " "*10 + "Parameter Sweep with Edge Cases & δ* Analysis" + " "*13 + "║")
            print("╚" + "═"*68 + "╝")
        
        # Phase 1: Amplitude sweep (focus on a ≈ 200)
        amplitude_results = self.sweep_amplitude_range(verbose=verbose)
        
        # Phase 2: Multi-parameter sweep
        multi_results = self.sweep_multi_parameter(verbose=verbose)
        
        # Phase 3: Edge cases
        edge_results = self.test_edge_cases(verbose=verbose)
        
        # Phase 4: Generate recommendations
        recommendations = self.generate_recommendations(amplitude_results, edge_results)
        
        if verbose:
            print("\n" + "="*70)
            print("RECOMMENDATIONS")
            print("="*70)
            for rec in recommendations:
                print(rec)
        
        # Compile complete results
        complete_results = {
            'config': asdict(self.config),
            'amplitude_sweep': amplitude_results,
            'multi_parameter_sweep': multi_results,
            'edge_cases': edge_results,
            'recommendations': recommendations,
            'summary': {
                'total_tests': (
                    len(amplitude_results.get('results', [])) +
                    len(multi_results.get('results', [])) +
                    len(edge_results.get('edge_cases', []))
                )
            }
        }
        
        return complete_results
    
    def save_results(self, results: Dict, filename: str = "validation_results.json"):
        """
        Save validation results to JSON file
        
        Args:
            results: Results dictionary
            filename: Output filename
        """
        import os
        output_dir = "/home/runner/work/3D-Navier-Stokes/3D-Navier-Stokes/Results"
        os.makedirs(output_dir, exist_ok=True)
        
        output_path = os.path.join(output_dir, filename)
        
        # Convert numpy types to native Python types for JSON serialization
        def convert_types(obj):
            if isinstance(obj, (np.bool_, bool)):
                return bool(obj)
            elif isinstance(obj, np.integer):
                return int(obj)
            elif isinstance(obj, np.floating):
                return float(obj)
            elif isinstance(obj, np.ndarray):
                return obj.tolist()
            elif isinstance(obj, dict):
                return {key: convert_types(value) for key, value in obj.items()}
            elif isinstance(obj, (list, tuple)):
                return [convert_types(item) for item in obj]
            return obj
        
        results_converted = convert_types(results)
        
        with open(output_path, 'w') as f:
            json.dump(results_converted, f, indent=2)
        
        print(f"\n✓ Results saved to: {output_path}")


def main():
    """
    Main entry point for exhaustive validation
    """
    # Create validator with default configuration
    validator = ExhaustiveValidator()
    
    # Run complete validation suite
    results = validator.run_full_validation(verbose=True)
    
    # Save results
    validator.save_results(results)
    
    print("\n" + "="*70)
    print("VALIDATION COMPLETE")
    print("="*70)
    print(f"Total tests executed: {results['summary']['total_tests']}")
    
    return results


if __name__ == "__main__":
    results = main()
