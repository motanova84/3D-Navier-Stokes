#!/usr/bin/env python3
"""
═══════════════════════════════════════════════════════════════
    PARAMETRIC SWEEP ORCHESTRATOR
    
    Generates organized packages of simulations for parametric sweeps
    Each package contains multiple simulations with related parameters
═══════════════════════════════════════════════════════════════
"""

import json
import os
from pathlib import Path
from typing import Dict, List, Tuple
from datetime import datetime
import itertools


class ParametricSweepOrchestrator:
    """
    Orchestrates parametric sweeps by generating organized simulation packages
    """
    
    def __init__(self, output_dir: str = "parametric_sweep_packages"):
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(exist_ok=True)
        
    def define_parameter_space(self) -> Dict:
        """
        Define the parameter space for the sweeps
        Based on typical DNS parameters for Ψ-NSE simulations
        """
        parameter_space = {
            # Viscosity (Reynolds number proxy)
            'nu': [1e-2, 1e-3, 1e-4],  # High, medium, low viscosity
            
            # Grid resolution
            'N': [64, 128],  # Spatial resolution
            
            # Coupling strength
            'alpha_coupling': [0.01, 0.1, 0.5],  # QFT coupling parameter
            
            # Simulation time
            'T_max': [2.0, 5.0, 10.0],  # Short, medium, long runs
            
            # Initial condition type
            'ic_type': ['taylor_green', 'random', 'shear_layer'],
            
            # Time step
            'dt': [0.001, 0.0005]
        }
        
        return parameter_space
    
    def prioritize_combinations(self, combinations: List[Dict]) -> Dict[str, List[Dict]]:
        """
        Classify parameter combinations by priority
        
        HIGH: Standard cases, most likely to provide useful results
        MEDIUM: Extended cases, more expensive but valuable
        LOW: Edge cases, very expensive or extreme parameters
        """
        high_priority = []
        medium_priority = []
        low_priority = []
        
        for combo in combinations:
            # High priority: Standard resolution, moderate parameters
            if (combo['N'] == 64 and 
                combo['nu'] >= 1e-3 and 
                combo['T_max'] <= 5.0 and
                combo['alpha_coupling'] <= 0.1):
                high_priority.append(combo)
            
            # Low priority: High resolution + extreme parameters
            elif (combo['N'] == 128 and 
                  (combo['nu'] == 1e-4 or combo['T_max'] == 10.0)):
                low_priority.append(combo)
            
            # Medium: Everything else
            else:
                medium_priority.append(combo)
        
        return {
            'HIGH': high_priority,
            'MEDIUM': medium_priority,
            'LOW': low_priority
        }
    
    def create_packages(self, sims_per_package: int = 10) -> Dict:
        """
        Create simulation packages
        
        Args:
            sims_per_package: Number of simulations per package
            
        Returns:
            Dictionary with package metadata
        """
        print("🔧 Generating parametric sweep packages...")
        print("="*60)
        
        # Define parameter space
        param_space = self.define_parameter_space()
        
        # Generate all combinations
        keys = list(param_space.keys())
        values = [param_space[k] for k in keys]
        all_combinations = [dict(zip(keys, combo)) 
                           for combo in itertools.product(*values)]
        
        print(f"Total parameter combinations: {len(all_combinations)}")
        
        # Prioritize combinations
        prioritized = self.prioritize_combinations(all_combinations)
        
        print(f"\nPriority distribution:")
        print(f"  HIGH:   {len(prioritized['HIGH'])} simulations")
        print(f"  MEDIUM: {len(prioritized['MEDIUM'])} simulations")
        print(f"  LOW:    {len(prioritized['LOW'])} simulations")
        
        # Create packages
        packages = []
        package_id = 0
        
        for priority in ['HIGH', 'MEDIUM', 'LOW']:
            sims = prioritized[priority]
            
            # Split into packages
            for i in range(0, len(sims), sims_per_package):
                package = {
                    'package_id': package_id,
                    'priority': priority,
                    'simulations': sims[i:i+sims_per_package],
                    'status': 'pending',
                    'created_at': datetime.now().isoformat()
                }
                
                # Save package to file
                package_file = self.output_dir / f"package_{package_id:04d}.json"
                with open(package_file, 'w') as f:
                    json.dump(package, f, indent=2)
                
                packages.append({
                    'package_id': package_id,
                    'priority': priority,
                    'num_simulations': len(package['simulations']),
                    'file': str(package_file)
                })
                
                package_id += 1
        
        # Create metadata file
        metadata = {
            'total_packages': len(packages),
            'total_simulations': len(all_combinations),
            'created_at': datetime.now().isoformat(),
            'packages': packages
        }
        
        metadata_file = self.output_dir / "metadata.json"
        with open(metadata_file, 'w') as f:
            json.dump(metadata, f, indent=2)
        
        # Create priority summary
        priority_summary = {}
        for priority in ['HIGH', 'MEDIUM', 'LOW']:
            priority_packages = [p for p in packages if p['priority'] == priority]
            priority_summary[priority] = [p['package_id'] for p in priority_packages]
        
        priority_file = self.output_dir / "priority_summary.json"
        with open(priority_file, 'w') as f:
            json.dump(priority_summary, f, indent=2)
        
        print(f"\n✓ Created {len(packages)} packages")
        print(f"✓ Metadata saved to: {metadata_file}")
        print(f"✓ Priority summary: {priority_file}")
        
        return metadata
    
    def list_packages(self, priority: str = None) -> List[Dict]:
        """
        List available packages
        
        Args:
            priority: Filter by priority (HIGH, MEDIUM, LOW) or None for all
        """
        metadata_file = self.output_dir / "metadata.json"
        
        if not metadata_file.exists():
            print("❌ No packages found. Run create_packages() first.")
            return []
        
        with open(metadata_file, 'r') as f:
            metadata = json.load(f)
        
        packages = metadata['packages']
        
        if priority:
            packages = [p for p in packages if p['priority'] == priority]
        
        return packages


def main():
    """Main entry point for package generation"""
    import argparse
    
    parser = argparse.ArgumentParser(
        description='Generate parametric sweep packages for Ψ-NSE simulations'
    )
    parser.add_argument(
        '--sims-per-package',
        type=int,
        default=10,
        help='Number of simulations per package (default: 10)'
    )
    parser.add_argument(
        '--output-dir',
        type=str,
        default='parametric_sweep_packages',
        help='Output directory for packages'
    )
    parser.add_argument(
        '--list',
        action='store_true',
        help='List existing packages'
    )
    parser.add_argument(
        '--priority',
        type=str,
        choices=['HIGH', 'MEDIUM', 'LOW'],
        help='Filter by priority when listing'
    )
    
    args = parser.parse_args()
    
    orchestrator = ParametricSweepOrchestrator(output_dir=args.output_dir)
    
    if args.list:
        packages = orchestrator.list_packages(priority=args.priority)
        print(f"\n📦 Found {len(packages)} packages:")
        for pkg in packages:
            print(f"  Package {pkg['package_id']:04d}: "
                  f"{pkg['priority']:6s} priority, "
                  f"{pkg['num_simulations']} simulations")
    else:
        orchestrator.create_packages(sims_per_package=args.sims_per_package)


if __name__ == "__main__":
    main()
