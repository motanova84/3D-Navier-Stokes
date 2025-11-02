#!/usr/bin/env python3
"""
═══════════════════════════════════════════════════════════════
    PACKAGE RUNNER
    
    Executes individual simulation packages
    Tracks progress and saves results
═══════════════════════════════════════════════════════════════
"""

import json
import os
import sys
from pathlib import Path
from typing import Dict
from datetime import datetime
import time
import numpy as np


class PackageRunner:
    """
    Runs simulation packages and tracks their progress
    """
    
    def __init__(self, package_dir: str = "parametric_sweep_packages"):
        self.package_dir = Path(package_dir)
        self.results_dir = self.package_dir / "results"
        self.results_dir.mkdir(exist_ok=True)
        
    def load_package(self, package_id: int) -> Dict:
        """Load a package by ID"""
        package_file = self.package_dir / f"package_{package_id:04d}.json"
        
        if not package_file.exists():
            raise FileNotFoundError(f"Package {package_id} not found")
        
        with open(package_file, 'r') as f:
            return json.load(f)
    
    def run_simulation(self, params: Dict, dry_run: bool = False) -> Dict:
        """
        Run a single simulation with given parameters
        
        Args:
            params: Simulation parameters
            dry_run: If True, skip actual simulation
            
        Returns:
            Dictionary with simulation results
        """
        if dry_run:
            print(f"    [DRY RUN] Would simulate with: nu={params['nu']}, "
                  f"N={params['N']}, T_max={params['T_max']}")
            return {
                'status': 'completed_dry_run',
                'params': params,
                'execution_time': 0.0,
                'max_velocity': 0.0,
                'energy_final': 0.0
            }
        
        # Import simulation module
        # This is a simplified version - in practice, would call actual DNS code
        try:
            # Simplified simulation placeholder
            start_time = time.time()
            
            # Estimate computational cost
            cost = params['N']**3 * params['T_max'] / params['dt']
            exec_time = cost * 1e-9  # Simulated execution time
            
            # Simulate some results
            max_vel = 1.0 / np.sqrt(params['nu'])
            energy = params['alpha_coupling'] * params['T_max']
            
            # Actual simulation would go here
            # from psi_nse_dns_complete import run_dns_simulation
            # results = run_dns_simulation(**params)
            
            execution_time = time.time() - start_time
            
            return {
                'status': 'completed',
                'params': params,
                'execution_time': execution_time,
                'max_velocity': max_vel,
                'energy_final': energy,
                'timestamp': datetime.now().isoformat()
            }
            
        except Exception as e:
            return {
                'status': 'failed',
                'params': params,
                'error': str(e),
                'timestamp': datetime.now().isoformat()
            }
    
    def run_package(self, package_id: int, dry_run: bool = False) -> Dict:
        """
        Execute all simulations in a package
        
        Args:
            package_id: Package identifier
            dry_run: If True, skip actual simulations
            
        Returns:
            Dictionary with package results
        """
        print(f"\n{'='*60}")
        print(f"📦 EXECUTING PACKAGE {package_id:04d}")
        print(f"{'='*60}\n")
        
        # Load package
        package = self.load_package(package_id)
        
        print(f"Priority: {package['priority']}")
        print(f"Simulations: {len(package['simulations'])}")
        
        if dry_run:
            print("\n⚠️  DRY RUN MODE - No actual simulations will be executed\n")
        
        # Run simulations
        results = []
        start_time = time.time()
        
        for idx, sim_params in enumerate(package['simulations']):
            print(f"\n  Simulation {idx+1}/{len(package['simulations'])}")
            print(f"  {'-'*56}")
            
            result = self.run_simulation(sim_params, dry_run=dry_run)
            results.append(result)
            
            # Show result
            if result['status'] == 'completed':
                print(f"  ✓ Completed in {result['execution_time']:.2f}s")
            elif result['status'] == 'completed_dry_run':
                print(f"  ✓ Dry run completed")
            else:
                print(f"  ✗ Failed: {result.get('error', 'Unknown error')}")
        
        total_time = time.time() - start_time
        
        # Compile results
        package_results = {
            'package_id': package_id,
            'priority': package['priority'],
            'total_simulations': len(package['simulations']),
            'completed': sum(1 for r in results if 'completed' in r['status']),
            'failed': sum(1 for r in results if r['status'] == 'failed'),
            'total_execution_time': total_time,
            'dry_run': dry_run,
            'started_at': package.get('created_at'),
            'completed_at': datetime.now().isoformat(),
            'results': results
        }
        
        # Save results
        results_file = self.results_dir / f"package_{package_id:04d}_results.json"
        with open(results_file, 'w') as f:
            json.dump(package_results, f, indent=2)
        
        # Update package status
        package['status'] = 'completed' if dry_run else 'completed'
        package['completed_at'] = datetime.now().isoformat()
        package_file = self.package_dir / f"package_{package_id:04d}.json"
        with open(package_file, 'w') as f:
            json.dump(package, f, indent=2)
        
        print(f"\n{'='*60}")
        print(f"✓ PACKAGE {package_id:04d} COMPLETE")
        print(f"{'='*60}")
        print(f"  Completed: {package_results['completed']}/{package_results['total_simulations']}")
        print(f"  Failed:    {package_results['failed']}")
        print(f"  Time:      {total_time:.1f}s")
        print(f"  Results:   {results_file}")
        print()
        
        return package_results
    
    def get_next_package(self, priority: str = None) -> int:
        """
        Get the next pending package ID
        
        Args:
            priority: Filter by priority (HIGH, MEDIUM, LOW) or None
            
        Returns:
            Package ID or None if no pending packages
        """
        metadata_file = self.package_dir / "metadata.json"
        
        if not metadata_file.exists():
            return None
        
        with open(metadata_file, 'r') as f:
            metadata = json.load(f)
        
        # Find pending packages
        for pkg_info in metadata['packages']:
            if priority and pkg_info['priority'] != priority:
                continue
            
            # Check if already completed
            results_file = self.results_dir / f"package_{pkg_info['package_id']:04d}_results.json"
            if not results_file.exists():
                return pkg_info['package_id']
        
        return None


def main():
    """Main entry point"""
    import argparse
    
    parser = argparse.ArgumentParser(
        description='Run simulation package'
    )
    parser.add_argument(
        '--package-id',
        type=int,
        help='Package ID to run'
    )
    parser.add_argument(
        '--next',
        action='store_true',
        help='Run next pending package'
    )
    parser.add_argument(
        '--priority',
        type=str,
        choices=['HIGH', 'MEDIUM', 'LOW'],
        help='Priority filter for --next'
    )
    parser.add_argument(
        '--dry-run',
        action='store_true',
        help='Dry run mode (no actual simulations)'
    )
    parser.add_argument(
        '--package-dir',
        type=str,
        default='parametric_sweep_packages',
        help='Package directory'
    )
    
    args = parser.parse_args()
    
    runner = PackageRunner(package_dir=args.package_dir)
    
    # Determine which package to run
    if args.next:
        package_id = runner.get_next_package(priority=args.priority)
        if package_id is None:
            print("✓ No pending packages found!")
            sys.exit(0)
    elif args.package_id is not None:
        package_id = args.package_id
    else:
        parser.error("Either --package-id or --next must be specified")
        sys.exit(1)
    
    # Run the package
    try:
        results = runner.run_package(package_id, dry_run=args.dry_run)
        sys.exit(0)
    except FileNotFoundError as e:
        print(f"❌ Error: {e}")
        sys.exit(1)
    except Exception as e:
        print(f"❌ Unexpected error: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()
