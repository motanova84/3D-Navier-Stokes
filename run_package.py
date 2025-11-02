#!/usr/bin/env python3
"""
Run Package
Executes a specific parameter sweep package
"""

import os
import sys
import json
import argparse
import time
from datetime import datetime
from typing import Dict, Any


class PackageRunner:
    """Runs a specific parameter sweep package"""
    
    def __init__(self, package_dir: str = "parametric_sweep_packages"):
        self.package_dir = package_dir
        self.results_dir = os.path.join(package_dir, "results")
        os.makedirs(self.results_dir, exist_ok=True)
    
    def load_package(self, package_id: int) -> Dict[str, Any]:
        """Load a package configuration"""
        package_file = os.path.join(
            self.package_dir,
            f"package_{package_id:04d}.json"
        )
        
        if not os.path.exists(package_file):
            raise FileNotFoundError(f"Package {package_id} not found: {package_file}")
        
        with open(package_file, 'r') as f:
            return json.load(f)
    
    def run_simulation(self, package: Dict[str, Any]) -> Dict[str, Any]:
        """Run the simulation with the given parameters"""
        print(f"\n{'='*70}")
        print(f"Running Package ID: {package['id']}")
        print(f"{'='*70}")
        print(f"Parameters:")
        print(f"  Reynolds Number: {package['reynolds']}")
        print(f"  Grid Size: {package['grid_size']}³")
        print(f"  Time Step: {package['time_step']}")
        print(f"  Viscosity: {package['viscosity']}")
        print(f"  Priority: {package['priority']}")
        print(f"  Estimated Time: {package['estimated_time_minutes']} minutes")
        print(f"{'='*70}\n")
        
        start_time = time.time()
        
        # Simulate the computation (in a real implementation, this would run the actual solver)
        print("Starting simulation...")
        
        # Mock simulation with progress updates
        simulation_steps = 10
        for step in range(simulation_steps):
            time.sleep(0.1)  # Simulate computation time
            progress = (step + 1) / simulation_steps * 100
            print(f"Progress: {progress:.1f}%")
        
        end_time = time.time()
        elapsed_time = end_time - start_time
        
        # Generate mock results
        results = {
            "package_id": package['id'],
            "status": "completed",
            "start_time": datetime.fromtimestamp(start_time).isoformat(),
            "end_time": datetime.fromtimestamp(end_time).isoformat(),
            "elapsed_seconds": round(elapsed_time, 2),
            "parameters": {
                "reynolds": package['reynolds'],
                "grid_size": package['grid_size'],
                "time_step": package['time_step'],
                "viscosity": package['viscosity']
            },
            "results": {
                "final_energy": 1.234,  # Mock value
                "max_velocity": 2.345,  # Mock value
                "convergence": True,
                "iterations": 100
            }
        }
        
        print(f"\n✅ Simulation completed in {elapsed_time:.2f} seconds")
        
        return results
    
    def save_results(self, results: Dict[str, Any]) -> None:
        """Save simulation results"""
        result_file = os.path.join(
            self.results_dir,
            f"result_{results['package_id']:04d}.json"
        )
        
        with open(result_file, 'w') as f:
            json.dump(results, f, indent=2)
        
        print(f"📊 Results saved to: {result_file}")
    
    def update_package_status(self, package_id: int, status: str) -> None:
        """Update the status of a package"""
        package_file = os.path.join(
            self.package_dir,
            f"package_{package_id:04d}.json"
        )
        
        with open(package_file, 'r') as f:
            package = json.load(f)
        
        package['status'] = status
        package['last_updated'] = datetime.now().isoformat()
        
        with open(package_file, 'w') as f:
            json.dump(package, f, indent=2)
    
    def run(self, package_id: int) -> None:
        """Main execution method"""
        try:
            # Load package
            print(f"Loading package {package_id}...")
            package = self.load_package(package_id)
            
            # Update status to running
            self.update_package_status(package_id, "running")
            
            # Run simulation
            results = self.run_simulation(package)
            
            # Save results
            self.save_results(results)
            
            # Update status to completed
            self.update_package_status(package_id, "completed")
            
            print(f"\n✅ Package {package_id} completed successfully!")
            
        except Exception as e:
            print(f"\n❌ Error running package {package_id}: {e}")
            try:
                self.update_package_status(package_id, "failed")
            except:
                pass
            sys.exit(1)


def main():
    """Main entry point"""
    parser = argparse.ArgumentParser(
        description="Run a specific parameter sweep package"
    )
    parser.add_argument(
        "--package-id",
        type=int,
        required=True,
        help="ID of the package to run"
    )
    parser.add_argument(
        "--package-dir",
        type=str,
        default="parametric_sweep_packages",
        help="Directory containing packages"
    )
    
    args = parser.parse_args()
    
    runner = PackageRunner(package_dir=args.package_dir)
    runner.run(args.package_id)


if __name__ == "__main__":
    main()
