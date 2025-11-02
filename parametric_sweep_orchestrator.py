#!/usr/bin/env python3
"""
Parametric Sweep Orchestrator
Generates parameter sweep packages for numerical simulations
"""

import os
import json
import itertools
from datetime import datetime
from typing import Dict, List, Any

# Constants for time estimation
BASE_GRID_SIZE = 32
BASE_TIME_STEP = 0.01
BASE_COMPUTATION_TIME_MINUTES = 5.0


class ParametricSweepOrchestrator:
    """Orchestrates the generation of parametric sweep packages"""
    
    def __init__(self, output_dir: str = "parametric_sweep_packages"):
        self.output_dir = output_dir
        self.packages = []
        
    def generate_parameter_grid(self) -> List[Dict[str, Any]]:
        """Generate a grid of parameter combinations for sweep"""
        
        # Define parameter ranges for the Navier-Stokes simulation
        reynolds_numbers = [100, 500, 1000, 2000, 5000]
        grid_sizes = [32, 64, 128]
        time_steps = [0.001, 0.005, 0.01]
        viscosities = [0.01, 0.001, 0.0001]
        
        # Generate all combinations
        param_grid = []
        param_id = 0
        
        for re, grid, dt, nu in itertools.product(
            reynolds_numbers, grid_sizes, time_steps, viscosities
        ):
            # Calculate priority based on computational cost and scientific interest
            priority = self._calculate_priority(re, grid, dt, nu)
            
            param_set = {
                "id": param_id,
                "reynolds": re,
                "grid_size": grid,
                "time_step": dt,
                "viscosity": nu,
                "priority": priority,
                "status": "pending",
                "estimated_time_minutes": self._estimate_time(grid, dt),
                "created_at": datetime.now().isoformat()
            }
            
            param_grid.append(param_set)
            param_id += 1
        
        return param_grid
    
    def _calculate_priority(self, re: float, grid: int, dt: float, nu: float) -> str:
        """Calculate priority level based on parameters"""
        # High priority: moderate Reynolds, reasonable grid
        if 500 <= re <= 2000 and grid >= 64:
            return "HIGH"
        # Medium priority: broader range
        elif re <= 5000 and grid >= 32:
            return "MEDIUM"
        else:
            return "LOW"
    
    def _estimate_time(self, grid: int, dt: float) -> float:
        """Estimate computation time in minutes"""
        # Simple heuristic: time scales with grid^3 and inversely with dt
        base_time = (grid / BASE_GRID_SIZE) ** 3 * (BASE_TIME_STEP / dt)
        return round(base_time * BASE_COMPUTATION_TIME_MINUTES, 2)
    
    def create_packages(self) -> None:
        """Create parameter sweep packages"""
        print("Generating parameter sweep packages...")
        
        # Create output directory
        os.makedirs(self.output_dir, exist_ok=True)
        
        # Generate parameter grid
        self.packages = self.generate_parameter_grid()
        
        # Save individual packages
        for package in self.packages:
            package_file = os.path.join(
                self.output_dir, 
                f"package_{package['id']:04d}.json"
            )
            with open(package_file, 'w') as f:
                json.dump(package, f, indent=2)
        
        # Create priority summary
        self._create_priority_summary()
        
        # Create package index
        self._create_package_index()
        
        print(f"✅ Created {len(self.packages)} parameter sweep packages")
        print(f"📁 Output directory: {self.output_dir}")
    
    def _create_priority_summary(self) -> None:
        """Create a summary of packages by priority"""
        summary = {
            "total_packages": len(self.packages),
            "created_at": datetime.now().isoformat(),
            "priority_breakdown": {
                "HIGH": [],
                "MEDIUM": [],
                "LOW": []
            }
        }
        
        for package in self.packages:
            priority = package['priority']
            summary['priority_breakdown'][priority].append({
                "id": package['id'],
                "reynolds": package['reynolds'],
                "grid_size": package['grid_size'],
                "estimated_time_minutes": package['estimated_time_minutes']
            })
        
        # Add counts
        summary['priority_counts'] = {
            "HIGH": len(summary['priority_breakdown']['HIGH']),
            "MEDIUM": len(summary['priority_breakdown']['MEDIUM']),
            "LOW": len(summary['priority_breakdown']['LOW'])
        }
        
        # Save summary
        summary_file = os.path.join(self.output_dir, "priority_summary.json")
        with open(summary_file, 'w') as f:
            json.dump(summary, f, indent=2)
    
    def _create_package_index(self) -> None:
        """Create an index of all packages"""
        index = {
            "total_packages": len(self.packages),
            "created_at": datetime.now().isoformat(),
            "packages": [
                {
                    "id": pkg['id'],
                    "priority": pkg['priority'],
                    "status": pkg['status'],
                    "reynolds": pkg['reynolds'],
                    "grid_size": pkg['grid_size']
                }
                for pkg in self.packages
            ]
        }
        
        index_file = os.path.join(self.output_dir, "package_index.json")
        with open(index_file, 'w') as f:
            json.dump(index, f, indent=2)


def main():
    """Main entry point"""
    orchestrator = ParametricSweepOrchestrator()
    orchestrator.create_packages()
    
    print("\n📊 Summary:")
    print(f"   - Total packages: {len(orchestrator.packages)}")
    
    # Count by priority
    priority_counts = {}
    for pkg in orchestrator.packages:
        priority = pkg['priority']
        priority_counts[priority] = priority_counts.get(priority, 0) + 1
    
    for priority, count in sorted(priority_counts.items()):
        print(f"   - {priority} priority: {count} packages")
    
    print("\n✨ Next step: Run './quickstart_parametric_sweep.sh' for execution options")


if __name__ == "__main__":
    main()
