"""
═══════════════════════════════════════════════════════════════
  PARAMETRIC SWEEP ORCHESTRATOR
  
  Core functions for managing parametric sweep packages:
  - Package loading and management
  - Priority assignment
  - Computational cost estimation
  - Package execution
═══════════════════════════════════════════════════════════════
"""

import json
import numpy as np
from pathlib import Path
from typing import Dict, Any, Optional
import time

# ═══════════════════════════════════════════════════════════════
# PACKAGE MANAGEMENT
# ═══════════════════════════════════════════════════════════════

def load_package(package_id: int, packages_dir: str = 'parametric_sweep_packages') -> Dict[str, Any]:
    """
    Load a parametric sweep package from disk.
    
    Args:
        package_id: Package identifier
        packages_dir: Directory containing packages
        
    Returns:
        Dictionary containing package configuration
    """
    package_file = Path(packages_dir) / f"package_{package_id:04d}.json"
    
    if not package_file.exists():
        raise FileNotFoundError(f"Package {package_id} not found at {package_file}")
    
    with open(package_file, 'r') as f:
        package = json.load(f)
    
    package['package_id'] = package_id
    return package


def assign_priority(package: Dict[str, Any]) -> str:
    """
    Assign scientific priority to a package based on its parameters.
    
    Priority levels:
    - HIGH: Critical Reynolds numbers, extreme conditions
    - MEDIUM: Standard parameter ranges
    - LOW: Redundant or exploratory configurations
    
    Args:
        package: Package configuration dictionary
        
    Returns:
        Priority level: 'HIGH', 'MEDIUM', or 'LOW'
    """
    params = package.get('parameters', {})
    
    # Extract key parameters
    reynolds = params.get('reynolds', 1000)
    viscosity = params.get('viscosity', 1e-3)
    resolution = params.get('resolution', 64)
    
    # High priority: Critical Reynolds numbers (>1000), high resolution (>128)
    if reynolds > 1000 or resolution > 128:
        return 'HIGH'
    
    # Low priority: Very low Reynolds (<100), low resolution (<32)
    if reynolds < 100 and resolution < 32:
        return 'LOW'
    
    # Default: Medium priority
    return 'MEDIUM'


def estimate_computational_cost(package: Dict[str, Any]) -> Dict[str, float]:
    """
    Estimate computational resources required for a package.
    
    Args:
        package: Package configuration dictionary
        
    Returns:
        Dictionary with estimated costs:
        - time_hours: Estimated runtime in hours
        - memory_gb: Estimated memory usage in GB
        - disk_gb: Estimated disk space in GB
    """
    params = package.get('parameters', {})
    
    # Extract key parameters with defaults
    resolution = params.get('resolution', 64)
    timesteps = params.get('timesteps', 1000)
    reynolds = params.get('reynolds', 1000)
    
    # Estimate memory: roughly proportional to grid size^3
    grid_points = resolution ** 3
    memory_per_point = 8e-9  # 8 bytes per float64
    fields = 4  # velocity (3) + pressure (1)
    memory_gb = grid_points * memory_per_point * fields * 1.5  # 50% overhead
    
    # Estimate time: depends on resolution and timesteps
    # Base time for 64^3 grid with 1000 timesteps: 0.1 hours
    base_time = 0.1
    time_scaling = (resolution / 64) ** 3 * (timesteps / 1000)
    reynolds_factor = 1 + np.log10(reynolds / 1000) if reynolds > 1000 else 1
    time_hours = base_time * time_scaling * reynolds_factor
    
    # Estimate disk: output files and checkpoints
    disk_gb = memory_gb * 2  # Rough estimate for output storage
    
    return {
        'time_hours': max(0.01, time_hours),  # Minimum 0.01 hours
        'memory_gb': max(0.1, memory_gb),     # Minimum 0.1 GB
        'disk_gb': max(0.5, disk_gb)          # Minimum 0.5 GB
    }


# ═══════════════════════════════════════════════════════════════
# PACKAGE EXECUTION
# ═══════════════════════════════════════════════════════════════

def run_package(package_id: int, 
                output_dir: str = 'parametric_sweep_results',
                packages_dir: str = 'parametric_sweep_packages',
                n_workers: Optional[int] = None) -> Dict[str, Any]:
    """
    Execute a parametric sweep package.
    
    Args:
        package_id: Package identifier
        output_dir: Directory for output results
        packages_dir: Directory containing packages
        n_workers: Number of parallel workers (None = auto)
        
    Returns:
        Dictionary containing execution results
    """
    # Load package
    package = load_package(package_id, packages_dir)
    
    # Create output directory
    output_path = Path(output_dir)
    output_path.mkdir(parents=True, exist_ok=True)
    
    # Simulate execution (in real implementation, this would call actual solver)
    print(f"   Running package {package_id}...")
    print(f"   Parameters: {package.get('parameters', {})}")
    
    start_time = time.time()
    
    # Simulate computation time (scaled down for testing)
    cost = estimate_computational_cost(package)
    # For testing: simulate 1 second per estimated hour
    simulation_time = min(cost['time_hours'], 2.0)  # Cap at 2 seconds for testing
    time.sleep(simulation_time)
    
    end_time = time.time()
    elapsed = end_time - start_time
    
    # Create result dictionary
    result = {
        'package_id': package_id,
        'status': 'completed',
        'parameters': package.get('parameters', {}),
        'execution_time': elapsed,
        'estimated_time': cost['time_hours'] * 3600,  # Convert to seconds
        'timestamp': time.strftime('%Y-%m-%d %H:%M:%S'),
        'results': {
            'convergence': True,
            'final_error': np.random.random() * 1e-6,  # Simulated result
            'iterations': int(package.get('parameters', {}).get('timesteps', 1000))
        }
    }
    
    # Save result
    result_file = output_path / f"results_package_{package_id:04d}.json"
    with open(result_file, 'w') as f:
        json.dump(result, f, indent=2)
    
    print(f"   ✅ Completed in {elapsed:.2f}s")
    print(f"   Results saved to {result_file}")
    
    return result


# ═══════════════════════════════════════════════════════════════
# PACKAGE GENERATION (UTILITY)
# ═══════════════════════════════════════════════════════════════

def create_sample_packages(n_packages: int = 10, 
                          output_dir: str = 'parametric_sweep_packages') -> None:
    """
    Create sample parametric sweep packages for testing.
    
    Args:
        n_packages: Number of packages to create
        output_dir: Output directory
    """
    output_path = Path(output_dir)
    output_path.mkdir(parents=True, exist_ok=True)
    
    # Create diverse parameter combinations
    reynolds_values = [100, 500, 1000, 2000, 5000]
    resolution_values = [32, 64, 128, 256]
    viscosity_values = [1e-3, 5e-4, 1e-4]
    
    packages = []
    for i in range(n_packages):
        package = {
            'package_id': i,
            'parameters': {
                'reynolds': int(np.random.choice(reynolds_values)),
                'resolution': int(np.random.choice(resolution_values)),
                'viscosity': float(np.random.choice(viscosity_values)),
                'timesteps': int(np.random.choice([500, 1000, 2000])),
                'domain_size': 1.0,
                'initial_condition': 'taylor_green'
            },
            'metadata': {
                'created': time.strftime('%Y-%m-%d %H:%M:%S'),
                'description': f'Parameter sweep package {i}'
            }
        }
        
        # Save package
        package_file = output_path / f"package_{i:04d}.json"
        with open(package_file, 'w') as f:
            json.dump(package, f, indent=2)
        
        # Add to list with priority and cost
        priority = assign_priority(package)
        cost = estimate_computational_cost(package)
        
        packages.append({
            'package_id': i,
            'priority': priority,
            'estimated_time_hours': cost['time_hours'],
            'estimated_memory_gb': cost['memory_gb'],
            'estimated_disk_gb': cost['disk_gb']
        })
    
    # Create priority summary
    priority_summary = {
        'HIGH': [p for p in packages if p['priority'] == 'HIGH'],
        'MEDIUM': [p for p in packages if p['priority'] == 'MEDIUM'],
        'LOW': [p for p in packages if p['priority'] == 'LOW']
    }
    
    summary_file = output_path / 'priority_summary.json'
    with open(summary_file, 'w') as f:
        json.dump(priority_summary, f, indent=2)
    
    print(f"✅ Created {n_packages} sample packages in {output_dir}")
    print(f"   HIGH priority: {len(priority_summary['HIGH'])}")
    print(f"   MEDIUM priority: {len(priority_summary['MEDIUM'])}")
    print(f"   LOW priority: {len(priority_summary['LOW'])}")


if __name__ == '__main__':
    # Create sample packages for testing
    create_sample_packages(n_packages=10)
