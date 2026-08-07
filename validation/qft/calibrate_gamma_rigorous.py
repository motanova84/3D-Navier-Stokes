#!/usr/bin/env python3
"""
Calibrate gamma parameter rigorously for QFT framework.
"""
import json
import os
from datetime import datetime, timezone
from pathlib import Path


def calibrate_gamma():
    """Perform rigorous gamma calibration."""
    
    print("🔬 Performing rigorous gamma calibration...")
    
    # QCAL parameters from theoretical framework
    c_star = 1/16  # Parabolic coercivity coefficient
    C_str = 32      # Vorticity stretching constant
    C_BKM = 2       # Calderón-Zygmund/Besov constant
    
    # Misalignment defect candidates
    delta_candidates = [0.998, 0.95, 0.9, 0.5, 0.0253]
    
    results = []
    
    for delta_star in delta_candidates:
        # Calculate gamma = ν·c⋆ - (1-δ*/2)·C_str
        # Assuming ν = 1 for normalization
        nu = 1.0
        gamma = nu * c_star - (1 - delta_star/2) * C_str
        
        result = {
            'delta_star': delta_star,
            'gamma': gamma,
            'stable': gamma > 0,
            'c_star': c_star,
            'C_str': C_str
        }
        results.append(result)
        
        status = "✅ STABLE" if gamma > 0 else "❌ UNSTABLE"
        print(f"   δ* = {delta_star:.4f} → γ = {gamma:.6f} [{status}]")
    
    # Create calibration report
    calibration = {
        'metadata': {
            'generated_at': datetime.now(timezone.utc).isoformat().replace('+00:00', 'Z'),
            'framework': 'QCAL',
            'parameter': 'gamma'
        },
        'parameters': {
            'c_star': c_star,
            'C_str': C_str,
            'C_BKM': C_BKM,
            'nu': 1.0
        },
        'results': results,
        'recommendation': {
            'optimal_delta_star': 0.998,
            'notes': 'Higher δ* provides better misalignment control but may lead to negative γ. Balance required.'
        }
    }
    
    # Save to file
    output_dir = Path('validation/qft')
    output_dir.mkdir(parents=True, exist_ok=True)
    output_file = output_dir / 'gamma_calibration.json'
    
    with open(output_file, 'w') as f:
        json.dump(calibration, f, indent=2)
    
    print(f"✅ Calibration complete: {output_file}")
    
    return calibration


def main():
    calibrate_gamma()


if __name__ == '__main__':
    main()
