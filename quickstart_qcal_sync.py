#!/usr/bin/env python3
"""
Quick Start Example for QCAL-SYNC-1/7 Protocol
===============================================

Demonstrates basic usage of the global synchronization protocol.

Author: JMMB Ψ✧∞³
"""

from qcal_sync_protocol import QCALSyncProtocol
import numpy as np


def main():
    """Quick demonstration of QCAL-SYNC-1/7 protocol."""
    
    print("\n" + "="*80)
    print("  Quick Start: QCAL-SYNC-1/7 Global Synchronization Protocol")
    print("="*80 + "\n")
    
    # Initialize protocol
    protocol = QCALSyncProtocol()
    
    print("\n1️⃣  Testing Navier-Stokes Synchronization (Laminar Flow)")
    print("-" * 80)
    
    # Test with laminar flow
    velocity_laminar = np.array([0.5, 0.3, 0.2])
    nu_adjusted, is_laminar = protocol.adjust_viscosity_laminar(velocity_laminar, 0.0)
    print(f"   Velocity field: {velocity_laminar}")
    print(f"   Flow state: {'LAMINAR ✅' if is_laminar else 'TURBULENT ⚠️'}")
    print(f"   Adjusted viscosity: {nu_adjusted:.6f}")
    
    # Test with turbulent flow
    velocity_turbulent = np.array([10.0, 8.0, 6.0])
    nu_adjusted, is_laminar = protocol.adjust_viscosity_laminar(velocity_turbulent, 0.0)
    print(f"\n   Velocity field: {velocity_turbulent}")
    print(f"   Flow state: {'LAMINAR ✅' if is_laminar else 'TURBULENT ⚠️'}")
    print(f"   Adjusted viscosity: {nu_adjusted:.6f} (1/7 factor applied)")
    
    print("\n2️⃣  Testing Economic Coupling (Resonance Detection)")
    print("-" * 80)
    
    # Test resonance at 888.8 Hz
    at_resonance = protocol.check_resonance_peak(888.8)
    print(f"   Frequency: 888.8 Hz")
    print(f"   Resonance detected: {at_resonance} {'✅' if at_resonance else '❌'}")
    print(f"   PSIX pulses sent: {protocol.psix_ledger_pulses}")
    
    # Test non-resonance frequency
    at_resonance = protocol.check_resonance_peak(500.0)
    print(f"\n   Frequency: 500.0 Hz")
    print(f"   Resonance detected: {at_resonance} {'✅' if at_resonance else '❌'}")
    
    print("\n3️⃣  Testing Phase Validation (κ_Π Consistency)")
    print("-" * 80)
    
    # Validate κ_Π across locations
    locations = [
        ("contracts/PSIX", 2.5773),
        ("formal/PsiNSE", 2.5773),
        ("src/oscillators", 2.5773),
        ("invalid/location", 2.58)  # This should fail
    ]
    
    for location, kappa_value in locations:
        is_valid = protocol.validate_kappa_pi_consistency(location, kappa_value)
        status = "✅ VALID" if is_valid else "❌ INVALID"
        print(f"   {location}: κ_Π={kappa_value} → {status}")
    
    print(f"\n   Total validated repositories: {len(protocol.validated_repos)}")
    
    print("\n4️⃣  Testing Coherence Computation")
    print("-" * 80)
    
    # Perfect coherence
    protocol.data_flow_turbulence = 0.0
    psi = protocol.compute_coherence(noise_level=0.0)
    print(f"   No noise, no turbulence → Ψ = {psi:.3f}")
    
    # With noise
    psi = protocol.compute_coherence(noise_level=0.3)
    print(f"   Noise level 0.3 → Ψ = {psi:.3f}")
    
    # With turbulence
    protocol.data_flow_turbulence = 0.5
    psi = protocol.compute_coherence(noise_level=0.0)
    print(f"   Turbulence 0.5 → Ψ = {psi:.3f}")
    
    print("\n5️⃣  Running Synchronization Cycle")
    print("-" * 80)
    
    # Run a short sync cycle
    metrics = protocol.run_synchronization_cycle(duration=0.5, dt=0.01)
    
    print(f"\n   Time points collected: {len(metrics['time'])}")
    print(f"   Final coherence: {metrics['coherence'][-1]:.3f}")
    print(f"   Final turbulence: {metrics['turbulence'][-1]:.4f}")
    
    print("\n6️⃣  Generating Dashboard")
    print("-" * 80)
    dashboard = protocol.generate_dashboard()
    print(dashboard)
    
    print("\n7️⃣  Exporting State")
    print("-" * 80)
    protocol.export_sync_state('/tmp/quickstart_sync_state.json')
    print(f"   State exported to /tmp/quickstart_sync_state.json")
    
    print("\n" + "="*80)
    print("  ✅ Quick Start Complete!")
    print("  For full documentation, see: QCAL_SYNC_PROTOCOL.md")
    print("="*80 + "\n")


if __name__ == "__main__":
    main()
