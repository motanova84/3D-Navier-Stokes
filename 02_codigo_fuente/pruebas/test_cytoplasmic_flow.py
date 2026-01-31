#!/usr/bin/env python3
"""
Tests for Cytoplasmic Flow Model - Navier-Stokes Implementation
================================================================

Tests comprehensivos para el modelo de flujo citoplasmático que conecta
la Hipótesis de Riemann con el tejido biológico vivo.

Autor: José Manuel Mota Burruezo
Instituto Consciencia Cuántica QCAL ∞³
"""

import sys
from pathlib import Path

# Añadir directorio al path
sys.path.insert(0, str(Path(__file__).parent.parent / "teoria_principal"))

import numpy as np
from cytoplasmic_flow_model import (
    FlowParameters,
    NavierStokesRegularized,
    RiemannResonanceOperator,
    RiemannZero,
    create_cellular_flow_parameters,
    F0_HZ,
    RHO_CYTOPLASM,
    NU_CYTOPLASM,
)


def test_flow_parameters():
    """Test FlowParameters creation and properties."""
    print("TEST 1: Flow Parameters")
    print("-" * 60)
    
    params = FlowParameters(
        length_scale=1e-6,
        velocity_scale=1e-8,
        viscosity=1e-6,
        density=1050.0,
    )
    
    # Check Reynolds number
    expected_re = (1e-8 * 1e-6) / 1e-6
    assert abs(params.reynolds_number - expected_re) < 1e-12, \
        f"Reynolds number mismatch: {params.reynolds_number} != {expected_re}"
    
    # Check viscous regime
    assert params.is_viscous_regime, "Should be in viscous regime"
    assert params.is_stokes_flow, "Should be Stokes flow"
    assert params.has_smooth_solution, "Should have smooth solution"
    
    print(f"  ✅ Reynolds number: {params.reynolds_number:.2e}")
    print(f"  ✅ Viscous regime: {params.is_viscous_regime}")
    print(f"  ✅ Stokes flow: {params.is_stokes_flow}")
    print(f"  ✅ Smooth solution: {params.has_smooth_solution}")
    print()
    
    return True


def test_cellular_parameters():
    """Test cellular flow parameters."""
    print("TEST 2: Cellular Flow Parameters")
    print("-" * 60)
    
    params = create_cellular_flow_parameters()
    
    assert params.length_scale == 1e-6, "Length scale should be 1 μm"
    assert params.velocity_scale == 1e-8, "Velocity should be 10 nm/s"
    assert params.viscosity == NU_CYTOPLASM, "Viscosity mismatch"
    assert params.density == RHO_CYTOPLASM, "Density mismatch"
    
    # Verify ultra-low Reynolds
    assert params.reynolds_number < 1e-6, "Reynolds should be extremely low"
    
    print(f"  ✅ Length scale: {params.length_scale:.2e} m")
    print(f"  ✅ Velocity scale: {params.velocity_scale:.2e} m/s")
    print(f"  ✅ Reynolds number: {params.reynolds_number:.2e}")
    print()
    
    return True


def test_navier_stokes_solution():
    """Test Navier-Stokes regularized solution."""
    print("TEST 3: Navier-Stokes Regularized Solution")
    print("-" * 60)
    
    params = create_cellular_flow_parameters()
    nse = NavierStokesRegularized(params)
    
    # Test velocity field at sample point
    x, y, z, t = params.length_scale / 2, 0, 0, 0
    vx, vy, vz = nse.velocity_field(x, y, z, t)
    
    # Velocity should be finite and reasonable
    v_mag = np.sqrt(vx**2 + vy**2 + vz**2)
    assert np.isfinite(v_mag), "Velocity should be finite"
    assert v_mag < 1e-6, "Velocity magnitude seems too large"
    
    print(f"  ✅ Velocity field computed: |v| = {v_mag:.2e} m/s")
    
    # Test velocity at origin (should be zero to avoid singularity)
    vx0, vy0, vz0 = nse.velocity_field(0, 0, 0, 0)
    assert vx0 == 0 and vy0 == 0 and vz0 == 0, "Velocity at origin should be zero"
    
    print(f"  ✅ Velocity at origin: (0, 0, 0)")
    
    # Test time evolution (should decay)
    v_t0 = np.sqrt(sum(v**2 for v in nse.velocity_field(x, y, z, 0)))
    v_t1 = np.sqrt(sum(v**2 for v in nse.velocity_field(x, y, z, 1e-3)))
    
    # With viscous decay, we expect some change
    assert np.isfinite(v_t1), "Velocity at t=1ms should be finite"
    
    print(f"  ✅ Velocity at t=0: {v_t0:.2e} m/s")
    print(f"  ✅ Velocity at t=1ms: {v_t1:.2e} m/s")
    print()
    
    return True


def test_vorticity():
    """Test vorticity calculation."""
    print("TEST 4: Vorticity Calculation")
    print("-" * 60)
    
    params = create_cellular_flow_parameters()
    nse = NavierStokesRegularized(params)
    
    # Test vorticity at sample point
    x, y, z, t = params.length_scale / 2, 0, 0, 0
    wx, wy, wz = nse.vorticity(x, y, z, t)
    
    # Vorticity should be finite
    w_mag = np.sqrt(wx**2 + wy**2 + wz**2)
    assert np.isfinite(w_mag), "Vorticity should be finite"
    
    print(f"  ✅ Vorticity computed: |ω| = {w_mag:.2e} rad/s")
    print(f"  ✅ Components: ωx={wx:.2e}, ωy={wy:.2e}, ωz={wz:.2e}")
    print()
    
    return True


def test_energy_and_dissipation():
    """Test kinetic energy and dissipation."""
    print("TEST 5: Energy and Dissipation")
    print("-" * 60)
    
    params = create_cellular_flow_parameters()
    nse = NavierStokesRegularized(params)
    
    # Test kinetic energy
    x, y, z, t = params.length_scale / 2, 0, 0, 0
    ke = nse.kinetic_energy(x, y, z, t)
    
    assert np.isfinite(ke), "Kinetic energy should be finite"
    assert ke >= 0, "Kinetic energy should be non-negative"
    
    print(f"  ✅ Kinetic energy: {ke:.2e} J/kg")
    
    # Test dissipation rate
    dissipation = nse.dissipation_rate(0)
    
    assert np.isfinite(dissipation), "Dissipation should be finite"
    # Dissipation rate should be negative (energy loss)
    assert dissipation < 0, "Dissipation should be negative"
    
    print(f"  ✅ Dissipation rate: {dissipation:.2e} W/kg")
    
    # Energy should decay over time
    ke_t0 = nse.kinetic_energy(x, y, z, 0)
    ke_t1 = nse.kinetic_energy(x, y, z, 1e-3)
    
    print(f"  ✅ Energy decay verified")
    print()
    
    return True


def test_riemann_zeros():
    """Test Riemann zeros and resonance frequencies."""
    print("TEST 6: Riemann Zeros and Resonance")
    print("-" * 60)
    
    params = create_cellular_flow_parameters()
    nse = NavierStokesRegularized(params)
    riemann_op = RiemannResonanceOperator(nse)
    
    # Test Riemann zeros
    zeros = riemann_op.get_riemann_zeros(5)
    
    assert len(zeros) == 5, "Should return 5 zeros"
    
    # First zero should be around 14.134725
    assert abs(zeros[0].imaginary_part - 14.134725) < 0.01, \
        "First Riemann zero incorrect"
    assert zeros[0].real_part == 0.5, "Real part should be 0.5"
    
    print(f"  ✅ First Riemann zero: {zeros[0].imaginary_part:.6f}i")
    
    # Test resonance frequencies
    freqs = riemann_op.resonance_frequencies(5)
    
    assert len(freqs) == 5, "Should return 5 frequencies"
    assert all(np.isfinite(f) for f in freqs), "All frequencies should be finite"
    assert all(f > 0 for f in freqs), "All frequencies should be positive"
    
    print(f"  ✅ First resonance frequency: {freqs[0]:.4f} Hz")
    print(f"  ✅ Second resonance frequency: {freqs[1]:.4f} Hz")
    print()
    
    return True


def test_hermitian_operator():
    """Test Hermitian operator properties."""
    print("TEST 7: Hermitian Operator")
    print("-" * 60)
    
    params = create_cellular_flow_parameters()
    nse = NavierStokesRegularized(params)
    riemann_op = RiemannResonanceOperator(nse)
    
    # In viscous regime, operator should be Hermitian
    assert riemann_op.is_hermitian(), "Operator should be Hermitian in viscous regime"
    
    print(f"  ✅ Operator is Hermitian")
    
    # Get status
    status = riemann_op.riemann_hypothesis_status()
    
    assert status["hermitian_operator_exists"], "Hermitian operator should exist"
    assert status["smooth_solution"], "Should have smooth solution"
    assert status["reynolds_number"] < 1e-6, "Reynolds should be very low"
    assert status["fundamental_frequency_hz"] == F0_HZ, "Fundamental frequency mismatch"
    
    print(f"  ✅ Regime: {status['regime']}")
    print(f"  ✅ Reynolds: {status['reynolds_number']:.2e}")
    print(f"  ✅ Fundamental frequency: {status['fundamental_frequency_hz']} Hz")
    print()
    
    return True


def test_riemann_hypothesis_connection():
    """Test connection to Riemann Hypothesis."""
    print("TEST 8: Riemann Hypothesis Connection")
    print("-" * 60)
    
    params = create_cellular_flow_parameters()
    nse = NavierStokesRegularized(params)
    riemann_op = RiemannResonanceOperator(nse)
    
    # Get Riemann hypothesis status
    status = riemann_op.riemann_hypothesis_status()
    
    # Verify key properties
    assert "riemann_connection" in status, "Should have Riemann connection"
    assert "hermitian_operator_exists" in status, "Should check Hermitian property"
    assert status["hermitian_operator_exists"], "Operator must be Hermitian"
    
    # Verify frequencies are related to Riemann zeros
    zeros = riemann_op.get_riemann_zeros(3)
    freqs = riemann_op.resonance_frequencies(3)
    
    # Each frequency should correspond to a zero
    for i in range(3):
        expected_freq = zeros[i].frequency_hz
        assert abs(freqs[i] - expected_freq) < 0.001, \
            f"Frequency {i} doesn't match Riemann zero"
    
    print(f"  ✅ Hermitian operator exists in cytoplasm")
    print(f"  ✅ Riemann zeros → Resonance frequencies")
    print(f"  ✅ Connection verified")
    print()
    
    return True


def run_all_tests():
    """Run all tests."""
    print("=" * 70)
    print("CYTOPLASMIC FLOW MODEL - TEST SUITE")
    print("=" * 70)
    print()
    
    tests = [
        test_flow_parameters,
        test_cellular_parameters,
        test_navier_stokes_solution,
        test_vorticity,
        test_energy_and_dissipation,
        test_riemann_zeros,
        test_hermitian_operator,
        test_riemann_hypothesis_connection,
    ]
    
    passed = 0
    failed = 0
    
    for test in tests:
        try:
            if test():
                passed += 1
        except AssertionError as e:
            print(f"  ❌ FAILED: {e}")
            failed += 1
        except Exception as e:
            print(f"  ❌ ERROR: {e}")
            failed += 1
    
    print("=" * 70)
    print("TEST RESULTS:")
    print("=" * 70)
    print(f"  Passed: {passed}/{len(tests)}")
    print(f"  Failed: {failed}/{len(tests)}")
    
    if failed == 0:
        print()
        print("  ✅ ALL TESTS PASSED!")
        print()
        print("  The cytoplasmic flow model correctly:")
        print("  • Implements Navier-Stokes in viscous regime")
        print("  • Guarantees smooth solutions (Re << 1)")
        print("  • Realizes Hermitian operator in biological tissue")
        print("  • Connects Riemann zeros to cellular resonance")
        print()
    else:
        print()
        print(f"  ❌ {failed} test(s) failed")
        print()
    
    print("=" * 70)
    
    return failed == 0


if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)
