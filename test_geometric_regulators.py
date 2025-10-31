#!/usr/bin/env python3
"""
Test suite for geometric regulators scripts.

Validates that all scripts can be imported and basic functionality works.
"""

import sys
import os
import numpy as np

# Add scripts directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'scripts', 'geometrías_reguladoras'))

def test_calabi_yau_visualizer():
    """Test Calabi-Yau visualizer."""
    from visualizador_calabi_yau_3d import CalabiYauVisualizer
    
    visualizer = CalabiYauVisualizer(resolution=10, f0=141.7001)
    
    # Test geometry generation
    u = np.linspace(0, 2*np.pi, 10)
    v = np.linspace(0, np.pi, 10)
    U, V = np.meshgrid(u, v)
    x, y, z = visualizer.calabi_yau_quintic(U, V)
    
    assert x.shape == (10, 10), "Incorrect geometry shape"
    assert not np.any(np.isnan(x)), "NaN values in geometry"
    
    # Test field calculations
    energy = visualizer.spectral_energy_field(x, y, z, t=0)
    psi = visualizer.noetic_field_psi(x, y, z, t=0, coherence=0.88)
    
    assert energy.shape == x.shape, "Energy field shape mismatch"
    assert psi.shape == x.shape, "Psi field shape mismatch"
    
    print("✅ test_calabi_yau_visualizer passed")


def test_topological_spirals():
    """Test topological spiral simulator."""
    from espirales_topológicas_NS import TopologicalSpiralSimulator
    
    simulator = TopologicalSpiralSimulator(f0=141.7001)
    
    t = np.linspace(0, 2*np.pi, 50)
    
    # Test Hopf fibration
    x, y, z = simulator.hopf_fibration(t, phase=0)
    assert len(x) == 50, "Hopf fibration length mismatch"
    
    # Test trefoil knot
    x, y, z = simulator.trefoil_knot(t, scale=1.0, phase=0)
    assert len(x) == 50, "Trefoil knot length mismatch"
    
    # Test vorticity and coherence
    vorticity = simulator.compute_vorticity(x, y, z, t=0)
    coherence = simulator.compute_coherence(vorticity)
    assert 0 <= coherence <= 1, "Coherence out of range"
    
    print("✅ test_topological_spirals passed")


def test_portal_generator():
    """Test Gemina portal generator."""
    from portal_simbiótico_gemina import GeminaPortalGenerator
    
    portal = GeminaPortalGenerator(f0=141.7001)
    
    # Test sequence detection
    sequences = ['atgccccaccggggaaa', 'random']
    detected = portal.detect_gemina_sequence(sequences)
    assert detected == True, "Failed to detect Gemina sequence"
    
    # Test entity verification
    result = portal.verify_symbiotic_entity('gemina_141_coherence_portal_∞')
    assert 'gemina_score' in result, "Missing gemina_score in result"
    assert 0 <= result['gemina_score'] <= 1, "Score out of range"
    
    # Test double vortex generation
    x, y, z = portal.double_vortex_structure(t=0, n_points=100)
    assert len(x) == 200, "Double vortex should have 2*n_points"
    
    print("✅ test_portal_generator passed")


def test_coherent_field_simulator():
    """Test coherent field simulator."""
    from campo_coherente_global import CoherentFieldSimulator
    
    simulator = CoherentFieldSimulator(N=8, L=2*np.pi, f0=141.7001)
    
    # Test velocity field
    u, v, w = simulator.initialize_velocity_field(mode='taylor_green')
    assert u.shape == (8, 8, 8), "Velocity field shape mismatch"
    
    # Test vorticity
    vorticity = simulator.compute_vorticity(u, v, w)
    assert vorticity.shape == u.shape, "Vorticity shape mismatch"
    assert vorticity.max() > 0, "Vorticity should be positive somewhere"
    
    # Test Psi field
    psi = simulator.compute_psi_field(t=0, coherence=0.88)
    assert psi.shape == u.shape, "Psi field shape mismatch"
    
    # Test local coherence
    coherence_field = simulator.compute_local_coherence(vorticity, psi)
    assert coherence_field.shape == u.shape, "Coherence field shape mismatch"
    assert np.all((coherence_field >= 0) & (coherence_field <= 1)), "Coherence out of range"
    
    print("✅ test_coherent_field_simulator passed")


def test_riemann_zeta_visualizer():
    """Test Riemann zeta visualizer."""
    from módulo_ζ12_visual import RiemannZetaVisualizer
    
    visualizer = RiemannZetaVisualizer(n_modes=10, f0=141.7001)
    
    # Test dyadic modes
    k = visualizer.dyadic_modes()
    assert len(k) == 10, "Incorrect number of dyadic modes"
    assert np.all(k == 2.0 ** np.arange(1, 11)), "Incorrect dyadic mode values"
    
    # Test energy spectra
    E_baseline = visualizer.energy_spectrum_baseline(k)
    E_zeta = visualizer.energy_spectrum_with_zeta(k)
    E_zeta_f0 = visualizer.energy_spectrum_with_zeta_and_f0(k, t=0)
    
    assert len(E_baseline) == 10, "Energy spectrum length mismatch"
    assert np.all(E_baseline > 0), "Energy should be positive"
    
    # Verify zeta modulation changes energy
    assert not np.allclose(E_baseline, E_zeta), "Zeta modulation should change energy"
    
    print("✅ test_riemann_zeta_visualizer passed")


def test_gemina_live_monitor():
    """Test Gemina live monitor."""
    from run_gemina_live import GeminaLiveMonitor
    
    monitor = GeminaLiveMonitor(f0=141.7001)
    
    # Test coherence measurement
    coherence = monitor.simulate_coherence_measurement()
    assert 0 <= coherence <= 1, "Coherence out of range"
    
    # Test portal activation
    should_activate = monitor.check_portal_activation(0.90)
    assert isinstance(should_activate, bool), "Portal activation should return bool"
    
    # Test external resonance
    is_resonant = monitor.check_external_resonance(0.95)
    assert isinstance(is_resonant, bool), "External resonance should return bool"
    
    print("✅ test_gemina_live_monitor passed")


def run_all_tests():
    """Run all tests."""
    print("="*70)
    print("🧪 TESTING GEOMETRIC REGULATORS SCRIPTS")
    print("="*70)
    print()
    
    tests = [
        test_calabi_yau_visualizer,
        test_topological_spirals,
        test_portal_generator,
        test_coherent_field_simulator,
        test_riemann_zeta_visualizer,
        test_gemina_live_monitor,
    ]
    
    passed = 0
    failed = 0
    
    for test in tests:
        try:
            test()
            passed += 1
        except Exception as e:
            print(f"❌ {test.__name__} failed: {e}")
            failed += 1
    
    print()
    print("="*70)
    print(f"📊 RESULTS: {passed} passed, {failed} failed")
    print("="*70)
    
    if failed == 0:
        print("🟢 All tests passed!")
        return 0
    else:
        print(f"🔴 {failed} test(s) failed")
        return 1


if __name__ == "__main__":
    # Set matplotlib backend to non-interactive
    import matplotlib
    matplotlib.use('Agg')
    
    exit_code = run_all_tests()
    sys.exit(exit_code)
