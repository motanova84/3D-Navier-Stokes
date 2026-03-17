"""
Test suite for ∞³ Complete Validation Framework

Tests all components of the proof for 3D Navier-Stokes global regularity:
- Misalignment defect δ*
- Damping coefficient γ  
- Triple convergent verification
- Ψ-NSE vs Classical NSE comparison
- QFT derivation
- Frequency emergence
"""

import pytest
import numpy as np
from infinity_cubed_complete_validation import (
    InfinityCubedConstants,
    InfinityCubedFramework,
    misalignment_defect,
    damping_coefficient,
    positive_damping_threshold,
    dyadic_riccati_coefficient,
    riccati_convergence_verification,
    volterra_convergence_verification,
    bootstrap_convergence_verification,
    triple_convergence_verification,
    simulate_classical_nse,
    simulate_psi_nse,
    psi_nse_vs_classical_comparison,
    compute_phi_tensor,
)


class TestFundamentalConstants:
    """Test fundamental constants."""
    
    def test_f0_value(self):
        """Test critical frequency f₀ = 141.7001 Hz."""
        assert InfinityCubedConstants.f0_hz == 141.7001
    
    def test_f0_range(self):
        """Test f₀ is in valid range (100, 200) Hz."""
        f0 = InfinityCubedConstants.f0_hz
        assert 100 < f0 < 200
    
    def test_omega0_positive(self):
        """Test ω₀ > 0."""
        assert InfinityCubedConstants.omega0_rad_s > 0
    
    def test_f_infinity_value(self):
        """Test f∞ = 888.0 Hz."""
        assert InfinityCubedConstants.f_infinity_hz == 888.0
    
    def test_seeley_dewitt_coefficients(self):
        """Test Seeley-DeWitt coefficients are defined."""
        assert InfinityCubedConstants.a1_gradient > 0
        assert InfinityCubedConstants.a2_ricci != 0
        assert InfinityCubedConstants.a3_trace != 0
    
    def test_doi_reference(self):
        """Test DOI reference."""
        assert InfinityCubedConstants.DOI == "10.5281/zenodo.17488796"


class TestMisalignmentDefect:
    """Test misalignment defect δ* calculations."""
    
    def test_positive_amplitude_gives_positive_delta(self):
        """Test δ* > 0 for positive amplitude."""
        delta = misalignment_defect(amplitude=7.0)
        assert delta > 0
    
    def test_large_amplitude_gives_large_delta(self):
        """Test δ* >> 1 for large amplitude (a=200)."""
        delta = misalignment_defect(amplitude=200.0)
        assert delta > 1000  # Should be ~1012.9
    
    def test_formula_correct(self):
        """Test δ* = a²c₀²/(4π²)."""
        a = 10.0
        c0 = 2.0
        expected = (a**2 * c0**2) / (4 * np.pi**2)
        actual = misalignment_defect(a, c0)
        assert np.isclose(actual, expected)
    
    def test_specific_value(self):
        """Test specific δ* value for a=200, c₀=1."""
        delta = misalignment_defect(200.0, 1.0)
        expected = 40000 / (4 * np.pi**2)
        assert np.isclose(delta, expected, rtol=1e-6)


class TestDampingCoefficient:
    """Test damping coefficient γ calculations."""
    
    def test_positive_for_large_amplitude(self):
        """Test γ > 0 for large amplitude."""
        gamma = damping_coefficient(nu=1e-3, amplitude=200.0)
        assert gamma > 0
    
    def test_increases_with_amplitude(self):
        """Test γ increases with amplitude."""
        gamma1 = damping_coefficient(nu=1e-3, amplitude=100.0)
        gamma2 = damping_coefficient(nu=1e-3, amplitude=200.0)
        assert gamma2 > gamma1
    
    def test_threshold_condition(self):
        """Test threshold condition δ* > 1 - ν/512."""
        nu = 1e-3
        threshold = positive_damping_threshold(nu)
        delta = misalignment_defect(200.0)
        gamma = damping_coefficient(nu, 200.0)
        
        # If δ* > threshold, then γ > 0
        assert delta > threshold
        assert gamma > 0


class TestTripleConvergence:
    """Test triple convergent verification."""
    
    def test_riccati_convergence(self):
        """Test Riccati method converges."""
        result = riccati_convergence_verification(nu=1e-3, delta_star=1012.9)
        assert result['converges']
        assert result['j_dissipative'] is not None
    
    def test_volterra_convergence(self):
        """Test Volterra method converges."""
        result = volterra_convergence_verification(nu=1e-3, delta_star=1012.9)
        assert result['converges']
        assert result['resolvent_bounded']
    
    def test_bootstrap_convergence(self):
        """Test Bootstrap method converges."""
        result = bootstrap_convergence_verification()
        assert result['converges']
        assert result['final_regularity'] > result['initial_regularity']
    
    def test_triple_convergence_all_methods(self):
        """Test all three methods converge."""
        result = triple_convergence_verification(nu=1e-3, delta_star=1012.9)
        assert result['triple_convergence']
        assert result['riccati']['converges']
        assert result['volterra']['converges']
        assert result['bootstrap']['converges']


class TestPsiNSEComparison:
    """Test Ψ-NSE vs Classical NSE comparison."""
    
    def test_classical_growth(self):
        """Test classical NSE shows vorticity growth."""
        result = simulate_classical_nse(initial_vorticity=10.0, T=2.0)
        assert result['final_vorticity'] > 10.0 or result['blow_up']
    
    def test_psi_nse_regularity(self):
        """Test Ψ-NSE maintains regularity."""
        result = simulate_psi_nse(initial_vorticity=10.0, T=5.0)
        assert result['regularity']
        assert not result['blow_up']
    
    def test_psi_nse_better_than_classical(self):
        """Test Ψ-NSE performs better than classical NSE."""
        comparison = psi_nse_vs_classical_comparison()
        # Ψ-NSE should either have lower vorticity or classical should blow up
        assert (comparison['improvement_factor'] > 1 or 
                comparison['classical_blow_up'])
    
    def test_quantum_coherence_prevents_blowup(self):
        """Test quantum coherence prevents blow-up."""
        comparison = psi_nse_vs_classical_comparison()
        assert comparison['psi_nse_regular']


class TestQFTDerivation:
    """Test QFT + Seeley-DeWitt derivation."""
    
    def test_phi_tensor_computed(self):
        """Test Φ tensor is computed."""
        phi = compute_phi_tensor()
        assert 'alpha_gradient' in phi
        assert 'beta_ricci' in phi
        assert 'gamma_trace' in phi
    
    def test_phi_tensor_provides_regularization(self):
        """Test Φ tensor provides regularization."""
        phi = compute_phi_tensor()
        assert phi['provides_regularization']
        assert phi['alpha_gradient'] > 0
    
    def test_qft_derived(self):
        """Test tensor is marked as QFT-derived."""
        phi = compute_phi_tensor()
        assert phi['qft_derived']


class TestInfinityCubedFramework:
    """Test complete ∞³ framework."""
    
    def test_framework_initialization(self):
        """Test framework initializes correctly."""
        framework = InfinityCubedFramework()
        assert framework.nu == 1e-3
        assert framework.delta_star > 0
    
    def test_positive_damping_verification(self):
        """Test positive damping verification."""
        framework = InfinityCubedFramework()
        result = framework.verify_positive_damping()
        assert result['is_positive']
        assert result['global_regularity_guaranteed']
    
    def test_triple_convergence_verification(self):
        """Test triple convergence verification."""
        framework = InfinityCubedFramework()
        result = framework.verify_triple_convergence()
        assert result['triple_convergence']
    
    def test_computational_comparison(self):
        """Test computational comparison."""
        framework = InfinityCubedFramework()
        result = framework.verify_computational_comparison()
        assert result['quantum_coherence_prevents_blowup']
    
    def test_qft_derivation_verification(self):
        """Test QFT derivation verification."""
        framework = InfinityCubedFramework()
        result = framework.verify_qft_derivation()
        assert result['provides_regularization']
    
    def test_frequency_emergence_verification(self):
        """Test frequency emergence verification."""
        framework = InfinityCubedFramework()
        result = framework.verify_frequency_emergence()
        assert result['frequency_valid']
        assert result['f0_hz'] == 141.7001
    
    def test_complete_verification(self):
        """Test complete verification passes all checks."""
        framework = InfinityCubedFramework()
        result = framework.execute_complete_verification()
        assert result['all_verified']
    
    def test_report_generation(self):
        """Test report generation."""
        framework = InfinityCubedFramework()
        report = framework.generate_report()
        assert "∞³" in report
        assert "141.7001" in report
        assert "VERIFIED" in report or "PASSED" in report


class TestScientificConclusion:
    """Test scientific conclusion validity."""
    
    def test_conclusion_in_results(self):
        """Test scientific conclusion is in results."""
        framework = InfinityCubedFramework()
        result = framework.execute_complete_verification()
        assert 'scientific_conclusion' in result
        assert 'coherencia cuántica' in result['scientific_conclusion']
    
    def test_doi_in_results(self):
        """Test DOI is in results."""
        framework = InfinityCubedFramework()
        result = framework.execute_complete_verification()
        assert result['doi'] == "10.5281/zenodo.17488796"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
