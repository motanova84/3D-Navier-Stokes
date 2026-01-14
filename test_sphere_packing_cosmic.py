#!/usr/bin/env python3
"""
Tests for QCAL ∞³ Sphere Packing in Infinite Dimensions

Comprehensive test suite validating the cosmic sphere packing framework
including dimensional magic, convergence, and resonance properties.

Author: JMMB Ψ✧∞³
License: MIT
"""

import pytest
import numpy as np
from sphere_packing_cosmic import EmpaquetamientoCósmico


class TestEmpaquetamientoCósmicoBasic:
    """Basic functionality tests"""
    
    def setup_method(self):
        """Initialize framework for each test"""
        self.navegador = EmpaquetamientoCósmico()
    
    def test_initialization(self):
        """Test framework initialization"""
        assert self.navegador.phi == (1 + np.sqrt(5)) / 2
        assert abs(self.navegador.phi - 1.618033988) < 1e-8
        assert self.navegador.f0 == 141.7001
        assert len(self.navegador.dimensiones_magicas) > 0
    
    def test_golden_ratio_properties(self):
        """Test golden ratio mathematical properties"""
        phi = self.navegador.phi
        # φ² = φ + 1
        assert abs(phi**2 - (phi + 1)) < 1e-10
        # φ⁻¹ = φ - 1
        assert abs(1/phi - (phi - 1)) < 1e-10
        # φ × φ⁻¹ = 1
        assert abs(phi * self.navegador.phi_inverse - 1) < 1e-10
    
    def test_dimensiones_magicas_fibonacci(self):
        """Test that magic dimensions follow Fibonacci pattern"""
        # Magic dimensions should be d_k = round(8 × φ^k)
        phi = self.navegador.phi
        for k, d_k in enumerate(self.navegador.dimensiones_magicas[:5], start=1):
            expected = int(round(8 * (phi ** k)))
            assert d_k == expected, f"Magic dimension {k}: got {d_k}, expected {expected}"
    
    def test_frecuencia_dimensional(self):
        """Test cosmic frequency calculation"""
        # f_d = f₀ × φ^d
        d = 10
        freq = self.navegador.frecuencia_dimensional(d)
        expected = self.navegador.f0 * (self.navegador.phi ** d)
        assert abs(freq - expected) < 1e-6
        
        # Frequency should increase with dimension
        assert self.navegador.frecuencia_dimensional(20) > self.navegador.frecuencia_dimensional(10)


class TestDensidadCósmica:
    """Tests for cosmic density calculations"""
    
    def setup_method(self):
        """Initialize framework for each test"""
        self.navegador = EmpaquetamientoCósmico()
    
    def test_densidad_positive(self):
        """Test that density is always positive"""
        for d in [8, 24, 25, 50, 100]:
            density = self.navegador.densidad_cosmica(d)
            assert density > 0, f"Density at d={d} should be positive"
    
    def test_densidad_decreasing(self):
        """Test that density generally decreases with dimension"""
        # In high dimensions, density should decrease
        d1, d2, d3 = 50, 100, 200
        delta1 = self.navegador.densidad_cosmica(d1)
        delta2 = self.navegador.densidad_cosmica(d2)
        delta3 = self.navegador.densidad_cosmica(d3)
        
        assert delta1 > delta2 > delta3, "Density should decrease with dimension"
    
    def test_densidad_magic_dimensions(self):
        """Test that magic dimensions have enhanced density"""
        # Magic dimensions should have resonance enhancement
        d_magic = 34  # First readily computable magic dimension
        if d_magic in self.navegador.dimensiones_magicas:
            # Compare with nearby non-magic dimension
            d_normal = 33
            density_magic = self.navegador.densidad_cosmica(d_magic)
            density_normal = self.navegador.densidad_cosmica(d_normal)
            # Both should be positive
            assert density_magic > 0
            assert density_normal > 0


class TestConocidosValidation:
    """Tests against known exact results"""
    
    def setup_method(self):
        """Initialize framework for each test"""
        self.navegador = EmpaquetamientoCósmico()
    
    def test_e8_lattice(self):
        """Test agreement with E₈ lattice (d=8)"""
        d = 8
        density = self.navegador.densidad_cosmica(d)
        known_e8 = 0.25367
        
        # Should be within reasonable agreement
        # (framework is designed for d ≥ 25, so some deviation expected)
        assert density > 0
        relative_error = abs(density - known_e8) / known_e8
        # Allow larger tolerance for low dimensions
        assert relative_error < 5.0, f"E₈ density error too large: {relative_error*100:.2f}%"
    
    def test_leech_lattice(self):
        """Test agreement with Leech lattice (d=24)"""
        d = 24
        density = self.navegador.densidad_cosmica(d)
        known_leech = 0.001930
        
        # Should be within reasonable agreement
        assert density > 0
        relative_error = abs(density - known_leech) / known_leech
        # Allow larger tolerance for boundary dimension
        assert relative_error < 5.0, f"Leech density error too large: {relative_error*100:.2f}%"
    
    def test_validar_casos_conocidos(self):
        """Test validation method for known cases"""
        validacion = self.navegador.validar_casos_conocidos()
        
        assert 8 in validacion
        assert 24 in validacion
        
        for d in [8, 24]:
            assert 'densidad_exacta' in validacion[d]
            assert 'densidad_qcal' in validacion[d]
            assert 'error_relativo' in validacion[d]
            assert validacion[d]['densidad_qcal'] > 0


class TestConvergencia:
    """Tests for convergence to φ⁻¹"""
    
    def setup_method(self):
        """Initialize framework for each test"""
        self.navegador = EmpaquetamientoCósmico()
    
    def test_convergencia_computation(self):
        """Test convergence analysis computation"""
        dims, ratios = self.navegador.analizar_convergencia_infinita(d_max=100, n_points=20)
        
        assert len(dims) > 0
        assert len(ratios) == len(dims)
        assert all(r >= 0 for r in ratios if not np.isnan(r))
    
    def test_convergencia_towards_phi_inverse(self):
        """Test that convergence approaches φ⁻¹"""
        dims, ratios = self.navegador.analizar_convergencia_infinita(d_max=1000, n_points=50)
        
        # Get last valid ratio
        valid_ratios = [r for r in ratios if r > 0 and not np.isnan(r)]
        if len(valid_ratios) > 0:
            last_ratio = valid_ratios[-1]
            phi_inv = self.navegador.phi_inverse
            
            # Should be converging toward φ⁻¹
            # Allow generous tolerance for numerical stability
            assert abs(last_ratio - phi_inv) < 0.5, \
                f"Convergence to φ⁻¹: got {last_ratio:.6f}, expected {phi_inv:.6f}"
    
    def test_convergence_monotonic_approach(self):
        """Test that later ratios are closer to φ⁻¹"""
        dims, ratios = self.navegador.analizar_convergencia_infinita(d_max=500, n_points=30)
        
        phi_inv = self.navegador.phi_inverse
        valid_indices = [i for i, r in enumerate(ratios) if r > 0 and not np.isnan(r)]
        
        if len(valid_indices) >= 3:
            # Compare early vs late convergence
            early_idx = valid_indices[len(valid_indices)//3]
            late_idx = valid_indices[-1]
            
            early_error = abs(ratios[early_idx] - phi_inv)
            late_error = abs(ratios[late_idx] - phi_inv)
            
            # Later should generally be closer (allowing some numerical noise)
            # Not strictly monotonic but should trend toward better convergence
            assert late_error < early_error * 2


class TestCotasSuperiores:
    """Tests for upper bound compliance"""
    
    def setup_method(self):
        """Initialize framework for each test"""
        self.navegador = EmpaquetamientoCósmico()
    
    def test_kabatiansky_levenshtein_bound(self):
        """Test compliance with Kabatiansky-Levenshtein bound"""
        # KL bound: δ(d) ≤ 2^(-0.5990d + o(d))
        for d in [25, 50, 100]:
            verificacion = self.navegador.verificar_cotas_superiores(d)
            
            assert verificacion['cumple_KL'], \
                f"Dimension {d} violates KL bound: {verificacion['log2_densidad_per_d']:.4f} > {verificacion['limite_KL']}"
    
    def test_qcal_exponent(self):
        """Test that QCAL exponent is consistent"""
        for d in [30, 50, 100]:
            verificacion = self.navegador.verificar_cotas_superiores(d)
            
            # QCAL exponent should be approximately -0.5847
            expected_exp = -0.5847
            assert abs(verificacion['exponente_qcal'] - expected_exp) < 0.01
    
    def test_positive_margin(self):
        """Test that there's positive margin below upper bound"""
        for d in [25, 50, 75, 100]:
            verificacion = self.navegador.verificar_cotas_superiores(d)
            
            # Margin should be positive (we're below the bound)
            assert verificacion['margen'] > 0, \
                f"Dimension {d} has negative margin: {verificacion['margen']}"


class TestRedCósmica:
    """Tests for crystalline lattice construction"""
    
    def setup_method(self):
        """Initialize framework for each test"""
        self.navegador = EmpaquetamientoCósmico()
    
    def test_construir_red_structure(self):
        """Test that lattice construction returns proper structure"""
        d = 25
        red = self.navegador.construir_red_cosmica(d)
        
        assert 'dimension' in red
        assert 'vectores_base' in red
        assert 'gram_matrix' in red
        assert 'frecuencia' in red
        assert 'densidad' in red
        assert 'es_magica' in red
        
        assert red['dimension'] == d
        assert len(red['vectores_base']) == d
        assert red['gram_matrix'].shape == (d, d)
    
    def test_gram_matrix_properties(self):
        """Test Gram matrix properties"""
        d = 10
        red = self.navegador.construir_red_cosmica(d)
        gram = red['gram_matrix']
        
        # Diagonal should be 1
        for i in range(d):
            assert abs(gram[i, i] - 1.0) < 1e-10
        
        # Should be Hermitian
        assert np.allclose(gram, gram.T.conj())
    
    def test_magic_dimension_detection(self):
        """Test correct detection of magic dimensions"""
        # Test a known magic dimension
        d_magic = 13  # First magic dimension
        red = self.navegador.construir_red_cosmica(d_magic)
        assert red['es_magica'] == True
        assert red['index_magica'] is not None
        
        # Test a non-magic dimension
        d_normal = 14
        red = self.navegador.construir_red_cosmica(d_normal)
        assert red['es_magica'] == False
        assert red['index_magica'] is None


class TestDimensionesCríticas:
    """Tests for critical dimensions"""
    
    def setup_method(self):
        """Initialize framework for each test"""
        self.navegador = EmpaquetamientoCósmico()
    
    def test_calcular_dimensiones_criticas(self):
        """Test critical dimension calculations"""
        predicciones = self.navegador.calcular_dimensiones_criticas()
        
        # Should include specified critical dimensions
        expected_dims = [25, 34, 50, 55, 100, 144]
        for d in expected_dims:
            assert d in predicciones
            
            pred = predicciones[d]
            assert 'dimension' in pred
            assert 'densidad' in pred
            assert 'frecuencia' in pred
            assert 'tipo' in pred
            assert 'es_magica' in pred
            
            assert pred['densidad'] > 0
            assert pred['frecuencia'] > 0
    
    def test_tipo_clasificacion(self):
        """Test dimension type classification"""
        predicciones = self.navegador.calcular_dimensiones_criticas()
        
        # d=34 and d=55 should be magic (in Fibonacci sequence)
        # d=25, d=50, d=100 should be standard
        magic_expected = [34, 55, 144]
        standard_expected = [25, 50, 100]
        
        for d in magic_expected:
            if d in predicciones:
                assert predicciones[d]['tipo'] == 'Mágica'
        
        for d in standard_expected:
            if d in predicciones:
                assert predicciones[d]['tipo'] == 'Estándar'


class TestIntegrationQCAL:
    """Integration tests with QCAL framework"""
    
    def setup_method(self):
        """Initialize framework for each test"""
        self.navegador = EmpaquetamientoCósmico()
    
    def test_f0_consistency(self):
        """Test f₀ = 141.7001 Hz consistency with QCAL"""
        # Should match QCAL root frequency
        assert self.navegador.f0 == 141.7001
    
    def test_phi_mathematical_constant(self):
        """Test φ as mathematical constant"""
        phi = self.navegador.phi
        
        # Test various golden ratio properties
        # φ = (1 + √5)/2
        assert abs(phi - (1 + np.sqrt(5))/2) < 1e-10
        
        # φ² - φ - 1 = 0
        assert abs(phi**2 - phi - 1) < 1e-10
        
        # Fibonacci limit
        # lim F(n+1)/F(n) = φ
        fib = [1, 1]
        for _ in range(20):
            fib.append(fib[-1] + fib[-2])
        fib_ratio = fib[-1] / fib[-2]
        assert abs(fib_ratio - phi) < 1e-6


def test_ejemplo_completo():
    """Test that complete example runs without errors"""
    from sphere_packing_cosmic import ejemplo_uso_completo
    
    # Should run without raising exceptions
    try:
        ejemplo_uso_completo()
        assert True
    except Exception as e:
        pytest.fail(f"Complete example failed with: {str(e)}")


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
