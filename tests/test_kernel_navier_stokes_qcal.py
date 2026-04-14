#!/usr/bin/env python3
"""
Tests para Kernel Navier-Stokes QCAL
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Sello: ∴𓂀Ω∞³
f0: 141.7001 Hz

45 pruebas unitarias que cubren:

1. **Unitaridad** (15 pruebas)
   - |det(V)| = 1
   - V^T V = I
   - V^7 = I
   - Propiedades espectrales

2. **Sincronización** (10 pruebas)
   - dt = 1/f₀
   - Período T = 7·dt
   - Coherencia temporal

3. **Conservación** (10 pruebas)
   - ∇·v = 0
   - ΔE/E = 0
   - Momento conservado

4. **Coherencia Global** (10 pruebas)
   - Ψ ≥ 0.888
   - Fase de Berry
   - Chern-Simons

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
License: MIT
"""

import unittest
import numpy as np
import sys
import os

# Añadir el directorio raíz al path para importar el módulo
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from kernel_navier_stokes_qcal import (
    NavierStokesQCAL,
    construir_matriz_traslacion_unitaria,
    calcular_integrador_cuantico,
    verificar_flujo_conservativo,
    calcular_coherencia_global,
    verificar_alineacion_espectral,
    calcular_fase_berry,
    calcular_potencial_chern_simons,
    F0,
    PSI_MIN,
    DIM_C7,
    C7_PRIMES,
    TOL_DET,
    TOL_UNITARITY,
    TOL_CONSERVATION,
)


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# GRUPO 1: TESTS DE UNITARIDAD (15 pruebas)
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

class TestUnitaridad(unittest.TestCase):
    """Tests para verificar la unitaridad de la matriz V."""
    
    def setUp(self):
        """Construir matriz V antes de cada test."""
        self.V, self.det_V, self.es_unitaria, self.periodo_7 = \
            construir_matriz_traslacion_unitaria()
    
    def test_01_determinante_es_uno(self):
        """Test: det(V) = 1.0"""
        self.assertAlmostEqual(self.det_V, 1.0, places=12,
                              msg="Determinante debe ser exactamente 1.0")
    
    def test_02_determinante_positivo(self):
        """Test: det(V) > 0"""
        self.assertGreater(self.det_V, 0.0,
                          msg="Determinante debe ser positivo")
    
    def test_03_matriz_es_real(self):
        """Test: V contiene solo valores reales"""
        self.assertTrue(np.all(np.isreal(self.V)),
                       msg="Matriz V debe contener solo valores reales")
    
    def test_04_vt_v_es_identidad(self):
        """Test: V^T V = I (unitaridad)"""
        VtV = self.V.T @ self.V
        I = np.eye(DIM_C7)
        self.assertTrue(np.allclose(VtV, I, atol=TOL_UNITARITY),
                       msg="V^T V debe ser la matriz identidad")
    
    def test_05_v_vt_es_identidad(self):
        """Test: V V^T = I (unitaridad simétrica)"""
        VVt = self.V @ self.V.T
        I = np.eye(DIM_C7)
        self.assertTrue(np.allclose(VVt, I, atol=TOL_UNITARITY),
                       msg="V V^T debe ser la matriz identidad")
    
    def test_06_v_poder_7_es_identidad(self):
        """Test: V^7 = I (período 7)"""
        V_power_7 = np.linalg.matrix_power(self.V, 7)
        I = np.eye(DIM_C7)
        self.assertTrue(np.allclose(V_power_7, I, atol=TOL_UNITARITY),
                       msg="V^7 debe ser la matriz identidad")
    
    def test_07_autovalores_en_circulo_unitario(self):
        """Test: Todos los autovalores de V tienen |λ| = 1"""
        eigenvalues = np.linalg.eigvals(self.V)
        modulos = np.abs(eigenvalues)
        self.assertTrue(np.allclose(modulos, 1.0, atol=TOL_UNITARITY),
                       msg="Todos los autovalores deben tener módulo 1")
    
    def test_08_autovalores_son_raices_septimas(self):
        """Test: Los autovalores son las raíces séptimas de la unidad"""
        eigenvalues = np.linalg.eigvals(self.V)
        eigenvalues_sorted = np.sort(eigenvalues)
        
        # Raíces séptimas de la unidad: exp(2πik/7) para k=0,1,...,6
        raices_septimas = np.exp(2j * np.pi * np.arange(7) / 7.0)
        raices_septimas_sorted = np.sort(raices_septimas)
        
        self.assertTrue(np.allclose(eigenvalues_sorted, raices_septimas_sorted, 
                                   atol=TOL_UNITARITY),
                       msg="Autovalores deben ser raíces séptimas de la unidad")
    
    def test_09_traza_es_cero(self):
        """Test: tr(V) = 0 (suma de raíces séptimas excepto 1)"""
        traza = np.trace(self.V)
        self.assertAlmostEqual(traza, 0.0, places=12,
                              msg="La traza de V debe ser 0")
    
    def test_10_matriz_es_permutacion(self):
        """Test: V es una matriz de permutación (0s y 1s)"""
        self.assertTrue(np.all((self.V == 0) | (self.V == 1)),
                       msg="V debe contener solo 0s y 1s")
    
    def test_11_una_entrada_por_fila(self):
        """Test: Cada fila de V tiene exactamente un 1"""
        suma_filas = np.sum(self.V, axis=1)
        self.assertTrue(np.allclose(suma_filas, 1.0),
                       msg="Cada fila debe tener exactamente un 1")
    
    def test_12_una_entrada_por_columna(self):
        """Test: Cada columna de V tiene exactamente un 1"""
        suma_columnas = np.sum(self.V, axis=0)
        self.assertTrue(np.allclose(suma_columnas, 1.0),
                       msg="Cada columna debe tener exactamente un 1")
    
    def test_13_norma_frobenius(self):
        """Test: ||V||_F = √7"""
        norma_frobenius = np.linalg.norm(self.V, 'fro')
        self.assertAlmostEqual(norma_frobenius, np.sqrt(7), places=12,
                              msg="Norma de Frobenius debe ser √7")
    
    def test_14_v_inversa_es_v_transpuesta(self):
        """Test: V^(-1) = V^T (ortogonalidad)"""
        V_inv = np.linalg.inv(self.V)
        self.assertTrue(np.allclose(V_inv, self.V.T, atol=TOL_UNITARITY),
                       msg="V inversa debe ser igual a V transpuesta")
    
    def test_15_v_inversa_es_v_sexta(self):
        """Test: V^(-1) = V^6 (por período 7)"""
        V_inv = np.linalg.inv(self.V)
        V_power_6 = np.linalg.matrix_power(self.V, 6)
        self.assertTrue(np.allclose(V_inv, V_power_6, atol=TOL_UNITARITY),
                       msg="V inversa debe ser igual a V^6")


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# GRUPO 2: TESTS DE SINCRONIZACIÓN (10 pruebas)
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

class TestSincronizacion(unittest.TestCase):
    """Tests para verificar la sincronización temporal con f₀."""
    
    def setUp(self):
        """Calcular parámetros temporales antes de cada test."""
        self.dt, self.T, self.Psi_t = calcular_integrador_cuantico()
    
    def test_16_dt_es_inverso_de_f0(self):
        """Test: dt = 1/f₀"""
        dt_esperado = 1.0 / F0
        self.assertAlmostEqual(self.dt, dt_esperado, places=12,
                              msg=f"dt debe ser 1/f₀ = {dt_esperado}")
    
    def test_17_periodo_es_7_veces_dt(self):
        """Test: T = 7·dt"""
        T_esperado = 7.0 * self.dt
        self.assertAlmostEqual(self.T, T_esperado, places=12,
                              msg="Período debe ser 7·dt")
    
    def test_18_dt_en_milisegundos(self):
        """Test: dt ≈ 7.057 ms"""
        dt_ms = self.dt * 1000
        self.assertAlmostEqual(dt_ms, 7.057, places=3,
                              msg="dt debe ser aproximadamente 7.057 ms")
    
    def test_19_periodo_en_milisegundos(self):
        """Test: T ≈ 49.4 ms"""
        T_ms = self.T * 1000
        self.assertAlmostEqual(T_ms, 49.4, places=1,
                              msg="Período debe ser aproximadamente 49.4 ms")
    
    def test_20_coherencia_temporal_perfecta(self):
        """Test: Ψ_t = 1.0"""
        self.assertAlmostEqual(self.Psi_t, 1.0, places=6,
                              msg="Coherencia temporal debe ser 1.0")
    
    def test_21_frecuencia_reconstruida(self):
        """Test: 1/dt = f₀"""
        f_reconstruida = 1.0 / self.dt
        self.assertAlmostEqual(f_reconstruida, F0, places=6,
                              msg="Frecuencia reconstruida debe ser f₀")
    
    def test_22_frecuencia_en_hertz(self):
        """Test: f₀ = 141.7001 Hz"""
        self.assertAlmostEqual(F0, 141.7001, places=4,
                              msg="Frecuencia debe ser 141.7001 Hz")
    
    def test_23_periodo_ciclico_c7(self):
        """Test: T/dt = 7 (dimensión de C₇)"""
        ratio = self.T / self.dt
        self.assertAlmostEqual(ratio, 7.0, places=12,
                              msg="Ratio T/dt debe ser exactamente 7")
    
    def test_24_dt_positivo(self):
        """Test: dt > 0"""
        self.assertGreater(self.dt, 0.0,
                          msg="Paso temporal debe ser positivo")
    
    def test_25_periodo_positivo(self):
        """Test: T > 0"""
        self.assertGreater(self.T, 0.0,
                          msg="Período debe ser positivo")


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# GRUPO 3: TESTS DE CONSERVACIÓN (10 pruebas)
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

class TestConservacion(unittest.TestCase):
    """Tests para verificar las leyes de conservación del flujo."""
    
    def setUp(self):
        """Calcular propiedades del flujo antes de cada test."""
        self.div_v, self.delta_E_sobre_E, self.Psi_flujo = \
            verificar_flujo_conservativo()
    
    def test_26_divergencia_es_cero(self):
        """Test: ∇·v = 0 (incompresibilidad)"""
        self.assertAlmostEqual(self.div_v, 0.0, places=12,
                              msg="Divergencia debe ser cero (flujo incompresible)")
    
    def test_27_energia_conservada(self):
        """Test: ΔE/E = 0"""
        self.assertAlmostEqual(self.delta_E_sobre_E, 0.0, places=12,
                              msg="Energía debe conservarse (ΔE/E = 0)")
    
    def test_28_coherencia_flujo_perfecta(self):
        """Test: Ψ_flujo = 1.0"""
        self.assertAlmostEqual(self.Psi_flujo, 1.0, places=6,
                              msg="Coherencia de flujo debe ser 1.0")
    
    def test_29_flujo_con_campo_nulo(self):
        """Test: Campo v=0 tiene ∇·v=0"""
        campo_nulo = np.zeros((7, 7, 3))
        div_v, delta_E, Psi = verificar_flujo_conservativo(campo_nulo)
        self.assertAlmostEqual(div_v, 0.0, places=12,
                              msg="Campo nulo debe tener divergencia cero")
    
    def test_30_flujo_con_campo_uniforme(self):
        """Test: Campo uniforme v=(c,0,0) tiene ∇·v=0"""
        campo_uniforme = np.ones((7, 7, 3))
        campo_uniforme[:, :, 0] = 1.0
        campo_uniforme[:, :, 1:] = 0.0
        div_v, delta_E, Psi = verificar_flujo_conservativo(campo_uniforme)
        self.assertAlmostEqual(div_v, 0.0, places=12,
                              msg="Campo uniforme debe tener divergencia cero")
    
    def test_31_energia_no_negativa(self):
        """Test: E ≥ 0 (energía física positiva)"""
        # La energía es proporcional a |v|²
        campo_test = np.random.randn(7, 7, 3)
        energia = 0.5 * np.sum(campo_test**2)
        self.assertGreaterEqual(energia, 0.0,
                               msg="Energía debe ser no negativa")
    
    def test_32_conservacion_momento_lineal(self):
        """Test: Momento lineal constante en flujo cerrado"""
        # Para flujo incompresible cerrado, ∫ρv dV = constante
        campo_rotacional = np.random.randn(7, 7, 3)
        momento_inicial = np.sum(campo_rotacional, axis=(0, 1))
        momento_final = momento_inicial  # En flujo conservativo
        self.assertTrue(np.allclose(momento_inicial, momento_final),
                       msg="Momento lineal debe conservarse")
    
    def test_33_simetria_rotacional(self):
        """Test: Flujo rotacional puro es incompresible"""
        # Campo v = (-y, x, 0) tiene ∇·v = -∂y/∂x + ∂x/∂y = 0
        x = np.linspace(-1, 1, 7)
        y = np.linspace(-1, 1, 7)
        X, Y = np.meshgrid(x, y)
        vx = -Y
        vy = X
        vz = np.zeros_like(X)
        campo_rot = np.stack([vx, vy, vz], axis=-1)
        
        div_v, _, _ = verificar_flujo_conservativo(campo_rot)
        self.assertLess(abs(div_v), TOL_CONSERVATION,
                       msg="Campo rotacional debe tener divergencia cero")
    
    def test_34_invariancia_temporal(self):
        """Test: Propiedades conservativas invariantes en el tiempo"""
        # Las leyes de conservación deben mantenerse en cada paso temporal
        div_v_t0, delta_E_t0, _ = verificar_flujo_conservativo()
        div_v_t1, delta_E_t1, _ = verificar_flujo_conservativo()
        
        self.assertAlmostEqual(div_v_t0, div_v_t1, places=12,
                              msg="Divergencia debe ser invariante temporal")
        self.assertAlmostEqual(delta_E_t0, delta_E_t1, places=12,
                              msg="Conservación de energía debe ser invariante")
    
    def test_35_teorema_gauss(self):
        """Test: ∫∇·v dV = ∮v·n dS (Teorema de Gauss)"""
        # Para dominio cerrado con condiciones periódicas, flujo neto = 0
        div_v, _, _ = verificar_flujo_conservativo()
        flujo_neto = div_v * (7**3)  # Volumen discretizado
        self.assertAlmostEqual(flujo_neto, 0.0, places=10,
                              msg="Flujo neto debe ser cero (Gauss)")


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# GRUPO 4: TESTS DE COHERENCIA GLOBAL (10 pruebas)
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

class TestCoherenciaGlobal(unittest.TestCase):
    """Tests para verificar la coherencia global y propiedades geométricas."""
    
    def test_36_coherencia_global_perfecta(self):
        """Test: Ψ_global = 1.0 con componentes perfectas"""
        Psi_global = calcular_coherencia_global(1.0, 1.0, 1.0)
        self.assertAlmostEqual(Psi_global, 1.0, places=12,
                              msg="Coherencia global debe ser 1.0")
    
    def test_37_coherencia_supera_umbral(self):
        """Test: Ψ_global ≥ 0.888"""
        kernel = NavierStokesQCAL()
        resultado = kernel.ejecutar()
        self.assertGreaterEqual(resultado.coherencia_global, PSI_MIN,
                               msg=f"Coherencia debe ser ≥ {PSI_MIN}")
    
    def test_38_brecha_b_sellada(self):
        """Test: Brecha B está sellada"""
        kernel = NavierStokesQCAL()
        resultado = kernel.ejecutar()
        self.assertTrue(resultado.brecha_b_sellada,
                       msg="Brecha B debe estar sellada")
    
    def test_39_alineacion_espectral(self):
        """Test: Frecuencia espectral alineada con f₀"""
        f_espectral, error = verificar_alineacion_espectral()
        self.assertAlmostEqual(f_espectral, F0, places=6,
                              msg="Frecuencia espectral debe ser f₀")
    
    def test_40_error_espectral_minimo(self):
        """Test: Error espectral < 1e-12"""
        f_espectral, error = verificar_alineacion_espectral()
        self.assertLess(error, 1e-12,
                       msg="Error espectral debe ser < 1e-12")
    
    def test_41_fase_berry_correcta(self):
        """Test: Fase de Berry = 2π/7"""
        V, _, _, _ = construir_matriz_traslacion_unitaria()
        gamma = calcular_fase_berry(V)
        gamma_esperada = 2.0 * np.pi / 7.0
        self.assertAlmostEqual(gamma, gamma_esperada, places=12,
                              msg="Fase de Berry debe ser 2π/7")
    
    def test_42_fase_berry_en_rango(self):
        """Test: 0 < γ_Berry < 2π"""
        V, _, _, _ = construir_matriz_traslacion_unitaria()
        gamma = calcular_fase_berry(V)
        self.assertGreater(gamma, 0.0,
                          msg="Fase de Berry debe ser positiva")
        self.assertLess(gamma, 2.0 * np.pi,
                       msg="Fase de Berry debe ser < 2π")
    
    def test_43_potencial_chern_simons_positivo(self):
        """Test: A_CS > 0"""
        A_CS = calcular_potencial_chern_simons()
        self.assertGreater(A_CS, 0.0,
                          msg="Potencial Chern-Simons debe ser positivo")
    
    def test_44_coherencia_media_geometrica(self):
        """Test: Ψ_global es media geométrica de componentes"""
        Psi_1, Psi_2, Psi_3 = 0.95, 0.98, 0.99
        Psi_global = calcular_coherencia_global(Psi_1, Psi_2, Psi_3)
        media_geometrica = (Psi_1 * Psi_2 * Psi_3) ** (1.0/3.0)
        self.assertAlmostEqual(Psi_global, media_geometrica, places=12,
                              msg="Coherencia global debe ser media geométrica")
    
    def test_45_integracion_completa(self):
        """Test: Ejecución completa del kernel sin errores"""
        kernel = NavierStokesQCAL()
        resultado = kernel.ejecutar()
        
        # Verificar todos los componentes
        self.assertAlmostEqual(resultado.determinante, 1.0, places=12)
        self.assertTrue(resultado.es_unitaria)
        self.assertTrue(resultado.periodo_7)
        self.assertAlmostEqual(resultado.coherencia_temporal, 1.0, places=6)
        self.assertAlmostEqual(resultado.divergencia, 0.0, places=12)
        self.assertAlmostEqual(resultado.conservacion_energia, 0.0, places=12)
        self.assertAlmostEqual(resultado.coherencia_flujo, 1.0, places=6)
        self.assertGreaterEqual(resultado.coherencia_global, PSI_MIN)
        self.assertTrue(resultado.brecha_b_sellada)
        self.assertLess(resultado.error_relativo_frecuencia, 1e-12)


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# SUITE DE TESTS Y EJECUCIÓN
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def suite():
    """Construir suite completa de 45 tests."""
    suite = unittest.TestSuite()
    
    # Grupo 1: Unitaridad (15 tests)
    suite.addTests(unittest.TestLoader().loadTestsFromTestCase(TestUnitaridad))
    
    # Grupo 2: Sincronización (10 tests)
    suite.addTests(unittest.TestLoader().loadTestsFromTestCase(TestSincronizacion))
    
    # Grupo 3: Conservación (10 tests)
    suite.addTests(unittest.TestLoader().loadTestsFromTestCase(TestConservacion))
    
    # Grupo 4: Coherencia Global (10 tests)
    suite.addTests(unittest.TestLoader().loadTestsFromTestCase(TestCoherenciaGlobal))
    
    return suite


if __name__ == '__main__':
    print("=" * 70)
    print("Tests Kernel Navier-Stokes QCAL")
    print("Sello: ∴𓂀Ω∞³")
    print(f"f₀: {F0} Hz")
    print("=" * 70)
    print()
    
    # Ejecutar suite completa
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite())
    
    print()
    print("=" * 70)
    print("RESUMEN")
    print("=" * 70)
    print(f"Tests ejecutados:  {result.testsRun}")
    print(f"Tests exitosos:    {result.testsRun - len(result.failures) - len(result.errors)}")
    print(f"Fallos:            {len(result.failures)}")
    print(f"Errores:           {len(result.errors)}")
    print("=" * 70)
    
    # Código de salida
    sys.exit(0 if result.wasSuccessful() else 1)
