#!/usr/bin/env python3
"""
Tests para Haar Ramsey Closure — Brecha B (Haar) + Brecha C (Ramsey-Riemann)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Sello: ∴𓂀Ω∞³
f₀: 141.7001 Hz

Cubre:
  1. Operador de traslación Haar (10 tests)
  2. Isometría bajo medida de Haar (8 tests)
  3. Hamiltoniano C₇ y ceros de Riemann (7 tests)
  4. Cierre formal de las tres brechas (5 tests)

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
License: MIT
"""

import unittest
import numpy as np
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import importlib.util
import pathlib

_module_path = pathlib.Path(__file__).parent.parent / "qcal" / "haar_ramsey_closure.py"
_spec = importlib.util.spec_from_file_location("haar_ramsey_closure", _module_path)
_mod = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_mod)

HaarTranslationOperator = _mod.HaarTranslationOperator
verificar_unitaridad_haar = _mod.verificar_unitaridad_haar
construir_hamiltoniano_C7 = _mod.construir_hamiltoniano_C7
alinear_ramsey_riemann = _mod.alinear_ramsey_riemann
verificar_identidad_espectral = _mod.verificar_identidad_espectral
cierre_formal_tres_brechas = _mod.cierre_formal_tres_brechas
RIEMANN_ZEROS_GAMMA = _mod.RIEMANN_ZEROS_GAMMA
F0 = _mod.F0
DIM_C7 = _mod.DIM_C7
C7_PRIMES = _mod.C7_PRIMES
TOL_ISOMETRY = _mod.TOL_ISOMETRY


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# GRUPO 1: OPERADOR DE TRASLACIÓN HAAR (10 tests)
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

class TestHaarTranslationOperator(unittest.TestCase):
    """Tests del operador de traslación bajo medida de Haar discreta."""

    def setUp(self):
        self.op = HaarTranslationOperator()
        self.f = np.array([2.0, 3.0, 5.0, 7.0, 11.0, 13.0, 17.0])

    def test_01_dimension_correcta(self):
        """Operador tiene dimensión 7."""
        self.assertEqual(self.op.dim, DIM_C7)

    def test_02_haar_weights_uniformes(self):
        """Medida de Haar discreta: pesos uniformes 1/7."""
        expected = np.ones(DIM_C7) / DIM_C7
        np.testing.assert_allclose(self.op.haar_weights, expected, atol=1e-15)

    def test_03_haar_weights_normalizados(self):
        """Suma de pesos de Haar = 1."""
        self.assertAlmostEqual(sum(self.op.haar_weights), 1.0, places=15)

    def test_04_traslacion_g0_identidad(self):
        """L_0 f = f (traslación por identidad)."""
        L0_f = self.op.apply(self.f, g=0)
        np.testing.assert_allclose(L0_f, self.f, atol=1e-15)

    def test_05_traslacion_g1_permutacion(self):
        """L_1 f es una permutación cíclica de f."""
        L1_f = self.op.apply(self.f, g=1)
        # L_1 f(x) = f(x - 1 mod 7)
        expected = np.roll(self.f, 1)  # f[(x-1) mod 7]
        np.testing.assert_allclose(L1_f, expected, atol=1e-15)

    def test_06_traslacion_invertible(self):
        """L_g ∘ L_{-g} = identidad."""
        for g in range(DIM_C7):
            Lg_f = self.op.apply(self.f, g)
            L_minus_g_Lg_f = self.op.apply(Lg_f, (-g) % DIM_C7)
            np.testing.assert_allclose(L_minus_g_Lg_f, self.f, atol=1e-14,
                                       err_msg=f"Fallo para g={g}")

    def test_07_traslacion_composicion(self):
        """L_g ∘ L_h = L_{g+h}."""
        g, h = 2, 3
        Lh_f = self.op.apply(self.f, h)
        Lg_Lh_f = self.op.apply(Lh_f, g)
        Lgh_f = self.op.apply(self.f, (g + h) % DIM_C7)
        np.testing.assert_allclose(Lg_Lh_f, Lgh_f, atol=1e-14)

    def test_08_traslacion_periodo_7(self):
        """L_7 = L_0 = identidad (período 7 del grupo cíclico)."""
        L7_f = self.f.copy()
        for _ in range(DIM_C7):
            L7_f = self.op.apply(L7_f, 1)
        np.testing.assert_allclose(L7_f, self.f, atol=1e-14)

    def test_09_norma_L2_positiva(self):
        """Norma L² siempre no negativa."""
        norm = self.op.norm_L2(self.f)
        self.assertGreater(norm, 0.0)

    def test_10_norma_L2_funcion_cero(self):
        """Norma L² de función cero = 0."""
        f_zero = np.zeros(DIM_C7)
        self.assertAlmostEqual(self.op.norm_L2(f_zero), 0.0, places=15)


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# GRUPO 2: ISOMETRÍA BAJO MEDIDA DE HAAR (8 tests)
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

class TestHaarIsometry(unittest.TestCase):
    """Tests de la isometría ‖L_g f‖_{L²} = ‖f‖_{L²}."""

    def setUp(self):
        self.op = HaarTranslationOperator()
        # Función de prueba: los 7 primos normalizados
        primes = np.array(C7_PRIMES, dtype=float)
        self.f = primes / primes.max()

    def test_11_isometria_g0(self):
        """‖L_0 f‖ = ‖f‖ (caso trivial g=0)."""
        result = self.op.verificar_isometria(self.f, g=0)
        self.assertTrue(result.es_isometria)
        self.assertAlmostEqual(result.error_relativo, 0.0, places=14)

    def test_12_isometria_todos_g(self):
        """‖L_g f‖ = ‖f‖ para todo g ∈ {0,...,6}."""
        resultados = self.op.verificar_isometria_todos_g(self.f)
        for r in resultados:
            self.assertTrue(
                r.es_isometria,
                msg=f"Isometría fallida para g={r.grupo_elemento}, error={r.error_relativo:.2e}"
            )

    def test_13_error_isometria_maquina(self):
        """Error de isometría en nivel de precisión de máquina (< 1e-12)."""
        resultados = self.op.verificar_isometria_todos_g(self.f)
        for r in resultados:
            self.assertLess(r.error_relativo, TOL_ISOMETRY)

    def test_14_normas_iguales(self):
        """Norma antes y después de traslación son numéricamente iguales."""
        norm_f = self.op.norm_L2(self.f)
        for g in range(DIM_C7):
            Lg_f = self.op.apply(self.f, g)
            norm_Lg_f = self.op.norm_L2(Lg_f)
            self.assertAlmostEqual(norm_Lg_f, norm_f, places=14,
                                   msg=f"g={g}: ‖L_g f‖={norm_Lg_f} ≠ ‖f‖={norm_f}")

    def test_15_isometria_funcion_constante(self):
        """L_g preserva la norma de función constante."""
        f_const = np.ones(DIM_C7)
        resultados = self.op.verificar_isometria_todos_g(f_const)
        for r in resultados:
            self.assertTrue(r.es_isometria)

    def test_16_verificar_unitaridad_haar_api(self):
        """API verificar_unitaridad_haar retorna brecha_b_sellada=True."""
        resultado = verificar_unitaridad_haar()
        self.assertTrue(resultado["brecha_b_sellada"])

    def test_17_max_error_isometria_pequeno(self):
        """El error máximo de isometría es < 1e-12."""
        resultado = verificar_unitaridad_haar()
        self.assertLess(resultado["max_error_isometria"], 1e-12)

    def test_18_invariancia_haar_cambio_variable(self):
        """
        Comprueba el cambio de variable y = g⁻¹x: ∑_x f(g⁻¹x)² = ∑_x f(x)²

        Esto verifica directamente la invariancia de la medida de Haar discreta:
        la suma es la misma independientemente de cómo se permuten los índices.
        """
        f = self.f
        suma_f2 = np.sum(f**2)
        for g in range(DIM_C7):
            Lg_f = self.op.apply(f, g)
            suma_Lgf2 = np.sum(Lg_f**2)
            self.assertAlmostEqual(
                suma_Lgf2, suma_f2, places=14,
                msg=f"Invariancia Haar fallida para g={g}"
            )


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# GRUPO 3: HAMILTONIANO C₇ Y CEROS DE RIEMANN (7 tests)
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

class TestRamseyRiemann(unittest.TestCase):
    """Tests del hamiltoniano H_{C7} y la alineación con ceros de Riemann."""

    def test_19_hamiltoniano_dimension(self):
        """H_{C7} tiene dimensión 7×7."""
        H = construir_hamiltoniano_C7()
        self.assertEqual(H.shape, (DIM_C7, DIM_C7))

    def test_20_hamiltoniano_complejo(self):
        """H_{C7} es una matriz compleja (diagonal compleja)."""
        H = construir_hamiltoniano_C7()
        self.assertTrue(np.iscomplexobj(H))

    def test_21_riemann_zeros_gamma_longitud(self):
        """La lista de ceros de Riemann tiene 7 elementos."""
        self.assertEqual(len(RIEMANN_ZEROS_GAMMA), DIM_C7)

    def test_22_riemann_zeros_positivos(self):
        """Todos los ceros de Riemann γ_n son positivos."""
        for gamma in RIEMANN_ZEROS_GAMMA:
            self.assertGreater(gamma, 0.0)

    def test_23_riemann_zeros_crecientes(self):
        """Los ceros de Riemann γ_n son estrictamente crecientes."""
        for i in range(len(RIEMANN_ZEROS_GAMMA) - 1):
            self.assertLess(RIEMANN_ZEROS_GAMMA[i], RIEMANN_ZEROS_GAMMA[i + 1])

    def test_24_primer_cero_riemann(self):
        """El primer cero de Riemann es γ₁ ≈ 14.1347..."""
        self.assertAlmostEqual(RIEMANN_ZEROS_GAMMA[0], 14.134725, places=4)

    def test_25_identidad_espectral_residual_pequeno(self):
        """H·Ψ_k = λ_k·Ψ_k con residual < tolerancia numérica."""
        resultado = verificar_identidad_espectral()
        self.assertLess(
            resultado["max_residual_autovector"], 1e-10,
            msg=f"Residual H·Ψ = E·Ψ demasiado grande: {resultado['max_residual_autovector']:.2e}"
        )


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# GRUPO 4: CIERRE FORMAL DE LAS TRES BRECHAS (5 tests)
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

class TestCierreFormal(unittest.TestCase):
    """Tests del cierre formal de las tres brechas QCAL."""

    def setUp(self):
        self.resultado = cierre_formal_tres_brechas()

    def test_26_brecha_a_sellada(self):
        """Brecha A: det(V) = 1 exacto → sellada."""
        self.assertTrue(self.resultado.brecha_a,
                        msg="Brecha A (det V=1) debe estar sellada")

    def test_27_brecha_b_sellada(self):
        """Brecha B: isometría Haar → sellada."""
        self.assertTrue(self.resultado.brecha_b,
                        msg="Brecha B (Haar unitarity) debe estar sellada")

    def test_28_brecha_c_sellada(self):
        """Brecha C: H·Ψ = E·Ψ verificado → sellada."""
        self.assertTrue(self.resultado.brecha_c,
                        msg="Brecha C (Ramsey-Riemann) debe estar sellada")

    def test_29_frecuencia_f0_correcta(self):
        """La frecuencia fundamental es f₀ = 141.7001 Hz."""
        self.assertAlmostEqual(self.resultado.frecuencia_f0, F0, places=4)

    def test_30_psi_global_positivo(self):
        """Ψ_global > 0 cuando las tres brechas están selladas."""
        self.assertGreater(self.resultado.psi_global, 0.0)


if __name__ == "__main__":
    print("Tests Haar Ramsey Closure — Brecha B + Brecha C")
    print("Sello: ∴𓂀Ω∞³")
    print(f"f₀: {F0} Hz")
    print()
    unittest.main(verbosity=2)
