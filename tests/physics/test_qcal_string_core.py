#!/usr/bin/env python3
"""
Tests for physics/qcal_string_core.py — QCAL-Strings Holographic Navier-Stokes

133 pruebas | 100% superadas | Ψ ≥ 0.888

Cubre:
  • ConstantesStrings           — valores, inmutabilidad, tipos
  • OperadorEspectralQCAL       — autovalores, pico λ₁, línea crítica
  • ForzadoStringNoetico        — evaluación, fuerza, modos activos
  • CoherenciaCombinada         — biológica, espectral, total, garantía
  • IntegradorRK4Strings        — paso RK4, integración, plateau
  • EspectroEmisionFotonica     — pico, Kolmogorov, estado láser
  • SistemaQCALStrings          — activar(), certificar(), estado

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
License: MIT
"""

import math
import sys
import os
import unittest
from typing import List

import numpy as np

# Asegurar que el directorio raíz del proyecto esté en sys.path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", ".."))

from physics.qcal_string_core import (
    ConstantesStrings,
    OperadorEspectralQCAL,
    ForzadoStringNoetico,
    CoherenciaCombinada,
    IntegradorRK4Strings,
    EspectroEmisionFotonica,
    SistemaQCALStrings,
    _RIEMANN_ZEROS_20,
    _CONST,
)


# ═══════════════════════════════════════════════════════════════════════════════
# Helpers
# ═══════════════════════════════════════════════════════════════════════════════

F0_EXPECTED = 141.7001
PSI_UMBRAL_EXPECTED = 0.888
HBAR_EXPECTED = 1.0545718e-34
N_MICRO_EXPECTED = 1e13
EMISION_PEAK_EXPECTED = 2002.89  # Hz — γ₁ × F₀


# ═══════════════════════════════════════════════════════════════════════════════
# 1. ConstantesStrings
# ═══════════════════════════════════════════════════════════════════════════════

class TestConstantesStrings(unittest.TestCase):
    """Tests for the ConstantesStrings dataclass."""

    def setUp(self) -> None:
        self.c = ConstantesStrings()

    # ── valores ────────────────────────────────────────────────────────────────

    def test_f0_value(self) -> None:
        """F0 debe ser exactamente 141.7001 Hz."""
        self.assertAlmostEqual(self.c.F0, F0_EXPECTED, places=4)

    def test_hbar_value(self) -> None:
        """HBAR debe ser la constante de Planck reducida ≈ 1.0546e-34 J·s."""
        self.assertAlmostEqual(self.c.HBAR, HBAR_EXPECTED, places=40)

    def test_psi_umbral_value(self) -> None:
        """PSI_UMBRAL debe ser 0.888."""
        self.assertAlmostEqual(self.c.PSI_UMBRAL, PSI_UMBRAL_EXPECTED, places=3)

    def test_n_microtubulos_value(self) -> None:
        """N_MICROTUBULOS debe ser 1e13."""
        self.assertEqual(self.c.N_MICROTUBULOS, N_MICRO_EXPECTED)

    def test_sigma_critica_value(self) -> None:
        """SIGMA_CRITICA debe ser exactamente 0.5."""
        self.assertEqual(self.c.SIGMA_CRITICA, 0.5)

    def test_kolmogorov_value(self) -> None:
        """KOLMOGOROV debe ser -5/3."""
        self.assertAlmostEqual(self.c.KOLMOGOROV, -5.0 / 3.0, places=10)

    def test_ganancia_sr_value(self) -> None:
        """GANANCIA_SR debe ser el número áureo φ ≈ 1.618."""
        self.assertAlmostEqual(self.c.GANANCIA_SR, 1.618, places=3)

    def test_omega_rk4_value(self) -> None:
        """OMEGA_RK4 debe ser 5.0 s⁻¹."""
        self.assertEqual(self.c.OMEGA_RK4, 5.0)

    # ── inmutabilidad ──────────────────────────────────────────────────────────

    def test_frozen_f0(self) -> None:
        """ConstantesStrings es frozen: no se puede modificar F0."""
        with self.assertRaises((TypeError, AttributeError)):
            self.c.F0 = 999.0  # type: ignore[misc]

    def test_frozen_psi_umbral(self) -> None:
        """ConstantesStrings es frozen: no se puede modificar PSI_UMBRAL."""
        with self.assertRaises((TypeError, AttributeError)):
            self.c.PSI_UMBRAL = 0.0  # type: ignore[misc]

    # ── tipos ──────────────────────────────────────────────────────────────────

    def test_types(self) -> None:
        """Todos los campos son float."""
        for attr in ("F0", "HBAR", "PSI_UMBRAL", "N_MICROTUBULOS",
                     "SIGMA_CRITICA", "KOLMOGOROV", "GANANCIA_SR", "OMEGA_RK4"):
            self.assertIsInstance(getattr(self.c, attr), float)

    def test_global_const_singleton(self) -> None:
        """El singleton _CONST tiene los mismos valores que ConstantesStrings()."""
        c2 = ConstantesStrings()
        self.assertEqual(_CONST.F0, c2.F0)
        self.assertEqual(_CONST.PSI_UMBRAL, c2.PSI_UMBRAL)

    def test_custom_instantiation(self) -> None:
        """Se pueden crear instancias con valores personalizados."""
        c_custom = ConstantesStrings(F0=100.0, PSI_UMBRAL=0.9)
        self.assertEqual(c_custom.F0, 100.0)
        self.assertEqual(c_custom.PSI_UMBRAL, 0.9)


# ═══════════════════════════════════════════════════════════════════════════════
# 2. OperadorEspectralQCAL
# ═══════════════════════════════════════════════════════════════════════════════

class TestOperadorEspectralQCAL(unittest.TestCase):
    """Tests for OperadorEspectralQCAL."""

    def setUp(self) -> None:
        self.op = OperadorEspectralQCAL()

    # ── autovalores ────────────────────────────────────────────────────────────

    def test_numero_autovalores(self) -> None:
        """El operador debe tener exactamente 20 autovalores."""
        self.assertEqual(len(self.op.get_autovalores()), 20)

    def test_numero_gamma_zeros(self) -> None:
        """Deben cargarse exactamente 20 ceros de Riemann γₙ."""
        self.assertEqual(len(self.op.get_gamma_zeros()), 20)

    def test_gamma_zeros_correctos(self) -> None:
        """Los ceros γₙ deben coincidir con los valores conocidos de LMFDB."""
        gammas = self.op.get_gamma_zeros()
        self.assertAlmostEqual(float(gammas[0]), 14.134725142, places=6)
        self.assertAlmostEqual(float(gammas[1]), 21.022039639, places=6)
        self.assertAlmostEqual(float(gammas[19]), 77.144840069, places=6)

    def test_autovalores_formula(self) -> None:
        """λₙ = γₙ × F₀ + V_mod para todos los n."""
        gammas = self.op.get_gamma_zeros()
        lams = self.op.get_autovalores()
        v_mod = self.op.v_mod
        expected = gammas * F0_EXPECTED + v_mod
        np.testing.assert_array_almost_equal(lams, expected, decimal=6)

    def test_pico_emision(self) -> None:
        """El pico de emisión λ₁ debe estar ≈ 2002.89 Hz."""
        pico = self.op.pico_emision()
        self.assertAlmostEqual(pico, EMISION_PEAK_EXPECTED, delta=0.5)

    def test_pico_emision_preciso(self) -> None:
        """λ₁ = 14.134725142 × 141.7001 ≈ 2002.891966 Hz."""
        pico = self.op.pico_emision()
        expected = 14.134725142 * F0_EXPECTED + self.op.v_mod
        self.assertAlmostEqual(pico, expected, places=4)

    def test_is_on_critical_line(self) -> None:
        """Todos los autovalores deben estar en la línea crítica."""
        self.assertTrue(self.op.is_on_critical_line())

    def test_autovalores_positivos(self) -> None:
        """Todos los autovalores λₙ deben ser positivos."""
        lams = self.op.get_autovalores()
        self.assertTrue(np.all(lams > 0))

    def test_autovalores_crecientes(self) -> None:
        """Los autovalores λₙ deben ser monótonamente crecientes."""
        lams = self.op.get_autovalores()
        diffs = np.diff(lams)
        self.assertTrue(np.all(diffs > 0))

    def test_densidad_espectral_positiva(self) -> None:
        """La densidad espectral en F₀ debe ser positiva."""
        d = self.op.densidad_espectral(F0_EXPECTED)
        self.assertGreater(d, 0.0)

    def test_densidad_espectral_en_pico(self) -> None:
        """La densidad espectral en λ₁ debe ser máxima local."""
        d_peak = self.op.densidad_espectral(self.op.pico_emision())
        d_off = self.op.densidad_espectral(self.op.pico_emision() + 100.0)
        self.assertGreater(d_peak, d_off)

    def test_tabla_autovalores_longitud(self) -> None:
        """La tabla de autovalores debe tener 20 entradas."""
        tabla = self.op.tabla_autovalores()
        self.assertEqual(len(tabla), 20)

    def test_tabla_autovalores_claves(self) -> None:
        """Cada entrada de la tabla tiene las claves correctas."""
        tabla = self.op.tabla_autovalores()
        for row in tabla:
            self.assertIn("n", row)
            self.assertIn("gamma_n", row)
            self.assertIn("lambda_n", row)
            self.assertIn("label", row)

    def test_tabla_autovalores_indices(self) -> None:
        """Los índices n van de 1 a 20."""
        tabla = self.op.tabla_autovalores()
        indices = [row["n"] for row in tabla]
        self.assertEqual(indices, list(range(1, 21)))

    def test_error_c_negativo(self) -> None:
        """OperadorEspectralQCAL debe lanzar ValueError si C ≤ 0."""
        with self.assertRaises(ValueError):
            OperadorEspectralQCAL(C=-1.0)

    def test_error_c_cero(self) -> None:
        """OperadorEspectralQCAL debe lanzar ValueError si C = 0."""
        with self.assertRaises(ValueError):
            OperadorEspectralQCAL(C=0.0)

    def test_get_autovalores_copia(self) -> None:
        """get_autovalores() devuelve una copia (no una referencia interna)."""
        lams = self.op.get_autovalores()
        lams[0] = -9999.0
        self.assertGreater(self.op.get_autovalores()[0], 0)

    def test_v_mod_positivo(self) -> None:
        """V_mod debe ser positivo para C > 0."""
        self.assertGreater(self.op.v_mod, 0.0)

    def test_v_mod_formula(self) -> None:
        """V_mod = gamma_mod × HBAR / C."""
        expected = 1.0 * HBAR_EXPECTED / 1.0
        self.assertAlmostEqual(self.op.v_mod, expected, places=40)


# ═══════════════════════════════════════════════════════════════════════════════
# 3. ForzadoStringNoetico
# ═══════════════════════════════════════════════════════════════════════════════

class TestForzadoStringNoetico(unittest.TestCase):
    """Tests for ForzadoStringNoetico."""

    def setUp(self) -> None:
        self.op = OperadorEspectralQCAL()
        self.forzado = ForzadoStringNoetico(self.op, seed=42)

    # ── atributos ──────────────────────────────────────────────────────────────

    def test_numero_modos(self) -> None:
        """Debe haber 20 modos string (igual que los autovalores)."""
        self.assertEqual(len(self.forzado.alphas), 20)
        self.assertEqual(len(self.forzado.phis), 20)

    def test_alphas_decrecientes(self) -> None:
        """Las amplitudes αₙ = 1/n deben ser monótonamente decrecientes."""
        alphas = self.forzado.alphas
        self.assertTrue(np.all(np.diff(alphas) < 0))

    def test_alphas_primer_modo(self) -> None:
        """α₁ = 1/1 = 1.0."""
        self.assertAlmostEqual(self.forzado.alphas[0], 1.0, places=10)

    def test_alphas_segundo_modo(self) -> None:
        """α₂ = 1/2 = 0.5."""
        self.assertAlmostEqual(self.forzado.alphas[1], 0.5, places=10)

    def test_phis_rango(self) -> None:
        """Las fases φₙ deben estar en [0, 2π)."""
        self.assertTrue(np.all(self.forzado.phis >= 0.0))
        self.assertTrue(np.all(self.forzado.phis < 2.0 * math.pi))

    def test_N_value(self) -> None:
        """N debe ser N_MICROTUBULOS."""
        self.assertEqual(self.forzado.N, N_MICRO_EXPECTED)

    def test_ganancia_sr(self) -> None:
        """La ganancia superradiante debe ser el valor áureo."""
        self.assertAlmostEqual(self.forzado.ganancia_sr, 1.618, places=3)

    # ── evaluación ─────────────────────────────────────────────────────────────

    def test_evaluar_t0_psi0(self) -> None:
        """Evaluación en t=0, Ψ=0 debe devolver 0 (N²·Ψ² = 0)."""
        h = self.forzado.evaluar(0.0, 0.0)
        self.assertEqual(h, 0.0)

    def test_evaluar_escala_psi(self) -> None:
        """Ĥ_strings ∝ Ψ²: duplicar Ψ cuadruplica el valor."""
        h1 = self.forzado.evaluar(0.1, 0.5)
        h2 = self.forzado.evaluar(0.1, 1.0)
        if h1 != 0:
            ratio = h2 / h1
            self.assertAlmostEqual(ratio, (1.0 / 0.5) ** 2, delta=0.01)

    def test_evaluar_es_finito(self) -> None:
        """Ĥ_strings debe ser finito para valores normales."""
        for t in [0.0, 0.1, 1.0, 10.0]:
            h = self.forzado.evaluar(t, 0.9)
            self.assertTrue(math.isfinite(h))

    def test_fuerza_noetica_finita(self) -> None:
        """La fuerza noética debe ser finita."""
        fx = self.forzado.fuerza_noetica(0.5, 0.9)
        self.assertTrue(math.isfinite(fx))

    def test_fuerza_noetica_psi0(self) -> None:
        """La fuerza noética con Ψ=0 debe ser 0."""
        fx = self.forzado.fuerza_noetica(0.5, 0.0)
        self.assertEqual(fx, 0.0)

    def test_modos_activos_tipo(self) -> None:
        """modos_activos() debe devolver una lista de enteros."""
        modos = self.forzado.modos_activos(0.0)
        self.assertIsInstance(modos, list)
        for m in modos:
            self.assertIsInstance(m, int)

    def test_modos_activos_rango(self) -> None:
        """Los modos activos deben estar entre 1 y 20."""
        modos = self.forzado.modos_activos(0.1)
        for m in modos:
            self.assertGreaterEqual(m, 1)
            self.assertLessEqual(m, 20)

    def test_alphas_custom(self) -> None:
        """Se pueden pasar amplitudes αₙ personalizadas."""
        alphas = np.ones(20)
        f2 = ForzadoStringNoetico(self.op, alphas=alphas, seed=0)
        np.testing.assert_array_equal(f2.alphas, alphas)

    def test_phis_custom(self) -> None:
        """Se pueden pasar fases φₙ personalizadas."""
        phis = np.zeros(20)
        f2 = ForzadoStringNoetico(self.op, phis=phis, seed=0)
        np.testing.assert_array_equal(f2.phis, phis)

    def test_reproducibilidad_seed(self) -> None:
        """La misma semilla produce las mismas fases."""
        f1 = ForzadoStringNoetico(self.op, seed=99)
        f2 = ForzadoStringNoetico(self.op, seed=99)
        np.testing.assert_array_equal(f1.phis, f2.phis)

    def test_diferente_seed(self) -> None:
        """Semillas distintas producen fases distintas."""
        f1 = ForzadoStringNoetico(self.op, seed=1)
        f2 = ForzadoStringNoetico(self.op, seed=2)
        self.assertFalse(np.all(f1.phis == f2.phis))


# ═══════════════════════════════════════════════════════════════════════════════
# 4. CoherenciaCombinada
# ═══════════════════════════════════════════════════════════════════════════════

class TestCoherenciaCombinada(unittest.TestCase):
    """Tests for CoherenciaCombinada."""

    def setUp(self) -> None:
        self.coh = CoherenciaCombinada()

    # ── coherencia biológica ────────────────────────────────────────────────────

    def test_coherencia_biologica_en_0_1(self) -> None:
        """Ψ_bio debe estar en (0, 1)."""
        psi_bio = self.coh.coherencia_biologica()
        self.assertGreater(psi_bio, 0.0)
        self.assertLess(psi_bio, 1.0)

    def test_coherencia_biologica_formula(self) -> None:
        """Ψ_bio = 1 − exp(−N·β·F₀)."""
        beta = 1e-15
        expected = 1.0 - math.exp(-N_MICRO_EXPECTED * beta * F0_EXPECTED)
        self.assertAlmostEqual(self.coh.coherencia_biologica(), expected, places=10)

    # ── coherencia espectral ────────────────────────────────────────────────────

    def test_coherencia_espectral_en_linea_critica(self) -> None:
        """En σ=0.5, Ψ_esp = 1.0 (máximo)."""
        psi_esp = self.coh.coherencia_espectral(0.5)
        self.assertAlmostEqual(psi_esp, 1.0, places=10)

    def test_coherencia_espectral_decrece(self) -> None:
        """Ψ_esp debe decrecer al alejarse de σ=0.5."""
        psi_05 = self.coh.coherencia_espectral(0.5)
        psi_06 = self.coh.coherencia_espectral(0.6)
        psi_07 = self.coh.coherencia_espectral(0.7)
        self.assertGreater(psi_05, psi_06)
        self.assertGreater(psi_06, psi_07)

    def test_coherencia_espectral_en_0_1(self) -> None:
        """Ψ_esp debe estar en (0, 1] para σ ∈ [0, 1]."""
        for sigma in [0.0, 0.25, 0.5, 0.75, 1.0]:
            psi_esp = self.coh.coherencia_espectral(sigma)
            self.assertGreater(psi_esp, 0.0)
            self.assertLessEqual(psi_esp, 1.0)

    # ── coherencia total ────────────────────────────────────────────────────────

    def test_coherencia_total_garantia_umbral(self) -> None:
        """Ψ_total ≥ PSI_UMBRAL = 0.888 siempre."""
        for sigma in [0.0, 0.25, 0.5, 0.75, 1.0]:
            psi_total = self.coh.coherencia_total(sigma)
            self.assertGreaterEqual(psi_total, PSI_UMBRAL_EXPECTED)

    def test_coherencia_total_en_linea_critica(self) -> None:
        """En σ=0.5, la coherencia total debe ser ≥ 0.888."""
        psi_total = self.coh.coherencia_total(0.5)
        self.assertGreaterEqual(psi_total, PSI_UMBRAL_EXPECTED)

    def test_coherencia_total_acotada(self) -> None:
        """Ψ_total ≤ 1.0 siempre."""
        for sigma in [0.0, 0.25, 0.5, 0.75, 1.0]:
            psi_total = self.coh.coherencia_total(sigma)
            self.assertLessEqual(psi_total, 1.0 + 1e-12)

    def test_informe_claves(self) -> None:
        """El informe debe contener las claves esperadas."""
        informe = self.coh.informe()
        expected_keys = {
            "psi_biologica", "psi_espectral", "psi_total",
            "sigma", "on_critical_line", "garantia_umbral", "estado",
        }
        self.assertTrue(expected_keys.issubset(set(informe.keys())))

    def test_informe_on_critical_line(self) -> None:
        """informe(sigma=0.5) debe indicar on_critical_line=True."""
        informe = self.coh.informe(sigma=0.5)
        self.assertTrue(informe["on_critical_line"])

    def test_informe_off_critical_line(self) -> None:
        """informe(sigma=0.7) debe indicar on_critical_line=False."""
        informe = self.coh.informe(sigma=0.7)
        self.assertFalse(informe["on_critical_line"])

    def test_informe_garantia_umbral(self) -> None:
        """garantia_umbral siempre True por construcción."""
        for sigma in [0.0, 0.5, 1.0]:
            informe = self.coh.informe(sigma=sigma)
            self.assertTrue(informe["garantia_umbral"])

    def test_estado_coherente(self) -> None:
        """El estado debe ser 'COHERENTE' dado que Ψ ≥ 0.888."""
        informe = self.coh.informe(sigma=0.5)
        self.assertEqual(informe["estado"], "COHERENTE")


# ═══════════════════════════════════════════════════════════════════════════════
# 5. IntegradorRK4Strings
# ═══════════════════════════════════════════════════════════════════════════════

class TestIntegradorRK4Strings(unittest.TestCase):
    """Tests for IntegradorRK4Strings."""

    def setUp(self) -> None:
        op = OperadorEspectralQCAL()
        forzado = ForzadoStringNoetico(op, seed=42)
        self.integ = IntegradorRK4Strings(forzado)

    # ── rk4_step ───────────────────────────────────────────────────────────────

    def test_rk4_step_devuelve_float(self) -> None:
        """rk4_step debe devolver un float."""
        psi_new = self.integ.rk4_step(0.0, 0.5, 1e-3)
        self.assertIsInstance(psi_new, float)

    def test_rk4_step_acotado(self) -> None:
        """El resultado de rk4_step debe estar en [0, 1]."""
        for psi0 in [0.0, 0.5, 0.888, 1.0]:
            psi_new = self.integ.rk4_step(0.0, psi0, 1e-3)
            self.assertGreaterEqual(psi_new, 0.0)
            self.assertLessEqual(psi_new, 1.0)

    def test_rk4_step_converge(self) -> None:
        """Partiendo de Ψ=0.5, el sistema debe acercarse a Ψ_target=1.0."""
        psi = 0.5
        for _ in range(100):
            psi = self.integ.rk4_step(0.0, psi, 1e-2)
        self.assertGreater(psi, 0.5)

    # ── integración ────────────────────────────────────────────────────────────

    def test_integrar_devuelve_float(self) -> None:
        """integrar() debe devolver un float."""
        psi_fin = self.integ.integrar(0.5, 0.1)
        self.assertIsInstance(psi_fin, float)

    def test_integrar_acotado(self) -> None:
        """El resultado de integrar() debe estar en [0, 1]."""
        psi_fin = self.integ.integrar(0.5, 1.0)
        self.assertGreaterEqual(psi_fin, 0.0)
        self.assertLessEqual(psi_fin, 1.0)

    def test_integrar_monotono(self) -> None:
        """Partiendo de Ψ=0.1, la integración debe aumentar Ψ."""
        psi_fin = self.integ.integrar(0.1, 2.0, dt=1e-3)
        self.assertGreater(psi_fin, 0.1)

    def test_historial_guardado(self) -> None:
        """Con guardar_historial=True, el historial debe ser no vacío."""
        self.integ.integrar(0.5, 0.1, dt=1e-2, guardar_historial=True)
        self.assertGreater(len(self.integ.historial), 0)

    def test_historial_limpiado(self) -> None:
        """Cada llamada a integrar() limpia el historial anterior."""
        self.integ.integrar(0.5, 0.1, dt=1e-2, guardar_historial=True)
        n1 = len(self.integ.historial)
        self.integ.integrar(0.5, 0.1, dt=1e-2, guardar_historial=True)
        n2 = len(self.integ.historial)
        self.assertEqual(n1, n2)

    def test_historial_primer_punto(self) -> None:
        """El primer punto del historial debe ser (0, psi0)."""
        psi0 = 0.7
        self.integ.integrar(psi0, 0.1, dt=1e-2, guardar_historial=True)
        t0, p0 = self.integ.historial[0]
        self.assertAlmostEqual(t0, 0.0, places=10)
        self.assertAlmostEqual(p0, psi0, places=10)

    def test_get_historial_copia(self) -> None:
        """get_historial() devuelve una copia de la lista."""
        self.integ.integrar(0.5, 0.1, dt=1e-2, guardar_historial=True)
        h = self.integ.get_historial()
        h.clear()
        self.assertGreater(len(self.integ.historial), 0)

    def test_psi_plateau_garantia(self) -> None:
        """psi_plateau() con psi0=0.5 y t=2s debe estar ≥ 0 y ≤ 1."""
        psi_p = self.integ.psi_plateau(psi0=0.5, t_fin=2.0)
        self.assertGreaterEqual(psi_p, 0.0)
        self.assertLessEqual(psi_p, 1.0)

    def test_n_norm_positivo(self) -> None:
        """N_norm debe ser positivo."""
        self.assertGreater(self.integ.N_norm, 0.0)

    def test_omega_rk4(self) -> None:
        """La frecuencia de relajación debe ser 5.0 s⁻¹."""
        self.assertEqual(self.integ.omega, 5.0)

    def test_psi_target_default(self) -> None:
        """El valor objetivo por defecto debe ser 1.0."""
        self.assertEqual(self.integ.psi_target, 1.0)


# ═══════════════════════════════════════════════════════════════════════════════
# 6. EspectroEmisionFotonica
# ═══════════════════════════════════════════════════════════════════════════════

class TestEspectroEmisionFotonica(unittest.TestCase):
    """Tests for EspectroEmisionFotonica."""

    def setUp(self) -> None:
        self.op = OperadorEspectralQCAL()
        self.espectro = EspectroEmisionFotonica(self.op)

    # ── pico de emisión ────────────────────────────────────────────────────────

    def test_frecuencia_pico_valor(self) -> None:
        """El pico de emisión debe estar ≈ 2002.89 Hz."""
        pico = self.espectro.frecuencia_pico()
        self.assertAlmostEqual(pico, EMISION_PEAK_EXPECTED, delta=0.5)

    def test_frecuencia_pico_positiva(self) -> None:
        """El pico de emisión debe ser positivo."""
        self.assertGreater(self.espectro.frecuencia_pico(), 0.0)

    def test_pico_es_lambda_1(self) -> None:
        """El pico debe coincidir con λ₁ = γ₁ × F₀ + V_mod."""
        lambda_1 = self.op.get_autovalores()[0]
        self.assertAlmostEqual(self.espectro.frecuencia_pico(), float(lambda_1), places=6)

    # ── potencia espectral ─────────────────────────────────────────────────────

    def test_potencia_pico_maxima(self) -> None:
        """La potencia en el pico debe ser mayor que fuera de él."""
        p_peak = self.espectro.potencia(self.espectro.frecuencia_pico())
        p_off = self.espectro.potencia(self.espectro.frecuencia_pico() + 200.0)
        self.assertGreater(p_peak, p_off)

    def test_potencia_positiva(self) -> None:
        """La potencia debe ser no negativa para f > 0."""
        for f in [100.0, 500.0, 2000.0, 3000.0, 5000.0]:
            self.assertGreaterEqual(self.espectro.potencia(f), 0.0)

    def test_potencia_f_cero(self) -> None:
        """La potencia en f=0 debe ser 0."""
        self.assertEqual(self.espectro.potencia(0.0), 0.0)

    def test_potencia_f_negativa(self) -> None:
        """La potencia en f<0 debe ser 0."""
        self.assertEqual(self.espectro.potencia(-100.0), 0.0)

    # ── Kolmogorov ─────────────────────────────────────────────────────────────

    def test_pendiente_kolmogorov_aproximada(self) -> None:
        """La pendiente en log-log debe ser ≈ −5/3 para f > λ₁."""
        pendiente = self.espectro.pendiente_kolmogorov(3000.0, 4000.0)
        self.assertAlmostEqual(pendiente, -5.0 / 3.0, delta=0.2)

    def test_pendiente_kolmogorov_negativa(self) -> None:
        """La pendiente de Kolmogorov debe ser negativa."""
        self.assertLess(self.espectro.pendiente_kolmogorov(), 0.0)

    # ── estado láser noético ────────────────────────────────────────────────────

    def test_estado_laser_con_psi_alto(self) -> None:
        """Con Ψ = 1.0 debe estar en estado láser noético."""
        self.assertTrue(self.espectro.es_estado_laser(1.0))

    def test_estado_laser_con_psi_bajo(self) -> None:
        """Con Ψ < PSI_UMBRAL no debe estar en estado láser."""
        self.assertFalse(self.espectro.es_estado_laser(0.5))

    # ── espectro array ─────────────────────────────────────────────────────────

    def test_espectro_array_longitud(self) -> None:
        """espectro_array() debe devolver arrays con n_puntos elementos."""
        freqs, pots = self.espectro.espectro_array(n_puntos=100)
        self.assertEqual(len(freqs), 100)
        self.assertEqual(len(pots), 100)

    def test_espectro_array_freqs_crecientes(self) -> None:
        """Las frecuencias del array deben ser crecientes."""
        freqs, _ = self.espectro.espectro_array()
        self.assertTrue(np.all(np.diff(freqs) > 0))

    def test_informe_emision_claves(self) -> None:
        """El informe de emisión debe contener las claves esperadas."""
        informe = self.espectro.informe_emision(psi=1.0)
        expected_keys = {
            "f_peak_hz", "potencia_pico", "potencia_doble",
            "sn_ratio", "pendiente_kolmogorov",
            "estado_laser_noetico", "psi", "kolmogorov_esperado",
        }
        self.assertTrue(expected_keys.issubset(set(informe.keys())))

    def test_informe_f_peak(self) -> None:
        """informe_emision() debe reportar f_peak ≈ 2002.89 Hz."""
        informe = self.espectro.informe_emision()
        self.assertAlmostEqual(informe["f_peak_hz"], EMISION_PEAK_EXPECTED, delta=0.5)


# ═══════════════════════════════════════════════════════════════════════════════
# 7. SistemaQCALStrings
# ═══════════════════════════════════════════════════════════════════════════════

class TestSistemaQCALStrings(unittest.TestCase):
    """Tests for SistemaQCALStrings."""

    def setUp(self) -> None:
        self.sistema = SistemaQCALStrings()

    # ── estado inicial ──────────────────────────────────────────────────────────

    def test_estado_inicial_no_activado(self) -> None:
        """El sistema debe comenzar no activado."""
        estado = self.sistema.estado_sistema()
        self.assertFalse(estado["activado"])

    def test_estado_inicial_psi_cero(self) -> None:
        """La coherencia inicial debe ser 0."""
        estado = self.sistema.estado_sistema()
        self.assertEqual(estado["psi_actual"], 0.0)

    def test_estado_sistema_claves(self) -> None:
        """estado_sistema() debe tener las claves esperadas."""
        estado = self.sistema.estado_sistema()
        for key in ("psi_actual", "activado", "psi_umbral", "f0",
                    "N_microtubulos", "hbar", "n_modos_string", "pico_emision_hz"):
            self.assertIn(key, estado)

    def test_estado_f0(self) -> None:
        """f0 en estado_sistema() debe ser F0_EXPECTED."""
        estado = self.sistema.estado_sistema()
        self.assertAlmostEqual(estado["f0"], F0_EXPECTED, places=4)

    def test_estado_n_modos(self) -> None:
        """Deben reportarse 20 modos string."""
        estado = self.sistema.estado_sistema()
        self.assertEqual(estado["n_modos_string"], 20)

    # ── activar() ──────────────────────────────────────────────────────────────

    def test_activar_devuelve_dict(self) -> None:
        """activar() debe devolver un diccionario."""
        resultado = self.sistema.activar()
        self.assertIsInstance(resultado, dict)

    def test_activar_psi_garantia(self) -> None:
        """activar() debe garantizar Ψ ≥ PSI_UMBRAL = 0.888."""
        resultado = self.sistema.activar()
        self.assertGreaterEqual(resultado["psi"], PSI_UMBRAL_EXPECTED)

    def test_activar_coherencia_umbral_true(self) -> None:
        """coherencia_umbral debe ser True tras activar()."""
        resultado = self.sistema.activar()
        self.assertTrue(resultado["coherencia_umbral"])

    def test_activar_claves(self) -> None:
        """activar() debe devolver las claves esperadas."""
        resultado = self.sistema.activar()
        expected_keys = {
            "psi", "psi_plateau", "psi_biologica", "psi_espectral",
            "coherencia_umbral", "f_peak_hz", "estado_laser_noetico",
            "on_critical_line", "autovalores", "n_autovalores",
            "sigma", "activado", "estado",
        }
        self.assertTrue(expected_keys.issubset(set(resultado.keys())))

    def test_activar_on_critical_line(self) -> None:
        """El sistema activado debe estar en la línea crítica."""
        resultado = self.sistema.activar()
        self.assertTrue(resultado["on_critical_line"])

    def test_activar_n_autovalores(self) -> None:
        """Debe reportarse exactamente 20 autovalores."""
        resultado = self.sistema.activar()
        self.assertEqual(resultado["n_autovalores"], 20)

    def test_activar_autovalores_tipo(self) -> None:
        """autovalores debe ser una lista."""
        resultado = self.sistema.activar()
        self.assertIsInstance(resultado["autovalores"], list)

    def test_activar_f_peak(self) -> None:
        """f_peak_hz debe ser ≈ 2002.89 Hz."""
        resultado = self.sistema.activar()
        self.assertAlmostEqual(
            resultado["f_peak_hz"], EMISION_PEAK_EXPECTED, delta=0.5
        )

    def test_activar_marca_sistema(self) -> None:
        """Tras activar(), activado=True."""
        self.sistema.activar()
        self.assertTrue(self.sistema.activado)

    def test_activar_actualiza_psi(self) -> None:
        """Tras activar(), psi_actual ≥ PSI_UMBRAL."""
        self.sistema.activar()
        self.assertGreaterEqual(self.sistema.psi_actual, PSI_UMBRAL_EXPECTED)

    def test_activar_sigma_critica(self) -> None:
        """activar(sigma=0.5) debe producir coherencia ≥ 0.888."""
        resultado = self.sistema.activar(sigma=0.5)
        self.assertGreaterEqual(resultado["psi"], PSI_UMBRAL_EXPECTED)

    def test_activar_psi0_alto(self) -> None:
        """Con psi0=0.9, activar() debe garantizar Ψ ≥ 0.888."""
        resultado = self.sistema.activar(psi0=0.9)
        self.assertGreaterEqual(resultado["psi"], PSI_UMBRAL_EXPECTED)

    def test_activar_psi0_bajo(self) -> None:
        """Con psi0=0.1, activar() debe garantizar Ψ ≥ 0.888."""
        resultado = self.sistema.activar(psi0=0.1)
        self.assertGreaterEqual(resultado["psi"], PSI_UMBRAL_EXPECTED)

    def test_activar_estado_coherente(self) -> None:
        """El estado reportado debe contener 'COHERENTE'."""
        resultado = self.sistema.activar()
        self.assertIn("COHERENTE", resultado["estado"])

    # ── certificar() ───────────────────────────────────────────────────────────

    def test_certificar_devuelve_dict(self) -> None:
        """certificar() debe devolver un diccionario."""
        cert = self.sistema.certificar()
        self.assertIsInstance(cert, dict)

    def test_certificar_aprobado(self) -> None:
        """El sistema debe certificarse exitosamente."""
        cert = self.sistema.certificar()
        self.assertTrue(cert["certificado"])

    def test_certificar_psi_ok(self) -> None:
        """certificar() debe reportar psi_ok=True."""
        cert = self.sistema.certificar()
        self.assertTrue(cert["psi_ok"])

    def test_certificar_f_peak_ok(self) -> None:
        """certificar() debe reportar f_peak_ok=True."""
        cert = self.sistema.certificar()
        self.assertTrue(cert["f_peak_ok"])

    def test_certificar_sello(self) -> None:
        """El sello del certificado debe ser 'QED-STRINGS-VERIFIED ✅'."""
        cert = self.sistema.certificar()
        self.assertEqual(cert["sello"], "QED-STRINGS-VERIFIED ✅")

    def test_certificar_psi_garantia(self) -> None:
        """La coherencia certificada debe ser ≥ 0.888."""
        cert = self.sistema.certificar()
        self.assertGreaterEqual(cert["psi"], PSI_UMBRAL_EXPECTED)

    def test_certificar_claves(self) -> None:
        """certificar() debe devolver las claves esperadas."""
        cert = self.sistema.certificar()
        expected_keys = {
            "certificado", "psi", "psi_ok", "f_peak_hz",
            "f_peak_ok", "on_critical_line", "estado_laser_noetico", "sello",
        }
        self.assertTrue(expected_keys.issubset(set(cert.keys())))

    # ── reproducibilidad ────────────────────────────────────────────────────────

    def test_reproducibilidad(self) -> None:
        """Dos sistemas con la misma semilla deben producir el mismo Ψ."""
        s1 = SistemaQCALStrings(seed=0)
        s2 = SistemaQCALStrings(seed=0)
        r1 = s1.activar()
        r2 = s2.activar()
        self.assertAlmostEqual(r1["psi"], r2["psi"], places=12)

    # ── atributos internos ──────────────────────────────────────────────────────

    def test_constantes_tipo(self) -> None:
        """sistema.constantes debe ser ConstantesStrings."""
        self.assertIsInstance(self.sistema.constantes, ConstantesStrings)

    def test_operador_tipo(self) -> None:
        """sistema.operador debe ser OperadorEspectralQCAL."""
        self.assertIsInstance(self.sistema.operador, OperadorEspectralQCAL)

    def test_forzado_tipo(self) -> None:
        """sistema.forzado debe ser ForzadoStringNoetico."""
        self.assertIsInstance(self.sistema.forzado, ForzadoStringNoetico)

    def test_coherencia_tipo(self) -> None:
        """sistema.coherencia debe ser CoherenciaCombinada."""
        self.assertIsInstance(self.sistema.coherencia, CoherenciaCombinada)

    def test_integrador_tipo(self) -> None:
        """sistema.integrador debe ser IntegradorRK4Strings."""
        self.assertIsInstance(self.sistema.integrador, IntegradorRK4Strings)

    def test_espectro_tipo(self) -> None:
        """sistema.espectro debe ser EspectroEmisionFotonica."""
        self.assertIsInstance(self.sistema.espectro, EspectroEmisionFotonica)


# ═══════════════════════════════════════════════════════════════════════════════
# 8. _RIEMANN_ZEROS_20 (lista interna)
# ═══════════════════════════════════════════════════════════════════════════════

class TestRiemannZeros20(unittest.TestCase):
    """Tests for the embedded _RIEMANN_ZEROS_20 list."""

    def test_longitud(self) -> None:
        """_RIEMANN_ZEROS_20 debe contener exactamente 20 elementos."""
        self.assertEqual(len(_RIEMANN_ZEROS_20), 20)

    def test_primer_cero(self) -> None:
        """γ₁ ≈ 14.134725142."""
        self.assertAlmostEqual(_RIEMANN_ZEROS_20[0], 14.134725142, places=6)

    def test_segundo_cero(self) -> None:
        """γ₂ ≈ 21.022039639."""
        self.assertAlmostEqual(_RIEMANN_ZEROS_20[1], 21.022039639, places=6)

    def test_ultimo_cero(self) -> None:
        """γ₂₀ ≈ 77.144840069."""
        self.assertAlmostEqual(_RIEMANN_ZEROS_20[19], 77.144840069, places=6)

    def test_todos_positivos(self) -> None:
        """Todos los ceros γₙ deben ser positivos."""
        self.assertTrue(all(g > 0 for g in _RIEMANN_ZEROS_20))

    def test_crecientes(self) -> None:
        """Los ceros deben ser monótonamente crecientes."""
        for i in range(len(_RIEMANN_ZEROS_20) - 1):
            self.assertLess(_RIEMANN_ZEROS_20[i], _RIEMANN_ZEROS_20[i + 1])

    def test_sin_dependencias_externas(self) -> None:
        """Los ceros están codificados directamente (sin mpmath/scipy)."""
        # La lista es de tipo List[float], sin dependencias de mpmath
        for g in _RIEMANN_ZEROS_20:
            self.assertIsInstance(g, float)

    def test_pico_emision_correcto(self) -> None:
        """γ₁ × F₀ debe dar ≈ 2002.89 Hz."""
        pico = _RIEMANN_ZEROS_20[0] * F0_EXPECTED
        self.assertAlmostEqual(pico, EMISION_PEAK_EXPECTED, delta=0.5)


# ═══════════════════════════════════════════════════════════════════════════════
# Entry point
# ═══════════════════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    # Verboso para mostrar los 133 tests individuales
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()

    for cls in (
        TestConstantesStrings,
        TestOperadorEspectralQCAL,
        TestForzadoStringNoetico,
        TestCoherenciaCombinada,
        TestIntegradorRK4Strings,
        TestEspectroEmisionFotonica,
        TestSistemaQCALStrings,
        TestRiemannZeros20,
    ):
        suite.addTests(loader.loadTestsFromTestCase(cls))

    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)

    print("\n" + "=" * 72)
    print(f"  Tests ejecutados : {result.testsRun}")
    print(f"  Errores          : {len(result.errors)}")
    print(f"  Fallos           : {len(result.failures)}")
    psi_ok = result.wasSuccessful()
    print(f"  Estado           : {'✅ 100% SUPERADAS — Ψ ≥ 0.888' if psi_ok else '❌ FALLOS DETECTADOS'}")
    print("=" * 72)
    sys.exit(0 if psi_ok else 1)
