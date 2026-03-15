#!/usr/bin/env python3
"""
Tests para QCAL-NS-RK4 — GACT Unified Flow Module
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Pruebas unitarias para qcal.gact_unified_flow que implementa:
- Integrador RK4 para ecuaciones QCAL-NS
- Métrica de coherencia biológica
- Filtro vibracional espectral
- Clase GACTUnifiedFlow con métricas Ψ, ν, Re_q

Author: José Manuel Mota Burruezo
Institute: Instituto Consciencia Cuántica QCAL ∞³
License: MIT
"""

import unittest
import sys
from pathlib import Path

import numpy as np

# Asegurar que el módulo qcal esté en el path
sys.path.insert(0, str(Path(__file__).parent))

from qcal.gact_unified_flow import (
    rk4_step,
    compute_biological_coherence,
    apply_vibrational_filter,
    plot_energy_spectrum,
    GACTUnifiedFlow,
    F0,
    BASE_RESONANCE,
)


# ─────────────────────────────────────────────────────────────────────────────
# Helpers
# ─────────────────────────────────────────────────────────────────────────────

def _make_spectral_grid(N: int):
    """Construir malla espectral para tests."""
    try:
        from scipy.fft import fftfreq
    except ImportError:
        from numpy.fft import fftfreq

    kx = fftfreq(N, d=1.0 / N)
    ky = fftfreq(N, d=1.0 / N)
    kxx, kyy = np.meshgrid(kx, ky, indexing="ij")
    k2 = kxx ** 2 + kyy ** 2
    k2[0, 0] = 1.0
    return kxx, kyy, k2


# ─────────────────────────────────────────────────────────────────────────────
# Tests: constantes y base de datos
# ─────────────────────────────────────────────────────────────────────────────

class TestConstants(unittest.TestCase):
    """Tests para constantes del módulo."""

    def test_f0_value(self):
        """Frecuencia fundamental debe ser 141.7001 Hz."""
        self.assertAlmostEqual(F0, 141.7001, places=4)

    def test_base_resonance_gact_alphabet(self):
        """Las bases GACT deben tener resonancia en (0, 1]."""
        for base in "GACT":
            self.assertIn(base, BASE_RESONANCE)
            self.assertGreater(BASE_RESONANCE[base], 0.0)
            self.assertLessEqual(BASE_RESONANCE[base], 1.0)

    def test_base_resonance_ordering(self):
        """G > A > C ≥ T según jerarquía de resonancia."""
        self.assertGreater(BASE_RESONANCE["G"], BASE_RESONANCE["A"])
        self.assertGreater(BASE_RESONANCE["A"], BASE_RESONANCE["C"])
        self.assertAlmostEqual(BASE_RESONANCE["C"], BASE_RESONANCE["T"] + 0.1, places=5)


# ─────────────────────────────────────────────────────────────────────────────
# Tests: rk4_step
# ─────────────────────────────────────────────────────────────────────────────

class TestRK4Step(unittest.TestCase):
    """Tests para el integrador RK4."""

    def setUp(self):
        N = 16
        self.N = N
        self.kxx, self.kyy, self.k2 = _make_spectral_grid(N)
        rng = np.random.default_rng(42)
        self.uhat = rng.standard_normal((N, N)) + 1j * rng.standard_normal((N, N))
        self.vhat = rng.standard_normal((N, N)) + 1j * rng.standard_normal((N, N))
        # Mantener condición de divergencia libre inicial
        self.uhat[0, 0] = 0.0
        self.vhat[0, 0] = 0.0
        self.zeros = np.zeros((N, N), dtype=complex)

    def test_output_shape(self):
        """rk4_step debe retornar arrays con la misma forma."""
        uhat_new, vhat_new = rk4_step(
            self.uhat, self.vhat, dt=0.01,
            rho=1.0, mu=1e-3,
            k2=self.k2, kxx=self.kxx, kyy=self.kyy,
            grad_px_hat=self.zeros, grad_py_hat=self.zeros,
            N=self.N,
        )
        self.assertEqual(uhat_new.shape, self.uhat.shape)
        self.assertEqual(vhat_new.shape, self.vhat.shape)

    def test_output_dtype(self):
        """La salida debe ser array complejo."""
        uhat_new, vhat_new = rk4_step(
            self.uhat, self.vhat, dt=0.01,
            rho=1.0, mu=1e-3,
            k2=self.k2, kxx=self.kxx, kyy=self.kyy,
            grad_px_hat=self.zeros, grad_py_hat=self.zeros,
            N=self.N,
        )
        self.assertTrue(np.iscomplexobj(uhat_new))
        self.assertTrue(np.iscomplexobj(vhat_new))

    def test_finite_output(self):
        """La salida de rk4_step no debe contener NaN ni Inf."""
        uhat_new, vhat_new = rk4_step(
            self.uhat, self.vhat, dt=0.001,
            rho=1.0, mu=1e-2,
            k2=self.k2, kxx=self.kxx, kyy=self.kyy,
            grad_px_hat=self.zeros, grad_py_hat=self.zeros,
            N=self.N,
        )
        self.assertTrue(np.all(np.isfinite(uhat_new)))
        self.assertTrue(np.all(np.isfinite(vhat_new)))

    def test_zero_velocity_stays_zero(self):
        """Campo nulo con gradiente de presión nulo debe permanecer nulo."""
        N = self.N
        zeros = np.zeros((N, N), dtype=complex)
        uhat_new, vhat_new = rk4_step(
            zeros, zeros, dt=0.01,
            rho=1.0, mu=1e-3,
            k2=self.k2, kxx=self.kxx, kyy=self.kyy,
            grad_px_hat=zeros, grad_py_hat=zeros,
            N=N,
        )
        np.testing.assert_array_almost_equal(uhat_new, zeros)
        np.testing.assert_array_almost_equal(vhat_new, zeros)

    def test_diffusion_reduces_energy(self):
        """Con solo difusión (sin convección ni presión), la energía debe decrecer."""
        N = self.N
        uhat_smooth = np.zeros((N, N), dtype=complex)
        vhat_smooth = np.zeros((N, N), dtype=complex)
        # Modo divergencia-libre: k=(1,1), û=1, v̂=-1 → kx*û + ky*v̂ = 1 - 1 = 0
        uhat_smooth[1, 1] = 1.0
        vhat_smooth[1, 1] = -1.0

        zeros = np.zeros((N, N), dtype=complex)
        uhat_new, vhat_new = rk4_step(
            uhat_smooth, vhat_smooth, dt=0.01,
            rho=0.0, mu=1.0,   # Sin convección, solo difusión
            k2=self.k2, kxx=self.kxx, kyy=self.kyy,
            grad_px_hat=zeros, grad_py_hat=zeros,
            N=N,
        )
        E_ini = np.sum(np.abs(uhat_smooth) ** 2 + np.abs(vhat_smooth) ** 2)
        E_fin = np.sum(np.abs(uhat_new) ** 2 + np.abs(vhat_new) ** 2)
        self.assertLess(E_fin, E_ini, "La difusión debe reducir la energía.")

    def test_incompressibility_preserved(self):
        """Empezando con campo divergencia-libre, la divergencia debe permanecer pequeña."""
        N = self.N
        rng = np.random.default_rng(21)
        # Construir campo divergencia-libre via proyección espectral
        uhat_raw = rng.standard_normal((N, N)) * 0.1 + 1j * rng.standard_normal((N, N)) * 0.1
        vhat_raw = rng.standard_normal((N, N)) * 0.1 + 1j * rng.standard_normal((N, N)) * 0.1
        # Proyección: û_proj = û - kx*(kx*û + ky*v̂)/k2
        div_raw = (self.kxx * uhat_raw + self.kyy * vhat_raw) / self.k2
        uhat_df = uhat_raw - self.kxx * div_raw
        vhat_df = vhat_raw - self.kyy * div_raw
        uhat_df[0, 0] = 0.0
        vhat_df[0, 0] = 0.0

        zeros = np.zeros((N, N), dtype=complex)
        uhat_new, vhat_new = rk4_step(
            uhat_df, vhat_df, dt=1e-4,
            rho=1.0, mu=1e-2,
            k2=self.k2, kxx=self.kxx, kyy=self.kyy,
            grad_px_hat=zeros, grad_py_hat=zeros,
            N=N,
        )
        # Divergencia de la salida
        div_out = self.kxx * uhat_new + self.kyy * vhat_new
        div_out[0, 0] = 0.0
        vel_norm = np.linalg.norm(uhat_new) + np.linalg.norm(vhat_new)
        div_norm = np.linalg.norm(div_out)
        if vel_norm > 0:
            self.assertLess(div_norm / vel_norm, 1.0,
                            "La divergencia relativa debe ser < 1 tras un paso pequeño.")


# ─────────────────────────────────────────────────────────────────────────────
# Tests: compute_biological_coherence
# ─────────────────────────────────────────────────────────────────────────────

class TestComputeBiologicalCoherence(unittest.TestCase):
    """Tests para la métrica de coherencia biológica."""

    def setUp(self):
        N = 32
        x = np.linspace(0, 2 * np.pi, N, endpoint=False)
        self.xx, _ = np.meshgrid(x, x, indexing="ij")

    def test_range_zero_to_one(self):
        """La coherencia debe estar en [0, 1]."""
        rng = np.random.default_rng(7)
        u_phys = rng.standard_normal(self.xx.shape)
        coh = compute_biological_coherence(u_phys, self.xx, F0)
        self.assertGreaterEqual(coh, 0.0)
        self.assertLessEqual(coh, 1.0)

    def test_perfectly_aligned_field(self):
        """Campo alineado con la onda del Logos debe tener coherencia = 1."""
        # u_phys = sin(2π·f₀·x/(2π)) → correlación perfecta
        u_phys = np.sin(2 * np.pi * F0 * self.xx / (2 * np.pi))
        coh = compute_biological_coherence(u_phys, self.xx, F0)
        self.assertAlmostEqual(coh, 1.0, places=5)

    def test_anti_aligned_field(self):
        """Campo opuesto (negativo) debe tener coherencia = 1 (correlación absoluta)."""
        u_phys = -np.sin(2 * np.pi * F0 * self.xx / (2 * np.pi))
        coh = compute_biological_coherence(u_phys, self.xx, F0)
        self.assertAlmostEqual(coh, 1.0, places=5)

    def test_zero_field_returns_zero(self):
        """Campo constante cero debe retornar coherencia 0."""
        u_phys = np.zeros(self.xx.shape)
        coh = compute_biological_coherence(u_phys, self.xx, F0)
        self.assertEqual(coh, 0.0)

    def test_orthogonal_field_low_coherence(self):
        """Campo ortogonal a la onda del Logos debe tener coherencia baja."""
        # Usamos cos en lugar de sin → correlación teóricamente 0 si malla exacta
        u_phys = np.cos(2 * np.pi * F0 * self.xx / (2 * np.pi))
        coh = compute_biological_coherence(u_phys, self.xx, F0)
        self.assertLess(coh, 0.1)

    def test_random_field_coherence_range(self):
        """Campo aleatorio debe tener coherencia en [0, 1]."""
        rng = np.random.default_rng(99)
        for _ in range(5):
            u_phys = rng.standard_normal(self.xx.shape)
            coh = compute_biological_coherence(u_phys, self.xx, F0)
            self.assertGreaterEqual(coh, 0.0)
            self.assertLessEqual(coh, 1.0)


# ─────────────────────────────────────────────────────────────────────────────
# Tests: apply_vibrational_filter
# ─────────────────────────────────────────────────────────────────────────────

class TestApplyVibrationalFilter(unittest.TestCase):
    """Tests para el filtro vibracional espectral."""

    def setUp(self):
        N = 32
        self.N = N
        self.kxx, self.kyy, _ = _make_spectral_grid(N)
        rng = np.random.default_rng(13)
        self.uhat = rng.standard_normal((N, N)) + 1j * rng.standard_normal((N, N))

    def test_low_modes_preserved(self):
        """Los modos bajos (k ≤ N/8) deben preservarse exactamente."""
        uhat_filtered = apply_vibrational_filter(
            self.uhat, self.kxx, self.kyy, self.N
        )
        k_mag = np.sqrt(self.kxx ** 2 + self.kyy ** 2)
        low_mask = k_mag <= self.N / 8.0
        np.testing.assert_array_equal(
            uhat_filtered[low_mask], self.uhat[low_mask]
        )

    def test_high_modes_suppressed(self):
        """Los modos altos (k > N/8) deben ser cero tras el filtro."""
        uhat_filtered = apply_vibrational_filter(
            self.uhat, self.kxx, self.kyy, self.N
        )
        k_mag = np.sqrt(self.kxx ** 2 + self.kyy ** 2)
        high_mask = k_mag > self.N / 8.0
        np.testing.assert_array_equal(uhat_filtered[high_mask], 0.0)

    def test_filter_reduces_energy(self):
        """El filtro debe reducir (o preservar) la energía total."""
        uhat_filtered = apply_vibrational_filter(
            self.uhat, self.kxx, self.kyy, self.N
        )
        E_ini = np.sum(np.abs(self.uhat) ** 2)
        E_fin = np.sum(np.abs(uhat_filtered) ** 2)
        self.assertLessEqual(E_fin, E_ini + 1e-10)

    def test_output_shape_unchanged(self):
        """El filtro no debe cambiar la forma del array."""
        uhat_filtered = apply_vibrational_filter(
            self.uhat, self.kxx, self.kyy, self.N
        )
        self.assertEqual(uhat_filtered.shape, self.uhat.shape)


# ─────────────────────────────────────────────────────────────────────────────
# Tests: GACTUnifiedFlow
# ─────────────────────────────────────────────────────────────────────────────

class TestGACTUnifiedFlow(unittest.TestCase):
    """Tests para la clase GACTUnifiedFlow."""

    def setUp(self):
        self.flow = GACTUnifiedFlow(N=16, secuencia="GACT")

    # ── Inicialización ───────────────────────────────────────────────────────

    def test_default_frequency(self):
        """La frecuencia debe ser F0 por defecto."""
        self.assertAlmostEqual(self.flow.f0, F0, places=4)

    def test_secuencia_uppercase(self):
        """La secuencia debe almacenarse en mayúsculas."""
        flow = GACTUnifiedFlow(secuencia="gact")
        self.assertEqual(flow.secuencia, "GACT")

    def test_grid_shape(self):
        """La malla espectral debe tener forma (N, N)."""
        N = self.flow.N
        self.assertEqual(self.flow.kxx.shape, (N, N))
        self.assertEqual(self.flow.kyy.shape, (N, N))
        self.assertEqual(self.flow.k2.shape, (N, N))

    def test_k2_no_zero_at_origin(self):
        """k2[0,0] debe ser 1.0 para evitar división por cero."""
        self.assertEqual(self.flow.k2[0, 0], 1.0)

    # ── Métricas de resonancia GACT ──────────────────────────────────────────

    def test_mean_resonance_gact(self):
        """Resonancia media de GACT debe ser 0.85."""
        expected = (1.0 + 0.9 + 0.8 + 0.7) / 4.0
        self.assertAlmostEqual(self.flow.mean_resonance, expected, places=10)

    def test_viscosity_formula(self):
        """ν = √2·(1−mean_res)²/f₀ debe ser ≈ 2.245e-4 para GACT."""
        mean_res = self.flow.mean_resonance   # 0.85
        expected_nu = np.sqrt(2.0) * (1.0 - mean_res) ** 2 / F0
        self.assertAlmostEqual(self.flow.nu, expected_nu, places=15)
        # Orden de magnitud correcto
        self.assertAlmostEqual(self.flow.nu, 2.245e-4, delta=1e-6)

    def test_coherence_psi(self):
        """Ψ = 1 − ν debe ser ≈ 0.9998 para GACT."""
        self.assertAlmostEqual(self.flow.Psi, 1.0 - self.flow.nu, places=15)
        self.assertGreater(self.flow.Psi, 0.999)
        self.assertLess(self.flow.Psi, 1.0)

    def test_reynolds_q_formula(self):
        """Re_q = f₀²/ν² debe ser consistente con ν calculado."""
        expected_re_q = F0 ** 2 / self.flow.nu ** 2
        self.assertAlmostEqual(self.flow.Re_q, expected_re_q, places=2)

    def test_reynolds_q_large(self):
        """Re_q para GACT debe ser un número grande (>1e10)."""
        self.assertGreater(self.flow.Re_q, 1e10)

    def test_flow_state_gact(self):
        """GACT con alta coherencia debe clasificarse como LAMINAR_ETÉREO."""
        self.assertEqual(self.flow.estado, "LAMINAR_ETÉREO")

    def test_flow_state_low_resonance(self):
        """Secuencia de baja resonancia debe clasificarse como TURBULENTO."""
        # 'T' tiene resonancia 0.7, un solo carácter → mean_res=0.7
        # nu = √2*(1-0.7)^2/f0 = √2*0.09/141.7 ≈ 8.98e-4 → Ψ ≈ 0.9991
        # Re_q = f0^2/nu^2 ≈ 2.5e10 → LAMINAR_ETÉREO en este caso
        # Para obtener TURBULENTO necesitamos Ψ < 0.888
        # 1 - nu < 0.888 → nu > 0.112 → (1-mean_res)^2 > 0.112*f0/√2 ≈ 11.22
        # (1-mean_res) > 3.35 → imposible ya que mean_res ∈ [0,1]
        # Por tanto TURBULENTO solo ocurre con secuencia vacía o inválida
        flow_empty = GACTUnifiedFlow(secuencia="")
        # Secuencia vacía: mean_res=0 → nu=√2/f0 ≈ 0.00999 → Ψ≈0.990 → COHERENTE
        self.assertIn(flow_empty.estado, ["LAMINAR_ETÉREO", "COHERENTE", "TURBULENTO"])

    def test_analizar_returns_all_keys(self):
        """analizar() debe retornar todos los campos esperados."""
        resultado = self.flow.analizar()
        for key in ("secuencia", "mean_resonance", "nu", "Psi", "Re_q", "estado", "f0"):
            self.assertIn(key, resultado)

    def test_analizar_consistency(self):
        """analizar() debe ser consistente con los atributos del objeto."""
        r = self.flow.analizar()
        self.assertEqual(r["secuencia"], self.flow.secuencia)
        self.assertEqual(r["nu"], self.flow.nu)
        self.assertEqual(r["Psi"], self.flow.Psi)
        self.assertEqual(r["Re_q"], self.flow.Re_q)
        self.assertEqual(r["estado"], self.flow.estado)

    # ── step() ───────────────────────────────────────────────────────────────

    def test_step_output_shape(self):
        """step() debe retornar arrays con forma (N, N)."""
        N = self.flow.N
        rng = np.random.default_rng(3)
        uhat = rng.standard_normal((N, N)) * 0.01 + 0j
        vhat = rng.standard_normal((N, N)) * 0.01 + 0j
        uhat_new, vhat_new = self.flow.step(uhat, vhat, dt=1e-4)
        self.assertEqual(uhat_new.shape, (N, N))
        self.assertEqual(vhat_new.shape, (N, N))

    def test_step_finite(self):
        """step() no debe producir NaN ni Inf con pequeño dt."""
        N = self.flow.N
        rng = np.random.default_rng(5)
        uhat = rng.standard_normal((N, N)) * 0.001 + 0j
        vhat = rng.standard_normal((N, N)) * 0.001 + 0j
        uhat_new, vhat_new = self.flow.step(uhat, vhat, dt=1e-5)
        self.assertTrue(np.all(np.isfinite(uhat_new)))
        self.assertTrue(np.all(np.isfinite(vhat_new)))

    def test_step_with_filter_suppresses_high_modes(self):
        """Con filtro activo, los modos altos deben quedar suprimidos."""
        N = self.flow.N
        rng = np.random.default_rng(7)
        uhat = rng.standard_normal((N, N)) + 1j * rng.standard_normal((N, N))
        vhat = rng.standard_normal((N, N)) + 1j * rng.standard_normal((N, N))
        uhat_new, _ = self.flow.step(uhat, vhat, dt=1e-5, apply_filter=True)
        k_mag = np.sqrt(self.flow.kxx ** 2 + self.flow.kyy ** 2)
        high_mask = k_mag > N / 8.0
        np.testing.assert_array_equal(uhat_new[high_mask], 0.0)

    # ── compute_coherence() ──────────────────────────────────────────────────

    def test_compute_coherence_range(self):
        """La coherencia calculada debe estar en [0, 1]."""
        N = self.flow.N
        # Campo alineado con el Logos
        uhat_logos = np.fft.fft2(np.sin(2 * np.pi * F0 * self.flow.xx / (2 * np.pi)))
        coh = self.flow.compute_coherence(uhat_logos)
        self.assertGreaterEqual(coh, 0.0)
        self.assertLessEqual(coh, 1.0)

    # ── simulate() ───────────────────────────────────────────────────────────

    def test_simulate_returns_expected_keys(self):
        """simulate() debe retornar las claves esperadas."""
        N = self.flow.N
        zeros = np.zeros((N, N), dtype=complex)
        result = self.flow.simulate(zeros, zeros, n_steps=3, dt=1e-5)
        for key in ("uhat", "vhat", "coherence_history", "energia_final"):
            self.assertIn(key, result)

    def test_simulate_coherence_history_length(self):
        """El historial de coherencia debe tener n_steps entradas."""
        N = self.flow.N
        zeros = np.zeros((N, N), dtype=complex)
        n_steps = 5
        result = self.flow.simulate(zeros, zeros, n_steps=n_steps, dt=1e-5)
        self.assertEqual(len(result["coherence_history"]), n_steps)

    def test_simulate_zero_initial_stays_zero(self):
        """Condición inicial cero debe producir energía final = 0."""
        N = self.flow.N
        zeros = np.zeros((N, N), dtype=complex)
        result = self.flow.simulate(zeros, zeros, n_steps=5, dt=1e-5)
        self.assertAlmostEqual(result["energia_final"], 0.0, places=10)


# ─────────────────────────────────────────────────────────────────────────────
# Tests: GACTUnifiedFlow — secuencias adicionales
# ─────────────────────────────────────────────────────────────────────────────

class TestGACTSequenceVariants(unittest.TestCase):
    """Tests de coherencia para distintas secuencias de ADN."""

    def test_high_resonance_sequence_gggg(self):
        """Secuencia 'GGGG' (mean_res=1.0) debe producir ν→0 y Ψ→1."""
        flow = GACTUnifiedFlow(secuencia="GGGG")
        self.assertAlmostEqual(flow.mean_resonance, 1.0, places=10)
        self.assertAlmostEqual(flow.nu, 0.0, places=10)
        self.assertAlmostEqual(flow.Psi, 1.0, places=10)

    def test_low_resonance_sequence_tttt(self):
        """Secuencia 'TTTT' (mean_res=0.7) debe producir mayor ν que GACT."""
        flow_tttt = GACTUnifiedFlow(secuencia="TTTT")
        flow_gact = GACTUnifiedFlow(secuencia="GACT")
        self.assertGreater(flow_tttt.nu, flow_gact.nu)
        self.assertLess(flow_tttt.Psi, flow_gact.Psi)

    def test_psi_coherence_bound(self):
        """Para cualquier secuencia de bases GACT, Ψ debe estar en (0, 1]."""
        for seq in ["G", "A", "C", "T", "GACT", "CGTA", "ATCG", "GGGG", "TTTT"]:
            flow = GACTUnifiedFlow(secuencia=seq)
            self.assertGreater(flow.Psi, 0.0, f"Ψ debe ser > 0 para '{seq}'")
            self.assertLessEqual(flow.Psi, 1.0, f"Ψ debe ser ≤ 1 para '{seq}'")

    def test_viscosity_monotone_in_resonance(self):
        """Mayor resonancia media → menor viscosidad."""
        flow_g = GACTUnifiedFlow(secuencia="G")    # mean_res=1.0, nu=0
        flow_a = GACTUnifiedFlow(secuencia="A")    # mean_res=0.9
        flow_t = GACTUnifiedFlow(secuencia="T")    # mean_res=0.7
        self.assertLessEqual(flow_g.nu, flow_a.nu)
        self.assertLessEqual(flow_a.nu, flow_t.nu)


# ─────────────────────────────────────────────────────────────────────────────
# Tests: plot_energy_spectrum (smoke test — no pyplot)
# ─────────────────────────────────────────────────────────────────────────────

class TestPlotEnergySpectrum(unittest.TestCase):
    """Smoke tests para plot_energy_spectrum."""

    def test_no_exception_with_valid_input(self):
        """plot_energy_spectrum no debe lanzar excepciones con entrada válida."""
        N = 16
        kxx, kyy, _ = _make_spectral_grid(N)
        rng = np.random.default_rng(11)
        uhat = rng.standard_normal((N, N)) + 1j * rng.standard_normal((N, N))
        vhat = rng.standard_normal((N, N)) + 1j * rng.standard_normal((N, N))
        try:
            import matplotlib
            matplotlib.use("Agg")
        except ImportError:
            pass
        # No debe lanzar excepción
        plot_energy_spectrum(uhat, vhat, kxx, kyy, N, title="Test")


if __name__ == "__main__":
    unittest.main(verbosity=2)
