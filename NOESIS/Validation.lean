-- ============================================================================
-- NOESIS/Validation.lean
-- Verificación de consistencia: límites físicos y coherencia RMN
-- ============================================================================

import NOESIS.Coherence
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace NOESIS.Validation

open NOESIS
open Real

-- ============================================================
-- §1  RELACIONES LARMOR / CAMPO MAGNÉTICO APANTALLADO
-- ============================================================

/-- Campo magnético de referencia apantallado  B₀  [T]
    derivado de la relación de Larmor:  f₀ = (γ_p / 2π) · B₀ -/
theorem larmor_B₀_derivation :
    B₀ = f₀ / γ_p_reduced := by
  unfold B₀

/-- Verificación numérica: B₀ ≈ 3.327 × 10⁻⁶ T  (3.327 µT) -/
theorem B₀_approx_3327_µT :
    |B₀ - 3.327e-6| < 1e-9 := by
  unfold B₀ γ_p_reduced γ_p f₀
  norm_num [Real.pi_gt_3141592, Real.pi_lt_315]

/-- Lema de consistencia: recalcular f₀ a partir de B₀ reproduce exactamente f₀ -/
theorem larmor_roundtrip :
    γ_p_reduced * B₀ = f₀ := by
  unfold B₀
  field_simp
  exact (div_mul_cancel₀ f₀ (ne_of_gt γ_p_reduced_pos)).symm

-- ============================================================
-- §2  LÍMITE DE FOURIER — SEÑAL LORENTZIANA (FID)
-- ============================================================

/-- Ancho de línea FWHM para señal Lorentziana con decaimiento T₂*
    Δf_FWHM = 1 / (π · T₂*) -/
noncomputable def Δf_FWHM (T₂ : ℝ) : ℝ := 1 / (π * T₂)

theorem Δf_FWHM_pos {T₂ : ℝ} (hT : T₂ > 0) : Δf_FWHM T₂ > 0 := by
  unfold Δf_FWHM
  positivity

/-- Desviación estándar mínima para distribución Lorentziana
    σ_f_min = Δf_FWHM / (2√2) -/
noncomputable def σ_f_min (T₂ : ℝ) : ℝ := Δf_FWHM T₂ / (2 * sqrt 2)

theorem σ_f_min_pos {T₂ : ℝ} (hT : T₂ > 0) : σ_f_min T₂ > 0 := by
  unfold σ_f_min
  apply div_pos (Δf_FWHM_pos hT)
  apply mul_pos
  · norm_num
  · exact Real.sqrt_pos.mpr (by norm_num)

/-- Cota superior de Ψ alcanzable por RMN-FID con decaimiento T₂*
    Ψ_max = max(0, 1 − σ_f_min / f₀) -/
noncomputable def ψ_max_RMN (T₂ : ℝ) : ℝ :=
  max 0 (1 - σ_f_min T₂ / f₀)

theorem ψ_max_RMN_lt_one {T₂ : ℝ} (hT : T₂ > 0) : ψ_max_RMN T₂ < 1 := by
  unfold ψ_max_RMN
  rw [max_lt_iff]
  constructor
  · norm_num
  · have hσ : σ_f_min T₂ / f₀ > 0 :=
      div_pos (σ_f_min_pos hT) f₀_pos
    linarith

-- ============================================================
-- §3  VALORES NUMÉRICOS DEL PROBLEMA (T₂* = 8.7 s y 15 s)
-- ============================================================

/-- T₂* = 8.7 s  →  Δf ≈ 0.03662 Hz -/
theorem Δf_T2_8p7 :
    |Δf_FWHM 8.7 - 0.03662| < 1e-4 := by
  unfold Δf_FWHM
  norm_num [Real.pi_gt_3141592, Real.pi_lt_315]

/-- T₂* = 8.7 s  →  σ_f_min ≈ 0.01296 Hz -/
theorem σ_min_T2_8p7 :
    |σ_f_min 8.7 - 0.01296| < 1e-4 := by
  unfold σ_f_min Δf_FWHM
  norm_num [Real.pi_gt_3141592, Real.pi_lt_315,
            Real.sqrt_two_mul_self, Real.sq_sqrt (show (2:ℝ) ≥ 0 by norm_num)]

/-- T₂* = 8.7 s  →  Ψ_max < ψThreshold = 0.999999 -/
theorem ψ_max_T2_8p7_below_threshold :
    ψ_max_RMN 8.7 < ψThreshold := by
  unfold ψ_max_RMN ψThreshold
  rw [max_lt_iff]
  constructor
  · norm_num
  · unfold σ_f_min Δf_FWHM f₀
    norm_num [Real.pi_gt_3141592, Real.pi_lt_315,
              Real.sq_sqrt (show (2:ℝ) ≥ 0 by norm_num)]

/-- T₂* = 15 s  →  σ_f_min ≈ 0.00751 Hz -/
theorem σ_min_T2_15 :
    |σ_f_min 15 - 0.00751| < 1e-4 := by
  unfold σ_f_min Δf_FWHM
  norm_num [Real.pi_gt_3141592, Real.pi_lt_315,
            Real.sq_sqrt (show (2:ℝ) ≥ 0 by norm_num)]

/-- T₂* = 15 s  →  Ψ_max < ψThreshold = 0.999999 -/
theorem ψ_max_T2_15_below_threshold :
    ψ_max_RMN 15 < ψThreshold := by
  unfold ψ_max_RMN ψThreshold
  rw [max_lt_iff]
  constructor
  · norm_num
  · unfold σ_f_min Δf_FWHM f₀
    norm_num [Real.pi_gt_3141592, Real.pi_lt_315,
              Real.sq_sqrt (show (2:ℝ) ≥ 0 by norm_num)]

-- ============================================================
-- §4  TEOREMAS PRINCIPALES DE VALIDACIÓN
-- ============================================================

/-- Teorema: Para cualquier T₂* finito, Ψ_max(RMN) < 1 -/
theorem ψ_max_RMN_always_below_one {T₂ : ℝ} (hT : T₂ > 0) :
    ψ_max_RMN T₂ < 1 := ψ_max_RMN_lt_one hT

/-- Lema: σ_f_min es monotónicamente decreciente en T₂* -/
lemma σ_f_min_antitone : ∀ {T₂ T₂' : ℝ}, 0 < T₂ → T₂ ≤ T₂' →
    σ_f_min T₂' ≤ σ_f_min T₂ := by
  intro T₂ T₂' hT hle
  unfold σ_f_min Δf_FWHM
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply div_le_div_of_nonneg_left (by positivity) (by positivity) hle

/-- Lema: ψ_max_RMN es monotónicamente creciente en T₂* -/
lemma ψ_max_RMN_monotone : ∀ {T₂ T₂' : ℝ}, 0 < T₂ → T₂ ≤ T₂' →
    ψ_max_RMN T₂ ≤ ψ_max_RMN T₂' := by
  intro T₂ T₂' hT hle
  unfold ψ_max_RMN
  apply max_le_max_left
  apply sub_le_sub_left
  apply div_le_div_of_nonneg_right _ (le_of_lt f₀_pos)
  exact σ_f_min_antitone hT hle

/-- Teorema clave: Ψ ≥ ψThreshold requiere T₂* suficientemente grande.
    Inversión de la cota: T₂* ≥ 1 / (2π√2 · f₀ · (1 − ψThreshold)) -/
theorem T₂_lower_bound_for_threshold {T₂ : ℝ} (hT : T₂ > 0)
    (h : ψ_max_RMN T₂ ≥ ψThreshold) :
    T₂ ≥ 1 / (2 * π * sqrt 2 * f₀ * (1 - ψThreshold)) := by
  -- De ψ_max_RMN T₂ ≥ ψThreshold: max(0, 1 − σ_min/f₀) ≥ ψThreshold
  -- La rama relevante es 1 − σ_min/f₀ ≥ ψThreshold  (ya que ψThreshold > 0)
  have hbranch : 1 - σ_f_min T₂ / f₀ ≥ ψThreshold := by
    unfold ψ_max_RMN at h
    rw [max_ge_iff] at h
    rcases h with h0 | h1
    · exfalso; exact absurd h0 (by linarith [ψThreshold_in_range.1])
    · exact h1
  -- De 1 − σ_min/f₀ ≥ ψThreshold  →  σ_min/f₀ ≤ 1 − ψThreshold
  have hσ_div : σ_f_min T₂ / f₀ ≤ 1 - ψThreshold := by linarith
  -- Multiplicar por f₀ > 0
  have hσ : σ_f_min T₂ ≤ f₀ * (1 - ψThreshold) := by
    rwa [div_le_iff f₀_pos, mul_comm] at hσ_div
  -- Expandir σ_f_min T₂ = 1 / (π · T₂ · 2 · √2)
  have hσ_expand : σ_f_min T₂ = 1 / (π * T₂ * (2 * sqrt 2)) := by
    unfold σ_f_min Δf_FWHM
    field_simp
    ring
  rw [hσ_expand] at hσ
  -- De 1/(π·T₂·2√2) ≤ f₀·(1−ψThreshold), invertir
  have hpos_rhs : f₀ * (1 - ψThreshold) > 0 := by
    apply mul_pos f₀_pos
    linarith [ψThreshold_in_range.2]
  have hpos_denom : π * T₂ * (2 * sqrt 2) > 0 := by positivity
  rw [div_le_iff hpos_denom] at hσ
  -- T₂ ≥ 1 / (π · 2√2 · f₀ · (1−ψThreshold))
  have hT₂ : T₂ ≥ 1 / (π * (2 * sqrt 2) * (f₀ * (1 - ψThreshold))) := by
    rw [ge_iff_le, ← div_le_iff hpos_rhs]
    calc 1 / (π * (2 * sqrt 2) * (f₀ * (1 - ψThreshold)))
        = 1 / (π * (2 * sqrt 2) * f₀ * (1 - ψThreshold)) := by ring_nf
      _ ≤ T₂ := by
          rw [div_le_iff (by positivity)]
          linarith [mul_comm (π * T₂ * (2 * sqrt 2)) (f₀ * (1 - ψThreshold))]
  calc T₂ ≥ 1 / (π * (2 * sqrt 2) * (f₀ * (1 - ψThreshold))) := hT₂
    _ = 1 / (2 * π * sqrt 2 * f₀ * (1 - ψThreshold)) := by ring_nf

end NOESIS.Validation
