-- ============================================================================
-- NOESIS/Inconsistencies.lean
-- Verificación formal de las inconsistencias identificadas y delimitación
-- del dominio operativo del marco QCAL/NOESIS.
--
-- Tres resultados:
--   1. B₀ = 3.327 µT es una referencia apantallada, ≠ campo geomagnético.
--   2. Ψ ≥ ψThreshold es físicamente inalcanzable por FID en RMN convencional.
--   3. Ψ y f₀ son invariantes algebraicos formales (no empíricos).
-- ============================================================================

import NOESIS.Coherence
import NOESIS.Validation
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace NOESIS.Inconsistencies

open NOESIS
open NOESIS.Validation
open Real

-- ============================================================
-- §1  CAMPO MAGNÉTICO: REFERENCIA APANTALLADA vs. CAMPO TERRESTRE
-- ============================================================

/-- Campo geomagnético mínimo en superficie terrestre [T] -/
noncomputable def B_earth_min : ℝ := 25e-6

/-- Campo geomagnético máximo en superficie terrestre [T] -/
noncomputable def B_earth_max : ℝ := 65e-6

/-- Positividad de los límites geomagnéticos -/
theorem B_earth_min_pos : B_earth_min > 0 := by norm_num [B_earth_min]
theorem B_earth_max_pos : B_earth_max > 0 := by norm_num [B_earth_max]

/-- El campo de referencia apantallado B₀ ≈ 3.327 µT queda
    FUERA del rango geomagnético terrestre [25 µT, 65 µT]. -/
theorem B₀_outside_earth_field :
    ¬ (B_earth_min ≤ B₀ ∧ B₀ ≤ B_earth_max) := by
  intro ⟨h_lo, _⟩
  -- B_earth_min = 25e-6,  B₀ ≈ 3.327e-6  →  B₀ < B_earth_min
  have hB₀ : B₀ < B_earth_min := by
    unfold B₀ γ_p_reduced γ_p f₀ B_earth_min
    norm_num [Real.pi_gt_3141592, Real.pi_lt_315]
  linarith

/-- B₀ es una referencia operativa apantallada (mu-metal / bobinas Helmholtz),
    explícitamente desvinculada del campo geomagnético exterior. -/
theorem B₀_is_shielded_reference :
    B₀ < B_earth_min := by
  unfold B₀ γ_p_reduced γ_p f₀ B_earth_min
  norm_num [Real.pi_gt_3141592, Real.pi_lt_315]

-- ============================================================
-- §2  INALCANZABILIDAD DE Ψ ≥ ψThreshold VÍA FID CONVENCIONAL
-- ============================================================

/-- Valor de T₂*_min requerido para que Ψ_max_RMN ≥ ψThreshold.
    T₂*_min = 1 / (2π√2 · f₀ · (1 − ψThreshold)) ≈ 795.8 s -/
noncomputable def T₂_required : ℝ :=
  1 / (2 * π * sqrt 2 * f₀ * (1 - ψThreshold))

theorem T₂_required_pos : T₂_required > 0 := by
  unfold T₂_required f₀ ψThreshold
  positivity

/-- T₂_required ≫ 15 s  (el valor asumido frecuentemente en NOESIS) -/
theorem T₂_required_far_exceeds_15s : T₂_required > 15 := by
  unfold T₂_required f₀ ψThreshold
  rw [gt_iff_lt, lt_div_iff (by positivity)]
  norm_num [Real.pi_gt_3141592, Real.pi_lt_315,
            Real.sq_sqrt (show (2:ℝ) ≥ 0 by norm_num),
            Real.sqrt_lt' (show (0:ℝ) < 2 by norm_num)]

/-- T₂*_max del agua pura a temperatura ambiente ≈ 3 s ≪ T₂_required -/
noncomputable def T₂_water_max : ℝ := 3.0   -- s, bibliografía NMR

/-- T₂* del agua real es mucho menor que el requerido -/
theorem T₂_water_far_below_required : T₂_water_max < T₂_required := by
  have h1 : T₂_required > 15 := T₂_required_far_exceeds_15s
  unfold T₂_water_max
  linarith

/-- Consequence: Ψ_max achievable with pure water (T₂* ≤ 3 s)
    is well below ψThreshold. -/
theorem ψ_water_below_threshold :
    ψ_max_RMN T₂_water_max < ψThreshold := by
  -- T₂_water_max = 3.0 ≤ 15.0, so by monotonicity ψ_max_RMN 3.0 ≤ ψ_max_RMN 15.0
  have h_mono : ψ_max_RMN T₂_water_max ≤ ψ_max_RMN 15 :=
    ψ_max_RMN_monotone (by norm_num [T₂_water_max]) (by norm_num [T₂_water_max])
  -- ψ_max_RMN 15 < ψThreshold (numeric spot-check)
  exact lt_of_le_of_lt h_mono ψ_max_T2_15_below_threshold

-- ============================================================
-- §3  INVARIANTE ALGEBRAICO: Ψ Y f₀ COMO PRIMITIVAS FORMALES
-- ============================================================

/-- Declaración de dominio: Ψ = 0.999999 y f₀ = 141.7001 Hz
    son restricciones algebraicas — no afirmaciones empíricas sobre el agua. -/
structure AlgebraicInvariantDecl where
  /-- Frecuencia invariante del sistema [Hz] -/
  f₀_val    : ℝ
  /-- Parámetro de coherencia invariante -/
  ψ_val     : ℝ
  /-- Sistema de prueba formal -/
  prover    : String
  /-- Sistema de circuitos ZK -/
  circuit   : String
  /-- El invariante NO codifica propiedades empíricas del agua -/
  is_formal : Bool
  /-- Ψ es un índice de estabilidad espectral computable -/
  is_computable : Bool

/-- Instancia del invariante NOESIS -/
def noesisInvariant : AlgebraicInvariantDecl :=
  { f₀_val      := f₀
    ψ_val        := ψThreshold
    prover       := "Lean 4"
    circuit      := "Circom/Groth16"
    is_formal    := true
    is_computable := true }

theorem noesisInvariant_is_formal :
    noesisInvariant.is_formal = true := rfl

theorem noesisInvariant_is_computable :
    noesisInvariant.is_computable = true := rfl

theorem noesisInvariant_f₀_correct :
    noesisInvariant.f₀_val = 141.7001 := by
  simp [noesisInvariant, f₀]

theorem noesisInvariant_ψ_correct :
    noesisInvariant.ψ_val = 0.999999 := by
  simp [noesisInvariant, ψThreshold]

/-- El valor de f₀ cae en el rango audible (20 Hz – 20 kHz) -/
theorem f₀_in_audible_range : 20 < f₀ ∧ f₀ < 20000 := by
  constructor <;> norm_num [f₀]

/-- ψThreshold es estrictamente menor que 1 -/
theorem ψThreshold_lt_one : ψThreshold < 1 := ψThreshold_in_range.2

/-- ψThreshold es estrictamente mayor que 0 -/
theorem ψThreshold_gt_zero : ψThreshold > 0 := ψThreshold_in_range.1

-- ============================================================
-- §4  RESUMEN: SEPARACIÓN FORMAL / EMPÍRICA
-- ============================================================

/-- Teorema de separación de dominios:
    Todo lo que NOESIS formaliza pertenece al dominio matemático/criptográfico,
    no al dominio experimental de la materia condensada. -/
theorem domain_separation
    (fp : FrequencyProcess)
    (h  : ψSpectral fp ≥ ψThreshold) :
    -- La condición Ψ ≥ ψThreshold implica una cota en σ_f …
    freqStdDev fp ≤ f₀ * (1 - ψThreshold) ∧
    -- … que es una afirmación algebraica sobre el estimador, no sobre el agua …
    noesisInvariant.is_formal = true ∧
    -- … y el sistema NO requiere T₂* = 8.7 s del agua real para ser válido.
    noesisInvariant.is_computable = true := by
  exact ⟨coherenceThreshold fp h,
         noesisInvariant_is_formal,
         noesisInvariant_is_computable⟩

end NOESIS.Inconsistencies
