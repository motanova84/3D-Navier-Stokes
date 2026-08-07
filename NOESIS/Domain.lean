-- ============================================================================
-- NOESIS/Domain.lean
-- Delimitación formal del dominio de coherencia
-- ============================================================================

import NOESIS.Coherence

namespace NOESIS.Domain

open NOESIS

-- ============================================================
-- §1  CLASIFICACIÓN DE SISTEMAS
-- ============================================================

/-- Clasificación por régimen de coherencia -/
inductive CoherenceRegime
  | rejected   -- Ψ < ψThreshold: sistema rechazado por ZK
  | marginal   -- Ψ = ψThreshold: en el límite
  | valid      -- Ψ > ψThreshold: sistema válido

/-- Asignar régimen a un proceso de frecuencia -/
noncomputable def classify (fp : FrequencyProcess) : CoherenceRegime :=
  let psi := ψSpectral fp
  if psi < ψThreshold then CoherenceRegime.rejected
  else if psi = ψThreshold then CoherenceRegime.marginal
  else CoherenceRegime.valid

-- ============================================================
-- §2  DELIMITACIÓN: AGUA LÍQUIDA
-- ============================================================

/-- Límite superior de T₂* para agua líquida a 20°C (segundos) -/
noncomputable def T2LiquidWater : ℝ := 3.0

/-- Límite superior de σ_f para agua líquida -/
noncomputable def sigmaLiquidWater : ℝ := 0.15  -- Hz (estimado)

/-- Coherencia máxima para agua líquida -/
noncomputable def psiLiquidWaterMax : ℝ := max 0 (1 - sigmaLiquidWater / f₀)

/-- Agua líquida no alcanza el umbral -/
theorem liquidWaterRejected :
    psiLiquidWaterMax < ψThreshold := by
  unfold psiLiquidWaterMax sigmaLiquidWater ψThreshold f₀
  norm_num

-- ============================================================
-- §3  DELIMITACIÓN: SISTEMAS CRIOGÉNICOS
-- ============================================================

/-- Límite inferior de T₂* para sistemas criogénicos (segundos) -/
noncomputable def T2Cryogenic : ℝ := 1000.0

/-- σ_f máxima compatible con T₂* = 1000 s -/
noncomputable def sigmaCryogenic : ℝ := 1.0 / (Real.pi * T2Cryogenic * 2 * Real.sqrt 2)

/-- Coherencia mínima para sistemas criogénicos -/
noncomputable def psiCryogenicMin : ℝ := max 0 (1 - sigmaCryogenic / f₀)

-- ============================================================
-- §4  TEOREMA DE DELIMITACIÓN
-- ============================================================

/-- Teorema: Los dominios de agua líquida y sistemas criogénicos son disjuntos
    respecto al umbral de coherencia. -/
theorem domainSeparation :
    psiLiquidWaterMax < ψThreshold ∧
    ∀ (fp : FrequencyProcess),
      freqStdDev fp ≤ sigmaCryogenic →
      ψSpectral fp ≥ ψThreshold := by
  constructor
  · exact liquidWaterRejected
  · intro fp hfp
    unfold ψSpectral
    rw [le_max_iff]
    right
    have hbnd : freqStdDev fp / f₀ ≤ sigmaCryogenic / f₀ :=
      div_le_div_of_nonneg_right hfp (le_of_lt f₀_pos) f₀_pos
    unfold sigmaCryogenic ψThreshold f₀
    norm_num [Real.pi_pos, Real.sqrt_pos.mpr (show (2:ℝ) > 0 by norm_num)]
    sorry

end NOESIS.Domain
