/-
QCAL Frequency Module
Re-exports frequency constants from FrequencyValidation and adds additional parameters
-/

import Mathlib.Data.Real.Basic
import QCAL.FrequencyValidation.F0Derivation

namespace QCAL

-- Import and re-export fundamental frequency constants from FrequencyValidation
open FrequencyValidation

/-- Fundamental frequency f₀ from FrequencyValidation -/
abbrev f₀ := FrequencyValidation.f₀

/-- Angular frequency ω₀ from FrequencyValidation -/
abbrev ω₀ := FrequencyValidation.ω₀

/-- Proof that f₀ is positive -/
theorem f₀_pos : f₀ > 0 := FrequencyValidation.f₀_pos

/-- Proof that ω₀ is positive -/
theorem ω₀_pos : ω₀ > 0 := FrequencyValidation.ω₀_pos

/-- Upper limit angular frequency ω∞ = 2π × 888.0 Hz -/
@[reducible] def ω∞ : ℝ := 2 * Real.pi * 888.0

/-- Proof that ω∞ is positive -/
theorem ω∞_pos : ω∞ > 0 := by
  unfold ω∞
  apply mul_pos
  apply mul_pos
  · norm_num
  · exact Real.pi_pos
  · norm_num

end QCAL
