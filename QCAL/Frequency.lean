/-
QCAL Frequency Module
Re-exports frequency constants from FrequencyValidation and adds additional parameters
-/

import Mathlib.Data.Real.Basic
import QCAL.FrequencyValidation.F0Derivation

namespace QCAL

-- Re-export fundamental frequency constants from FrequencyValidation
export FrequencyValidation (f₀ ω₀ f₀_pos ω₀_pos frequency_validated)

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
