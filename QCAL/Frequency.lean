/-
QCAL Frequency Module
Defines fundamental frequency constants and related parameters
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace QCAL

/-- Fundamental frequency f₀ = 141.7001 Hz
    Derived from quantum coherence analysis -/
@[reducible] def f₀ : ℝ := 141.7001

/-- Angular frequency ω₀ = 2πf₀ -/
@[reducible] def ω₀ : ℝ := 2 * Real.pi * f₀

/-- Upper limit angular frequency ω∞ = 2π × 888.0 Hz -/
@[reducible] def ω∞ : ℝ := 2 * Real.pi * 888.0

/-- Proof that f₀ is positive -/
theorem f₀_pos : f₀ > 0 := by norm_num [f₀]

/-- Proof that ω₀ is positive -/
theorem ω₀_pos : ω₀ > 0 := by
  unfold ω₀
  apply mul_pos
  apply mul_pos
  · norm_num
  · exact Real.pi_pos
  · exact f₀_pos

/-- Proof that ω∞ is positive -/
theorem ω∞_pos : ω∞ > 0 := by
  unfold ω∞
  apply mul_pos
  apply mul_pos
  · norm_num
  · exact Real.pi_pos
  · norm_num

end QCAL
