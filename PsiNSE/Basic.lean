import Mathlib.Tactic

/-! # PsiNSE Basic Definitions -/

namespace PsiNSE

/-- Frecuencia fundamental f₀ = 141.7001 Hz -/
def f₀ : ℝ := 141.7001

/-- Frecuencia angular ω₀ = 2πf₀ -/
def ω₀ : ℝ := 2 * Real.pi * f₀

/-- Basic lemma about frequency -/
lemma f₀_positive : f₀ > 0 := by
  unfold f₀
  norm_num

/-- Angular frequency is positive -/
lemma ω₀_positive : ω₀ > 0 := by
  unfold ω₀
  sorry

/-- Relationship between f₀ and ω₀ -/
lemma ω₀_eq_two_pi_f₀ : ω₀ = 2 * Real.pi * f₀ := by
  rfl

end PsiNSE
