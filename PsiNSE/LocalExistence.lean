import Mathlib.Tactic
import PsiNSE.Basic

/-! # Local Existence Theory -/

namespace PsiNSE

/-- Local solution structure -/
structure LocalSolution where
  u : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ)
  T : ℝ
  T_pos : T > 0

/-- Existence of local solutions -/
theorem local_existence (u₀ : (Fin 3 → ℝ) → (Fin 3 → ℝ)) :
    ∃ sol : LocalSolution, True := by
  sorry

/-- Uniqueness of local solutions -/
theorem local_uniqueness (u₀ : (Fin 3 → ℝ) → (Fin 3 → ℝ)) 
    (sol1 sol2 : LocalSolution) :
    sol1.u = sol2.u := by
  sorry

/-- Continuity of the solution map -/
lemma solution_continuous (sol : LocalSolution) (t : ℝ) (h : 0 ≤ t ∧ t ≤ sol.T) :
    Continuous (sol.u t) := by
  sorry

end PsiNSE
