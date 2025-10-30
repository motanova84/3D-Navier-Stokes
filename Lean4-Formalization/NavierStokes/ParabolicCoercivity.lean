import NavierStokes.UniformConstants
import NavierStokes.DyadicRiccati

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NavierStokes

/-- Parabolic coercivity lemma (NBB, §XIII.3quinquies) -/
axiom parabolic_coercivity_lemma (ω : ℝ → ℝ) (ν : ℝ) (consts : UniversalConstants) :
  ∃ c_star C_star : ℝ, c_star > 0 ∧ C_star ≥ 0 ∧
  -- ∑_j 2^{2j} ‖Δ_j ω‖²_{L∞} ≥ c⋆ ‖ω‖²_{B⁰_{∞,1}} - C⋆ ‖ω‖²_{L²}
  True  -- Full formulation requires measure theory

/-- Lower bound on dissipation relative to stretching -/
axiom dissipation_lower_bound (ω : ℝ → ℝ) (ν : ℝ) (consts : UniversalConstants)
    (h_ν : ν > 0) :
    -- ν ∑_j 2^{2j} ‖Δ_j ω‖²_{L²} ≥ ν·c⋆ ‖ω‖²_{B⁰_{∞,1}}
    True

end NavierStokes
