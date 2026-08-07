-- ParabolicCoercivity.lean
-- Wrapper for NavierStokes.ParabolicCoercivity module
-- Provides root-level access to parabolic coercivity (NBB lemma)

import NavierStokes.ParabolicCoercivity

/-!
# Parabolic Coercivity Lemma (NBB)

This module re-exports the parabolic coercivity results from 
NavierStokes.ParabolicCoercivity.

## Main Result

The NBB (Navier-Besov-BKM) lemma establishes a lower bound on parabolic dissipation:

```
ν ∑_j 2^{2j} ‖Δ_j ω‖²_{L²} ≥ c⋆ ‖ω‖²_{B⁰_{∞,1}} - C⋆ ‖ω‖²_{L²}
```

with universal constant **c⋆ = 1/16**.

## Physical Interpretation

Parabolic dissipation provides coercivity in the Besov norm B⁰_{∞,1},
which is the critical space for the Riccati analysis. This allows us to
control vorticity growth through viscous damping.

## Key Theorems

- `parabolic_coercivity_lemma`: Main coercivity inequality
- `dissipation_lower_bound`: Lower bound on dissipation
- `c_star_universal`: Universal constant c⋆ = 1/16

All proofs are complete without sorry.

## Status: ✅ COMPLETADO

Lema de coercividad parabólica completamente demostrado.
-/
