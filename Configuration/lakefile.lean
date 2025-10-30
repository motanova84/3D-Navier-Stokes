import Lake
open Lake DSL

package NavierStokes {
  -- Clay Millennium Navier-Stokes formalization
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib NavierStokes {
  -- Lean library for Navier-Stokes formalization
  roots := #[`NavierStokes]
}
