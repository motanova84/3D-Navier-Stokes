import Lake
open Lake DSL

package NavierStokes {
  -- Clay Millennium Navier-Stokes formalization
}
package NavierStokesQCAL where
  moreServerArgs := #[
    "-DautoImplicit=false"
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib NavierStokes {
  -- Lean library for Navier-Stokes formalization
  roots := #[`NavierStokes]
}
lean_lib NavierStokes where
  globs := #[.submodules `NavierStokes]
