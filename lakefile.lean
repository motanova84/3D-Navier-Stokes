import Lake
open Lake DSL

package NavierStokesQCAL where
  -- More Lean options
  moreLeanArgs := #[
    "-DautoImplicit=false"
  ]
  moreServerArgs := #[
    "-DautoImplicit=false"
  ]

-- Require the mathematical library
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- Define the main library target
@[default_target]
lean_lib NavierStokes where
  -- Include all Lean files in the NavierStokes directory
  globs := #[.submodules `NavierStokes]
