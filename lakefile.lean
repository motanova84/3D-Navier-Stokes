import Lake
open Lake DSL

package «NavierStokes» where
  -- More Lean options
  moreLeanArgs := #[
    "-DautoImplicit=false"
  ]
  moreServerArgs := #[
    "-DautoImplicit=false"
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

require aesop from git
  "https://github.com/JLimperg/aesop" @ "master"

@[default_target] lean_lib NavierStokes

lean_lib QCAL

lean_lib PNP
