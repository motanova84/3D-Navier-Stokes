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
lean_lib PsiNSE where
  globs := #[.submodules `PsiNSE]

lean_lib Millennium
lean_lib GRH
lean_lib BSD
lean_lib PsiNS
