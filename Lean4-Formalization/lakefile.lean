import Lake
open Lake DSL

package NavierStokesQCAL where
  moreServerArgs := #[
    "-DautoImplicit=false"
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib NavierStokes where
  globs := #[.submodules `NavierStokes]

lean_lib PsiNSE where
  globs := #[.submodules `PsiNSE]
