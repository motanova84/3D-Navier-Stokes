import Lake
open Lake DSL

package PsiNSE where
  -- Lean 4 package for Ψ-NSE formal verification
  moreServerArgs := #[
    "-DautoImplicit=false"
  ]
  moreLeanArgs := #[
    "-DautoImplicit=false"
  ]

-- Mathlib dependency (core mathematical library)
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

-- P-NP framework integration
require PNP from git "https://github.com/motanova84/P-NP" @ "main"

-- QCAL (noesis88) quantum-classical coupling framework
require QCAL from git "https://github.com/motanova84/noesis88" @ "main"

@[default_target]
lean_lib PsiNSE where
  globs := #[.andSubmodules `PsiNSE]
