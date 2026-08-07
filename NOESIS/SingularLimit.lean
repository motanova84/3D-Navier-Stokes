-- ============================================================================
-- NOESIS/SingularLimit.lean
-- Formalización honesta del límite singular ε → 0 para una familia regularizada.
--
-- Este archivo NO demuestra regularidad global de Navier–Stokes.
-- Formaliza únicamente consecuencias que sí se siguen de hipótesis explícitas:
--   1. continuidad de la familia afín A_ε = A + ε R,
--   2. continuidad de la energía en límites fuertes,
--   3. preservación de funcionales continuos de coherencia,
--   4. herencia de cotas cerradas cuando el límite fuerte está dado.
-- ============================================================================

import NOESIS.Coherence
import Mathlib.Analysis.NormedSpace.OperatorNorm
import Mathlib.Topology.Algebra.Module.Basic

namespace NOESIS.SingularLimit

open Filter Topology

section OperatorFamilies

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Familia afín regularizada `A_ε = A + ε • R` en un espacio normado real. -/
structure RegularizedFamily where
  A : ContinuousLinearMap ℝ X X
  R : ContinuousLinearMap ℝ X X

/-- Operador regularizado evaluado en `ε`. -/
def RegularizedFamily.op (F : RegularizedFamily) (eps : ℝ) : ContinuousLinearMap ℝ X X :=
  F.A + eps • F.R

@[simp] theorem RegularizedFamily.op_zero (F : RegularizedFamily) :
    F.op 0 = F.A := by
  simp [RegularizedFamily.op]

@[simp] theorem RegularizedFamily.op_sub_base (F : RegularizedFamily) (eps : ℝ) :
    F.op eps - F.A = eps • F.R := by
  simp [RegularizedFamily.op]

/-- Para cada vector fijo, el término regularizante desaparece cuando `ε → 0`. -/
theorem regularizing_term_vanishes
    (F : RegularizedFamily) (x : X) :
    Tendsto (fun eps : ℝ => eps • (F.R x)) (𝓝 0) (𝓝 (0 : X)) := by
  simpa using (continuous_id.smul continuous_const).tendsto 0

/-- Para cada vector fijo, `A_ε x → A x` cuando `ε → 0`. -/
theorem op_apply_tendsto_base
    (F : RegularizedFamily) (x : X) :
    Tendsto (fun eps : ℝ => F.op eps x) (𝓝 0) (𝓝 (F.A x)) := by
  have hreg : Tendsto (fun eps : ℝ => eps • (F.R x)) (𝓝 0) (𝓝 (0 : X)) :=
    regularizing_term_vanishes F x
  have hconst : Tendsto (fun _ : ℝ => F.A x) (𝓝 0) (𝓝 (F.A x)) := tendsto_const_nhds
  simpa [RegularizedFamily.op, add_comm, add_left_comm, add_assoc] using hconst.add hreg

/-- La familia `ε ↦ A_ε x` es continua para cada `x` fijo. -/
theorem continuous_op_apply
    (F : RegularizedFamily) (x : X) :
    Continuous (fun eps : ℝ => F.op eps x) := by
  simpa [RegularizedFamily.op] using continuous_const.add (continuous_id.smul continuous_const)

end OperatorFamilies

section EnergyAndCoherence

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Energía cuadrática abstracta asociada a la norma del espacio de estados. -/
noncomputable def energy (u : X) : ℝ := ‖u‖ ^ 2

@[simp] theorem energy_nonneg (u : X) : 0 ≤ energy u := by
  unfold energy
  positivity

/-- La energía es continua respecto a la topología fuerte inducida por la norma. -/
theorem continuous_energy : Continuous (energy (X := X)) := by
  unfold energy
  simpa [pow_two] using (continuous_norm.mul continuous_norm)

/-- Hipótesis abstracta: una trayectoria regularizada converge fuertemente a un límite. -/
def StrongLimit (u : ℝ → X) (u0 : X) : Prop :=
  Tendsto u (𝓝 0) (𝓝 u0)

/-- Si `u_ε → u` fuertemente, entonces la energía converge. -/
theorem energy_tendsto_of_strongLimit
    {u : ℝ → X} {u0 : X}
    (h : StrongLimit u u0) :
    Tendsto (fun eps => energy (u eps)) (𝓝 0) (𝓝 (energy u0)) := by
  exact continuous_energy.continuousAt.tendsto.comp h

/-- Si `u_ε → u` fuertemente, entonces `‖u_ε - u‖ → 0`. -/
theorem norm_difference_tendsto_zero
    {u : ℝ → X} {u0 : X}
    (h : StrongLimit u u0) :
    Tendsto (fun eps => ‖u eps - u0‖) (𝓝 0) (𝓝 (0 : ℝ)) := by
  simpa using (continuous_norm.continuousAt.tendsto.comp (h.sub tendsto_const_nhds))

/-- Un funcional continuo de coherencia se preserva a lo largo de un límite fuerte. -/
theorem coherence_tendsto_of_strongLimit
    {u : ℝ → X} {u0 : X} {Psi : X → ℝ}
    (h : StrongLimit u u0)
    (hPsi : Continuous Psi) :
    Tendsto (fun eps => Psi (u eps)) (𝓝 0) (𝓝 (Psi u0)) := by
  exact hPsi.continuousAt.tendsto.comp h

/-- Si la coherencia es eventualmente constante a lo largo de la familia regularizada,
    entonces el límite fuerte hereda exactamente el mismo valor. -/
theorem coherence_limit_of_eventually_constant
    {u : ℝ → X} {u0 : X} {Psi : X → ℝ} {c : ℝ}
    (h : StrongLimit u u0)
    (hPsi : Continuous Psi)
    (hconst : ∀ᶠ eps in 𝓝 0, Psi (u eps) = c) :
    Psi u0 = c := by
  have h1 : Tendsto (fun eps => Psi (u eps)) (𝓝 0) (𝓝 (Psi u0)) :=
    coherence_tendsto_of_strongLimit h hPsi
  have h2 : Tendsto (fun eps => Psi (u eps)) (𝓝 0) (𝓝 c) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    exact hconst
  exact tendsto_nhds_unique h1 h2

/-- Si la coherencia es exactamente constante para todo `ε`, el límite también la preserva. -/
theorem coherence_limit_of_constant
    {u : ℝ → X} {u0 : X} {Psi : X → ℝ} {c : ℝ}
    (h : StrongLimit u u0)
    (hPsi : Continuous Psi)
    (hconst : ∀ eps, Psi (u eps) = c) :
    Psi u0 = c := by
  apply coherence_limit_of_eventually_constant h hPsi
  exact Filter.Eventually.of_forall hconst

/-- Herencia de una cota cerrada: si `‖u_ε‖ ≤ M` eventualmente y `u_ε → u`
    fuertemente, entonces `‖u‖ ≤ M`. -/
theorem norm_bound_closed_under_strongLimit
    {u : ℝ → X} {u0 : X} {M : ℝ}
    (h : StrongLimit u u0)
    (hbound : ∀ᶠ eps in 𝓝 0, ‖u eps‖ ≤ M) :
    ‖u0‖ ≤ M := by
  have hnorm : Tendsto (fun eps => ‖u eps‖) (𝓝 0) (𝓝 ‖u0‖) :=
    continuous_norm.continuousAt.tendsto.comp h
  have hmem : ∀ᶠ eps in 𝓝 0, ‖u eps‖ ∈ Set.Iic M := hbound
  have hclosed : IsClosed (Set.Iic M) := isClosed_Iic
  exact hclosed.mem_of_tendsto hnorm hmem

/-- Paquete explícito de hipótesis suficiente para hablar del límite singular
    sin sobre-afirmar resultados de regularidad global. -/
structure SingularLimitHypotheses where
  u : ℝ → X
  limit : X
  Psi : X → ℝ
  strongLimit : StrongLimit u limit
  PsiContinuous : Continuous Psi

/-- Con las hipótesis abstractas anteriores, la energía del límite es continua. -/
theorem energy_continuity
    (H : SingularLimitHypotheses (X := X)) :
    Tendsto (fun eps => energy (H.u eps)) (𝓝 0) (𝓝 (energy H.limit)) :=
  energy_tendsto_of_strongLimit H.strongLimit

/-- Con las hipótesis abstractas anteriores, la coherencia converge al valor límite. -/
theorem coherence_continuity
    (H : SingularLimitHypotheses (X := X)) :
    Tendsto (fun eps => H.Psi (H.u eps)) (𝓝 0) (𝓝 (H.Psi H.limit)) :=
  coherence_tendsto_of_strongLimit H.strongLimit H.PsiContinuous

/-- Versión exacta de preservación de coherencia bajo constancia de la familia. -/
theorem coherence_preservation
    (H : SingularLimitHypotheses (X := X)) {c : ℝ}
    (hconst : ∀ eps, H.Psi (H.u eps) = c) :
    H.Psi H.limit = c :=
  coherence_limit_of_constant H.strongLimit H.PsiContinuous hconst

end EnergyAndCoherence

end NOESIS.SingularLimit
