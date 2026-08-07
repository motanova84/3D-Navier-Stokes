import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Basic
import NavierStokes3D.Space.Euclidean

set_option autoImplicit false

namespace NavierStokes3D

/-- Basic open fluid domain in `ℝ³`. -/
structure FluidDomain where
  Ω : Set ℝ³
  isOpen_Ω : IsOpen Ω

/-- Boundary of a domain. -/
def FluidDomain.boundary (D : FluidDomain) : Set ℝ³ := frontier D.Ω

/-- Whole-space fluid domain. -/
def fullSpace : FluidDomain where
  Ω := Set.univ
  isOpen_Ω := isOpen_univ

/-- Open ball domain centered at the origin. -/
def ball (R : ℝ) : FluidDomain where
  Ω := Metric.ball (0 : ℝ³) R
  isOpen_Ω := Metric.isOpen_ball

/-- Open cube domain `|x_i| < L`. -/
def cube (L : ℝ) : FluidDomain where
  Ω := {x : ℝ³ | |xCoord x| < L ∧ |yCoord x| < L ∧ |zCoord x| < L}
  isOpen_Ω := by
    have hx : IsOpen {x : ℝ³ | |xCoord x| < L} :=
      isOpen_lt (continuous_abs.comp (continuous_apply 0)) continuous_const
    have hy : IsOpen {x : ℝ³ | |yCoord x| < L} :=
      isOpen_lt (continuous_abs.comp (continuous_apply 1)) continuous_const
    have hz : IsOpen {x : ℝ³ | |zCoord x| < L} :=
      isOpen_lt (continuous_abs.comp (continuous_apply 2)) continuous_const
    simpa [Set.setOf_and] using hx.inter (hy.inter hz)

end NavierStokes3D
