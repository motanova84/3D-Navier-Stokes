import Mathlib.Topology.Basic
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
    have hx : Continuous fun x : ℝ³ => xCoord x := continuous_apply 0
    have hy : Continuous fun x : ℝ³ => yCoord x := continuous_apply 1
    have hz : Continuous fun x : ℝ³ => zCoord x := continuous_apply 2
    simpa [Set.setOf_and] using
      (hx.continuousAt.preimage_mem_nhds (Iio L) (by simpa using isOpen_Iio)).inter
        ((hy.continuousAt.preimage_mem_nhds (Iio L) (by simpa using isOpen_Iio)).inter
          (hz.continuousAt.preimage_mem_nhds (Iio L) (by simpa using isOpen_Iio)))

end NavierStokes3D
