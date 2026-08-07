import NavierStokes3D.Core.Definitions

set_option autoImplicit false

namespace NavierStokes3D.Examples

open NavierStokes3D

/-- A simple Poiseuille-style profile in the `z` direction. -/
def poiseuilleFlow (R dpdx ν : ℝ) : VectorField :=
  fun x : ℝ³ =>
    let r2 := (xCoord x)^2 + (yCoord x)^2
    let vz := ((-dpdx) / (4 * ν)) * (R^2 - r2)
    point 0 0 vz

/-- The profile vanishes on the axis when `R = 0`. -/
@[simp] theorem poiseuilleFlow_axis (dpdx ν : ℝ) :
    poiseuilleFlow 0 dpdx ν (point 0 0 0) = point 0 0 0 := by
  simp [poiseuilleFlow, point]

/-- A trivial smooth fluid state used for base compilation. -/
def zeroFluidState (domain : FluidDomain) : FluidState where
  velocity := fun _ => point 0 0 0
  pressure := fun _ => 0
  density := Physics.waterDensity
  kinematicViscosity := Physics.waterKinematicViscosity
  domain := domain
  regularity := by
    constructor <;> simpa using contDiff_const

end NavierStokes3D.Examples
