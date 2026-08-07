import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.EuclideanSpace

set_option autoImplicit false

namespace NavierStokes3D

/-- Three-dimensional Euclidean space. -/
abbrev ℝ³ := EuclideanSpace ℝ (Fin 3)

/-- Point in `ℝ³`. -/
abbrev Point := ℝ³

/-- Vector in `ℝ³`. -/
abbrev Vector := ℝ³

/-- Canonical coordinates of a point. -/
def coordinates (x : ℝ³) : Fin 3 → ℝ := x

/-- Constructor from coordinates. -/
def point (x y z : ℝ) : ℝ³ := ![x, y, z]

/-- Standard basis vector. -/
def basisVec (i : Fin 3) : ℝ³ := fun j => if j = i then 1 else 0

/-- X coordinate. -/
def xCoord (p : ℝ³) : ℝ := p 0

/-- Y coordinate. -/
def yCoord (p : ℝ³) : ℝ := p 1

/-- Z coordinate. -/
def zCoord (p : ℝ³) : ℝ := p 2

/-- Euclidean norm. -/
def norm (v : ℝ³) : ℝ := ‖v‖

/-- Euclidean distance. -/
def dist (x y : ℝ³) : ℝ := ‖x - y‖

/-- Inner product. -/
def dot (u v : ℝ³) : ℝ := ⟪u, v⟫_ℝ

/-- Cross product in coordinates. -/
def cross (u v : ℝ³) : ℝ³ :=
  point
    (yCoord u * zCoord v - zCoord u * yCoord v)
    (zCoord u * xCoord v - xCoord u * zCoord v)
    (xCoord u * yCoord v - yCoord u * xCoord v)

end NavierStokes3D
