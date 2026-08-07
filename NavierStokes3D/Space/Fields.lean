import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Algebra.BigOperators.Basic
import NavierStokes3D.Space.Domain

set_option autoImplicit false

open scoped BigOperators

namespace NavierStokes3D

/-- Scalar field on `ℝ³`. -/
abbrev ScalarField := ℝ³ → ℝ

/-- Vector field on `ℝ³`. -/
abbrev VectorField := ℝ³ → ℝ³

/-- Second-order tensor field. -/
abbrev TensorField := ℝ³ → (ℝ³ → ℝ³)

/-- `C²` scalar field. -/
structure SmoothScalarField where
  f : ScalarField
  contDiff : ContDiff ℝ 2 f

/-- `C²` vector field. -/
structure SmoothVectorField where
  v : VectorField
  contDiff : ContDiff ℝ 2 v

/-- Gradient via Fréchet derivative. -/
noncomputable def gradient (f : ScalarField) : VectorField :=
  fun x i => fderiv ℝ f x (basisVec i)

/-- Divergence via the trace of the Jacobian. -/
noncomputable def divergence (v : VectorField) : ScalarField :=
  fun x => ∑ i : Fin 3, (fderiv ℝ v x (basisVec i)) i

/-- Curl in coordinates. -/
noncomputable def curl (v : VectorField) : VectorField :=
  fun x =>
    point
      ((gradient (fun p => zCoord (v p)) x 1) - (gradient (fun p => yCoord (v p)) x 2))
      ((gradient (fun p => xCoord (v p)) x 2) - (gradient (fun p => zCoord (v p)) x 0))
      ((gradient (fun p => yCoord (v p)) x 0) - (gradient (fun p => xCoord (v p)) x 1))

/-- Scalar Laplacian. -/
noncomputable def laplacian (f : ScalarField) : ScalarField :=
  divergence (gradient f)

/-- Vector Laplacian, coordinatewise. -/
noncomputable def vectorLaplacian (v : VectorField) : VectorField :=
  fun x =>
    point
      (laplacian (fun p => xCoord (v p)) x)
      (laplacian (fun p => yCoord (v p)) x)
      (laplacian (fun p => zCoord (v p)) x)

/-- Material derivative `(v · ∇)u`. -/
noncomputable def materialDerivative (v u : VectorField) : VectorField :=
  fun x => fderiv ℝ u x (v x)

end NavierStokes3D
