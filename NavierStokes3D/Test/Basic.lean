import NavierStokes3D

set_option autoImplicit false

namespace NavierStokes3D.Test

open NavierStokes3D

def testPoint : ℝ³ := point 1 2 3

def testAdd : ℝ³ := testPoint + point 4 5 6

def testNorm : ℝ := norm testPoint

def testDot : ℝ := dot testPoint (point 1 0 0)

def testCross : ℝ³ := cross (point 1 0 0) (point 0 1 0)

def constScalar : ScalarField := fun _ => 0

def constVector : VectorField := fun _ => point 1 1 1

noncomputable def testGradient : VectorField := gradient constScalar

noncomputable def testDivergence : ScalarField := divergence constVector

def validQuantumState : QuantumState where
  coherence := Physics.coherenceThreshold
  vonNeumannEntropy := 0.01
  stabilityCount := 100
  coherenceNonneg := by norm_num [Physics.coherenceThreshold]
  coherenceLeOne := by norm_num [Physics.coherenceThreshold]
  entropyNonneg := by norm_num

theorem testEmissionRegime : isInEmissionRegime validQuantumState := by
  exact ⟨by norm_num [Physics.coherenceThreshold], by norm_num⟩

end NavierStokes3D.Test
