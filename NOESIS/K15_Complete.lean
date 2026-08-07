import NOESIS.K15
import Mathlib.Tactic

namespace NOESIS.K15

noncomputable def alpha : ℝ := 0.1
noncomputable def beta : ℝ := -1e-6
noncomputable def gamma : ℝ := 0.05
noncomputable def maxFreqDev : ℝ := 1.417001e-4

def K15_NODES : ℕ := 13

theorem alpha_value : alpha = 0.1 := rfl
theorem beta_value : beta = -1e-6 := rfl
theorem gamma_value : gamma = 0.05 := rfl
theorem maxFreqDev_value : maxFreqDev = 1.417001e-4 := rfl

theorem K15_NODES_card : Finset.card allNodes = K15_NODES := by
  simpa [K15_NODES] using allNodes_card

lemma nodeCoherencePreservation_complete (state : K15NodeState) (dt : ℝ) (coupling : ℝ) :
    coherenceEvolution state dt coupling ≥ psiThreshold :=
  nodeCoherencePreservation state dt coupling

theorem k15CoherencePreservation_complete (top : K15Topology) (dt : ℝ) :
    k15GlobalCoherence (k15Evolution top dt) :=
  k15CoherencePreservation top dt

theorem k15InitialCoherence_complete : k15GlobalCoherence k15InitialState :=
  k15InitialCoherence

theorem k15PerpetualCoherence_complete (dt : ℝ) (n : ℕ) :
    let top := k15InitialState
    let evolved := (k15Step dt)^[n] top
    k15GlobalCoherence evolved := by
  simpa using k15PerpetualCoherence dt n

end NOESIS.K15
