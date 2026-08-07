import NOESIS.K15
import Mathlib.Tactic

namespace NOESIS.K15

def K15_NODES : ℕ := Finset.card allNodes

theorem K15_NODES_eq : K15_NODES = 13 := by
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
