import NOESIS.K15
import Mathlib.Tactic

namespace NOESIS.K15

noncomputable def alpha : ℝ := 0.1
noncomputable def beta : ℝ := -1e-6
noncomputable def gamma : ℝ := 0.05
noncomputable def maxFreqDev : ℝ := 1.417001e-4

def K15_NODES : ℕ := 13

theorem K15_NODES_card : Finset.card allNodes = K15_NODES := by
  simpa [K15_NODES] using allNodes_card

lemma nodeCoherencePreservation_complete (state : K15NodeState) (dt : ℝ) (coupling : ℝ)
    (h_coherence : state.coherence ≥ psiThreshold)
    (h_stability : state.stabilityCount ≥ minStability)
    (h_dt : dt > 0)
    (h_dt_bound : dt ≤ 1)
    (h_coupling : coupling ≥ 0)
    (h_freq : (state.frequency - f0)^2 ≤ 1e-4)
    (h_coherence_le_one : state.coherence ≤ 1) :
    coherenceEvolution state dt coupling ≥ psiThreshold := by
  exact nodeCoherencePreservation state dt coupling h_coherence h_stability h_dt

theorem k15CoherencePreservation_complete (top : K15Topology) (dt : ℝ)
    (h_dt : dt > 0)
    (h_dt_bound : dt ≤ 1)
    (h_coherence : k15GlobalCoherence top)
    (h_all_active : ∀ node, (top.nodes node).isActive = true)
    (h_stability : ∀ node, (top.nodes node).stabilityCount ≥ minStability)
    (h_freq_stable : ∀ node, (top.nodes node).frequency = f0) :
    k15GlobalCoherence (k15Evolution top dt) := by
  have h_freq_bound : ∀ node, |(top.nodes node).frequency - f0| ≤ maxFreqDev := by
    intro node
    rw [h_freq_stable node]
    norm_num [maxFreqDev]
  exact k15CoherencePreservation top dt h_dt h_coherence h_all_active h_stability h_freq_bound

theorem k15InitialCoherence_complete : k15GlobalCoherence k15InitialState :=
  k15InitialCoherence

theorem k15PerpetualCoherence_complete (dt : ℝ) (h_dt : dt > 0) (h_dt_bound : dt ≤ 1) (n : ℕ) :
    let top := k15InitialState
    let evolved := k15Evolution^[n] top dt
    k15GlobalCoherence evolved := by
  simpa using k15PerpetualCoherenceBounded dt h_dt h_dt_bound n

end NOESIS.K15
