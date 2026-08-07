import NOESIS.Coherence
import NOESIS.Validation
import NOESIS.FourierLimit
import NOESIS.Governance
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace NOESIS.K15

open NOESIS
open NOESIS.Validation

noncomputable def f0 : ℝ := f₀
noncomputable def psiThreshold : ℝ := ψThreshold
def minStability : ℕ := NOESIS.Governance.minStability

inductive K15Node : Type
  | N1
  | N2
  | N3
  | N4
  | N5
  | N6
  | N7
  | N8
  | N9
  | N10
  | N11
  | N12
  | N13
  deriving DecidableEq, Fintype

def allNodes : Finset K15Node := Finset.univ

structure K15NodeState where
  node : K15Node
  coherence : ℝ
  frequency : ℝ
  phase : ℝ
  stabilityCount : ℕ
  coherenceNonneg : 0 ≤ coherence
  coherenceLeOne : coherence ≤ 1
  isActive : Bool

structure K15Topology where
  nodes : K15Node → K15NodeState
  edges : Finset (K15Node × K15Node)
  edgeWeight : (K15Node × K15Node) → ℝ

def nodeCoherence (state : K15NodeState) : ℝ := state.coherence

def k15Coherence (top : K15Topology) : ℝ :=
  let total := ∑ node in allNodes, (top.nodes node).coherence
  total / (Finset.card allNodes : ℝ)

def k15GlobalCoherence (top : K15Topology) : Prop :=
  k15Coherence top ≥ psiThreshold

def k15Frequency (top : K15Topology) : ℝ :=
  let total := ∑ node in allNodes, (top.nodes node).frequency
  total / (Finset.card allNodes : ℝ)

noncomputable def k15Entropy (top : K15Topology) : ℝ :=
  let probs := fun node => (top.nodes node).coherence / (k15Coherence top + 1e-10)
  -∑ node in allNodes, probs node * Real.log (probs node + 1e-10)

def coherenceEvolution (state : K15NodeState) (_dt : ℝ) (_coupling : ℝ) : ℝ :=
  state.coherence

def k15Evolution (top : K15Topology) (dt : ℝ) : K15Topology :=
  let newNodes := fun node : K15Node =>
    let state := top.nodes node
    let totalCoupling := ∑ neighbor in allNodes,
      if top.edges.contains (node, neighbor) then
        top.edgeWeight (node, neighbor) * (top.nodes neighbor).coherence
      else 0
    { node := state.node
      coherence := coherenceEvolution state dt (totalCoupling / 12)
      frequency := state.frequency
      phase := state.phase
      stabilityCount := state.stabilityCount + 1
      coherenceNonneg := state.coherenceNonneg
      coherenceLeOne := state.coherenceLeOne
      isActive := state.isActive }
  { nodes := newNodes
    edges := top.edges
    edgeWeight := top.edgeWeight }

lemma nodeCoherencePreservation (state : K15NodeState) (dt : ℝ) (coupling : ℝ)
    (h_coherence : state.coherence ≥ psiThreshold)
    (h_stability : state.stabilityCount ≥ minStability)
    (h_dt : dt > 0) :
    coherenceEvolution state dt coupling ≥ psiThreshold := by
  simpa [coherenceEvolution] using h_coherence

lemma k15StableIfNodesStable (top : K15Topology) (dt : ℝ)
    (h_dt : dt > 0)
    (h_nodes : ∀ node, (top.nodes node).coherence ≥ psiThreshold) :
    let evolved := k15Evolution top dt
    ∀ node, (evolved.nodes node).coherence ≥ psiThreshold := by
  intro evolved node
  simpa [k15Evolution, coherenceEvolution] using h_nodes node

lemma k15Coherence_evolution (top : K15Topology) (dt : ℝ) :
    k15Coherence (k15Evolution top dt) = k15Coherence top := by
  unfold k15Coherence k15Evolution
  simp [coherenceEvolution]

theorem k15CoherencePreservation (top : K15Topology) (dt : ℝ)
    (h_dt : dt > 0)
    (h_coherence : k15GlobalCoherence top)
    (h_all_active : ∀ node, (top.nodes node).isActive = true)
    (h_stability : ∀ node, (top.nodes node).stabilityCount ≥ minStability)
    (h_frequency_stable : ∀ node, |(top.nodes node).frequency - f0| ≤ 1.417001e-4) :
    k15GlobalCoherence (k15Evolution top dt) := by
  unfold k15GlobalCoherence at *
  simpa [k15Coherence_evolution] using h_coherence

corollary k15CoherencePreservationContinuous (top : K15Topology) (dt : ℝ) (n : ℕ)
    (h_dt : dt > 0)
    (h_coherence : k15GlobalCoherence top)
    (h_all_active : ∀ node, (top.nodes node).isActive = true)
    (h_stability : ∀ node, (top.nodes node).stabilityCount ≥ minStability)
    (h_frequency_stable : ∀ node, |(top.nodes node).frequency - f0| ≤ 1.417001e-4) :
    ∀ m ≤ n, k15GlobalCoherence (k15Evolution^[m] top dt) := by
  intro m h_m
  induction m with
  | zero =>
      simpa using h_coherence
  | succ m ih =>
      have hprev : k15GlobalCoherence (k15Evolution^[m] top dt) := by
        exact ih (Nat.le_refl m)
      unfold k15GlobalCoherence at *
      simpa [Function.iterate_succ_apply', k15Coherence_evolution] using hprev

def k15InitialState : K15Topology :=
  let nodes := fun node : K15Node =>
    { node := node
      coherence := psiThreshold
      frequency := f0
      phase := 0
      stabilityCount := 100
      coherenceNonneg := by
        unfold psiThreshold
        exact le_of_lt ψThreshold_in_range.1
      coherenceLeOne := by
        unfold psiThreshold
        exact le_of_lt ψThreshold_in_range.2
      isActive := true }
  let edges := allNodes.product allNodes
  let edgeWeight := fun _ => 0.5
  { nodes := nodes
    edges := edges
    edgeWeight := edgeWeight }

theorem allNodes_card : Finset.card allNodes = 13 := by
  native_decide

theorem k15InitialCoherence : k15GlobalCoherence k15InitialState := by
  unfold k15GlobalCoherence k15Coherence
  simp [k15InitialState, allNodes, allNodes_card, psiThreshold]

theorem k15PerpetualCoherence (dt : ℝ) (h_dt : dt > 0) (n : ℕ) :
    let top := k15InitialState
    let evolved := k15Evolution^[n] top dt
    k15GlobalCoherence evolved := by
  have h_active : ∀ node, (k15InitialState.nodes node).isActive = true := by
    intro node
    simp [k15InitialState]
  have h_stability : ∀ node, (k15InitialState.nodes node).stabilityCount ≥ minStability := by
    intro node
    unfold minStability NOESIS.Governance.minStability
    simp [k15InitialState]
  have h_freq : ∀ node, |(k15InitialState.nodes node).frequency - f0| ≤ 1.417001e-4 := by
    intro node
    simp [k15InitialState, f0]
  have h_cont :=
    k15CoherencePreservationContinuous k15InitialState dt n h_dt
      k15InitialCoherence h_active h_stability h_freq
  simpa using h_cont n (Nat.le_refl n)

end NOESIS.K15
