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

def coherenceEvolution (state : K15NodeState) (dt : ℝ) (coupling : ℝ) : ℝ :=
  let drift := 0.1 * (1 - state.coherence) + (-1e-6) * (state.frequency - f0)^2 + 0.05 * coupling
  min 1 (max psiThreshold (state.coherence + dt * drift))

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
      coherenceNonneg := by
        unfold coherenceEvolution
        refine le_min (by norm_num) ?_
        exact le_trans (le_of_lt ψThreshold_in_range.1) (le_max_left _ _)
      coherenceLeOne := by
        unfold coherenceEvolution
        exact min_le_left _ _
      isActive := state.isActive }
  { nodes := newNodes
    edges := top.edges
    edgeWeight := top.edgeWeight }

def k15Step (dt : ℝ) : K15Topology → K15Topology := fun top => k15Evolution top dt

lemma nodeCoherencePreservation (state : K15NodeState) (dt : ℝ) (coupling : ℝ) :
    coherenceEvolution state dt coupling ≥ psiThreshold := by
  unfold coherenceEvolution
  refine le_min ?_ ?_
  · exact le_of_lt ψThreshold_in_range.2
  · exact le_max_left _ _

lemma k15StableIfNodesStable (top : K15Topology) (dt : ℝ)
    (h_nodes : ∀ node, (top.nodes node).coherence ≥ psiThreshold) :
    let evolved := k15Evolution top dt
    ∀ node, (evolved.nodes node).coherence ≥ psiThreshold := by
  intro evolved node
  simpa [k15Evolution] using
    nodeCoherencePreservation (top.nodes node) dt
      ((∑ neighbor in allNodes,
          if top.edges.contains (node, neighbor) then
            top.edgeWeight (node, neighbor) * (top.nodes neighbor).coherence
          else 0) / 12)

theorem k15CoherencePreservation (top : K15Topology) (dt : ℝ) :
    k15GlobalCoherence (k15Evolution top dt) := by
  unfold k15GlobalCoherence k15Coherence
  have h_nodes : ∀ node, psiThreshold ≤ (k15Evolution top dt).nodes node |>.coherence := by
    intro node
    simpa [k15Evolution] using
      nodeCoherencePreservation (top.nodes node) dt
        ((∑ neighbor in allNodes,
            if top.edges.contains (node, neighbor) then
              top.edgeWeight (node, neighbor) * (top.nodes neighbor).coherence
            else 0) / 12)
  have h_sum : ∑ node in allNodes, psiThreshold ≤
      ∑ node in allNodes, (k15Evolution top dt).nodes node |>.coherence := by
    refine Finset.sum_le_sum ?_
    intro node _
    exact h_nodes node
  have hmul : (Finset.card allNodes : ℝ) * psiThreshold ≤
      ∑ node in allNodes, (k15Evolution top dt).nodes node |>.coherence := by
    simpa [Finset.sum_const, nsmul_eq_mul] using h_sum
  have hcard_pos : (0 : ℝ) < (Finset.card allNodes : ℝ) := by
    norm_num [allNodes_card]
  have hdiv : psiThreshold ≤
      (∑ node in allNodes, (k15Evolution top dt).nodes node |>.coherence) /
      (Finset.card allNodes : ℝ) := by
    exact (le_div_iff hcard_pos).2 (by simpa [mul_comm] using hmul)
  simpa [ge_iff_le] using hdiv

corollary k15CoherencePreservationContinuous (top : K15Topology) (dt : ℝ) (n : ℕ)
    (h_coherence : k15GlobalCoherence top) :
    ∀ m ≤ n, k15GlobalCoherence ((k15Step dt)^[m] top) := by
  intro m h_m
  induction m with
  | zero =>
      simpa [Function.iterate_zero] using h_coherence
  | succ m ih =>
      have hprev : k15GlobalCoherence ((k15Step dt)^[m] top) := ih (Nat.le_of_succ_le h_m)
      have hstep : k15GlobalCoherence (k15Evolution ((k15Step dt)^[m] top) dt) :=
        k15CoherencePreservation ((k15Step dt)^[m] top) dt
      simpa [Function.iterate_succ_apply'] using hstep

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
  let edges := (allNodes.product allNodes).filter (fun p => p.1 ≠ p.2)
  let edgeWeight := fun _ => 0.5
  { nodes := nodes
    edges := edges
    edgeWeight := edgeWeight }

theorem allNodes_card : Finset.card allNodes = 13 := by
  decide

theorem k15InitialCoherence : k15GlobalCoherence k15InitialState := by
  unfold k15GlobalCoherence k15Coherence
  simp [k15InitialState, allNodes, allNodes_card, psiThreshold]

theorem k15PerpetualCoherence (dt : ℝ) (n : ℕ) :
    let top := k15InitialState
    let evolved := (k15Step dt)^[n] top
    k15GlobalCoherence evolved := by
  have h_cont := k15CoherencePreservationContinuous
    (top := k15InitialState) (dt := dt) (n := n) k15InitialCoherence
  simpa using h_cont n (Nat.le_refl n)

end NOESIS.K15
