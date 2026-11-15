/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntRunChronHistory
import InteractingSLE.Spec.Supplement.WalkIntClosedRetained

/-!
# Chronological histories for completed finite prefixes too

A live prefix uses the proved capped history. At a finite completed stop,
use the actual original state after the launch, whose status cannot be
infinite completion. Both cases retain all original real connectors.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntRunChron

open GW1WalkChain GW1Bookkeep Exist Exist.Staged Exist.StagedLaw
open WalkMean WalkBdry WalkIntFill WalkIntClosed WalkIntChrono

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ} {right : Bool}
  {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

variable
    (hP : ∀ k c θ',
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
        (k + 1)).2.2.2.1 k = some (c, θ') →
      (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k) : ℂ) ∈
        statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k) →
      PieceSimpleAt c (D k).1 (min (instrTime (boundaryWalkSpec b jumps θ right) k) (D k).2)
        (statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k))
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k))
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1))))
    (hC : WalkConnectorClearance (κ := κ) (b := b) (jumps := jumps)
      (boundaryWalkSpec b jumps θ right) D)

include hP hC

/-- Every actual completed-prefix reference has a physical chronological
carrier with exactly its raw set in H and lying in the full walk. -/
theorem exists_closed_history_of_run {α : ℝ≥0 → ℂ} (hα0 : α 0 = 0)
    (hRange : range α = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ right) D)
    (hD : ∀ k, IsRegularDriver (D k))
    (R : ClosedPrefix (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (boundaryWalkSpec b jumps θ right).2.2.length)) :
    ∃ (A : Set ℂ) (q : ℂ), ArcHistory (α 0) A q ∧ A ∩ H = R.raw ∧ A ⊆ range α := by
  rcases R.time_le.lt_or_eq with hlt | heq
  · let Q : WalkPrefix (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
        (boundaryWalkSpec b jumps θ right).2.2.length) :=
      ⟨R.pre, R.post, R.piece, R.time, R.split, hlt, R.model, R.normalized, R.proper, R.filled⟩
    obtain ⟨P⟩ := exists_prefixHistory_of_run hP hC hα0 hRange hD Q
    exact ⟨P.carrier, P.endpoint, P.history, P.raw_eq, P.range_subset⟩
  · let spec := boundaryWalkSpec b jumps θ right
    obtain ⟨k, hk, θ', hl, hpre, hpc⟩ := WalkSide.exists_launch_of_pieces_eq spec D spec.2.2.length R.split
    obtain ⟨_, hlaunch, _⟩ := eq_launch_of_launches spec D hl
    have hfin : R.piece.2.2 ≠ ⊤ := heq ▸ ENNReal.coe_ne_top
    have hstop : min (instrTime spec k) (D k).2 ≠ ⊤ := by
      simpa only [hpc, WalkSide.recPiece] using hfin
    have hnot : stStatus (ExplState.run κ b jumps spec D (k + 1)) ≠ stDone := by
      rw [hlaunch]
      exact status_launch_ne_done _ _ _ _ _ hstop
    have hh : ArcHistory (0 : ℂ) (SB.prefixPhysSet κ b jumps spec D (k + 1))
        (stPt (ExplState.run κ b jumps spec D (k + 1)) : ℂ) := by
      rcases stateRepresented_run hP hC (k + 1) with ⟨hd, _⟩ | ⟨_, hh⟩
      · exact False.elim (hnot hd)
      · exact hh
    have hpieces : (ExplState.run κ b jumps spec D (k + 1)).1 = R.pre ++ [R.piece] := by
      rw [hlaunch, CounterflowRange.pieces_launch, hpre, hpc]
      rfl
    have htime : R.time = R.piece.2.2.toNNReal := by
      rw [← heq, ENNReal.toNNReal_coe]
    have hraw : R.raw = wsetOf (ExplState.run κ b jumps spec D (k + 1)) := by
      change prefixSet R.pre R.piece R.time = _
      rw [htime]
      exact prefixSet_at_stop_eq_wsetOf hpieces hfin
    refine ⟨SB.prefixPhysSet κ b jumps spec D (k + 1),
      (stPt (ExplState.run κ b jumps spec D (k + 1)) : ℂ), ?_, ?_, ?_⟩
    · rw [hα0]
      exact hh
    · change physOf spec (ExplState.run κ b jumps spec D (k + 1)) ∩ H = R.raw
      rw [WalkIntFiber.physOf_inter_H, ← hraw]
    · rw [hRange, ← SB.prefixPhysSet_length]
      exact prefixPhysSet_mono spec D (Nat.succ_le_of_lt hk)

/-- Actual closed-time raw supports are initial segments in the given
proper full-walk parameter, including their finite ordinary endpoint. -/
theorem exists_closed_raw_initial_segment {α : ℝ≥0 → ℂ}
    (hα : Supp9B.IsProperCurve α) (hα0 : α 0 = 0)
    (hRange : range α = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ right) D)
    (hD : ∀ k, IsRegularDriver (D k))
    (R : ClosedPrefix (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (boundaryWalkSpec b jumps θ right).2.2.length)) :
    ∃ a : ℝ≥0, R.raw = (α '' Icc 0 a) ∩ H := by
  obtain ⟨A, q, hhist, hraw, hrange⟩ := exists_closed_history_of_run hP hC hα0 hRange hD R
  obtain ⟨a, hA, _⟩ := WalkIntOrient.arcHistory_endpoint_initial_segment hα hhist hrange
  exact ⟨a, hraw.symm.trans (congrArg (fun B => B ∩ H) hA)⟩

end InteractingSLE.Theorem14.WalkIntRunChron
