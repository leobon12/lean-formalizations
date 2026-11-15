/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntRunChronRun
import InteractingSLE.Spec.Supplement.GW1WalkChainPiece

/-!
# Actual launch histories and their inclusion in the complete walk

A recorded launch cannot follow a completed state. The exported stage
invariant therefore gives its actual old chronological history. Existing
physical-set monotonicity puts the entire history in the final walk.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.WalkIntRunChron

open GW1WalkChain GW1X GW1Bookkeep Exist Exist.Staged Exist.StagedLaw

/-- A launch record rules out a previously completed state. -/
theorem not_done_of_launch {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ} {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ')) :
    stStatus (ExplState.run κ b jumps spec D k) ≠ stDone := by
  intro hd
  have hins := (eq_launch_of_launches spec D hl).1
  have hsame : ExplState.run κ b jumps spec D (k + 1) = ExplState.run κ b jumps spec D k := by
    rw [run_succ, hins]
    exact isTerminal_flowStep (Or.inl hd) k (D k) θ' (instrTime spec k)
  have hnone := launches_run_of_le (κ := κ) (b := b) (jumps := jumps) spec D (le_refl k)
  rw [hsame, hnone] at hl
  cases hl

/-- All actual physical history sets are monotone in instruction time. -/
theorem prefixPhysSet_mono {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    Monotone (SB.prefixPhysSet κ b jumps spec D) :=
  monotone_nat_of_le_succ (GW1Z.prefixPhysSet_subset_succ spec D)

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

/-- The history immediately before a recorded launch is an actual
ArcHistory, including all earlier real connectors. -/
theorem arcHistory_at_launch {k : ℕ} {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (k + 1)).2.2.2.1 k = some (c, θ')) :
    ArcHistory (0 : ℂ) (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D k)
      (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k) : ℂ) := by
  rcases stateRepresented_run hP hC k with ⟨hd, _⟩ | ⟨_, hh⟩
  · exact False.elim (not_done_of_launch _ D hl hd)
  · exact hh

end InteractingSLE.Theorem14.WalkIntRunChron
