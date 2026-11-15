/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntRunChronClock
import InteractingSLE.Spec.Supplement.WalkSideSpec

/-!
# Own-time order for every actually recorded boundary-walk piece

Recover its original launch and actual pre-launch history, not a capped
program. Physical monotonicity places that history and the full piece in
the given complete proper walk. No hChron or history selection is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.WalkIntRunChron

open GW1WalkChain GW1X GW1Bookkeep Exist Exist.Staged Exist.StagedLaw WalkBdry WalkIntOrient

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

/-- Every selected recorded piece has increasing own time in the given
full proper parametrization. Finite endpoints and zero lifetimes allowed. -/
theorem recorded_piece_clock_order {α : ℝ≥0 → ℂ}
    (hα : Supp9B.IsProperCurve α) (hα0 : α 0 = 0)
    (hRange : range α = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ right) D)
    {pre post : List Piece} {pc : Piece}
    (hs : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (boundaryWalkSpec b jumps θ right).2.2.length).1 = pre ++ pc :: post) :
    ∀ (s t : ℝ≥0) (z w : ℂ), (s : ℝ≥0∞) ≤ pc.2.2 → (t : ℝ≥0∞) ≤ pc.2.2 →
      pc.1.tipAt pc.2.1 s z → pc.1.tipAt pc.2.1 t w →
      (s < t ↔ curveTime α z < curveTime α w) := by
  let spec := boundaryWalkSpec b jumps θ right
  obtain ⟨k, hk, θ', hl, _, hpc⟩ := WalkSide.exists_launch_of_pieces_eq spec D spec.2.2.length hs
  have hh := arcHistory_at_launch hP hC hl
  have hp := hP k _ θ' hl hh.endpoint_mem
  have hhist : ArcHistory (α 0) (SB.prefixPhysSet κ b jumps spec D k)
      (stPt (ExplState.run κ b jumps spec D k) : ℂ) := by
    rw [hα0]
    exact hh
  have hOld : SB.prefixPhysSet κ b jumps spec D k ⊆ range α := by
    rw [hRange, ← SB.prefixPhysSet_length]
    exact prefixPhysSet_mono spec D hk.le
  have hTip := (GW1Z.tipSet_subset_prefixPhysSet_succ spec D hl).trans
    (prefixPhysSet_mono spec D (Nat.succ_le_of_lt hk))
  have hTip' := hTip.trans (show SB.prefixPhysSet κ b jumps spec D spec.2.2.length ⊆ range α by
    rw [SB.prefixPhysSet_length, ← hRange])
  rw [hpc]
  exact tipAt_clock_order_of_pieceSimpleAt hα hp hhist hOld hTip'

/-- Membership alone suffices; the recorded list supplies its launch split. -/
theorem recorded_piece_clock_order_of_mem {α : ℝ≥0 → ℂ}
    (hα : Supp9B.IsProperCurve α) (hα0 : α 0 = 0)
    (hRange : range α = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ right) D)
    {pc : Piece} (hpc : pc ∈ (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (boundaryWalkSpec b jumps θ right).2.2.length).1) :
    ∀ (s t : ℝ≥0) (z w : ℂ), (s : ℝ≥0∞) ≤ pc.2.2 → (t : ℝ≥0∞) ≤ pc.2.2 →
      pc.1.tipAt pc.2.1 s z → pc.1.tipAt pc.2.1 t w →
      (s < t ↔ curveTime α z < curveTime α w) := by
  obtain ⟨pre, post, hs⟩ := List.append_of_mem hpc
  exact recorded_piece_clock_order hP hC hα hα0 hRange hs

end InteractingSLE.Theorem14.WalkIntRunChron
