/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntBoundCutClock

/-!
# Actual pre-launch supports precede the piece's physical seed

Recover the original instruction and use its chronological physical
history. This also checks that the continuous extension's seed is real.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.WalkIntBoundCut

open WalkBdry WalkWords WalkIntOrient WalkIntRunChron GW1WalkChain GW1Bookkeep
open Exist Exist.Staged Exist.StagedLaw

/-- Recorded-piece data with the full-walk order of every earlier piece.
All extensions agree at the real seed by uniqueness of the physical tip. -/
theorem exists_ordered_piece_data {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {θ : ℝ} {right : Bool} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hSimple : ∀ k c θ', (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
        (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1Z.IsSimplePiece c (D k).1 (min (instrTime (boundaryWalkSpec b jumps θ right) k) (D k).2)
        (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D k))
    (hTip : WalkTipCoordinates κ b jumps (boundaryWalkSpec b jumps θ right) D)
    (hC : WalkConnectorClearance (κ := κ) (b := b) (jumps := jumps)
      (boundaryWalkSpec b jumps θ right) D)
    {α : ℝ≥0 → ℂ} (hα : Supp9B.IsProperCurve α) (hα0 : α 0 = 0)
    (hRange : range α = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ right) D)
    {pre post : List Piece} {pc : Piece}
    (hs : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (boundaryWalkSpec b jumps θ right).2.2.length).1 = pre ++ pc :: post) :
    ∃ (A : Set ℂ) (f : ℂ → ℂ) (W : ℝ≥0 → ℝ) (η : ℝ≥0 → ℂ),
      PieceData pc A f W η ∧
      pc.1.tipSet pc.2.1 pc.2.2 ⊆ range α ∧
      StrictMonoOn (fun t => curveTime α (f (η t))) {t : ℝ≥0 | (t : ℝ≥0∞) ≤ pc.2.2} ∧
      (f (η 0)).im = 0 ∧
      ∀ z ∈ (⋃ p ∈ pre, p.1.tipSet p.2.1 p.2.2),
        z ∈ range α ∧ curveTime α z ≤ curveTime α (f (η 0)) := by
  let spec := boundaryWalkSpec b jumps θ right
  have hP := fun k c θ' hl hseed => pieceSimpleAt_at_launch spec D hSimple hTip
    (k := k) (c := c) (θ' := θ') hl hseed
  have hpcmem : pc ∈ (ExplState.run κ b jumps spec D spec.2.2.length).1 := by
    rw [hs]
    exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨A, f, W, η, d, hhist, hA⟩ :=
    recorded_piece_data_history hSimple hTip hC hα0 hRange hpcmem
  have hpcRange : pc.1.tipSet pc.2.1 pc.2.2 ⊆ range α := by
    intro z hz
    rw [hRange]
    exact Or.inl (Or.inr (mem_iUnion₂.2 ⟨pc, hpcmem, hz⟩))
  obtain ⟨k, hk, θ', hl, hpre, hpc⟩ :=
    WalkSide.exists_launch_of_pieces_eq spec D spec.2.2.length hs
  have hold := arcHistory_at_launch hP hC hl
  have hseed : pc.1.tipAt pc.2.1 0 (stPt (ExplState.run κ b jumps spec D k)) := by
    rw [hpc]
    exact (hTip k _ θ' hl).1
  have hf0 : f (η 0) = (stPt (ExplState.run κ b jumps spec D k) : ℂ) :=
    Chart.tipAt_unique (d.tipAt (by simp)) hseed
  have hOldRange : SB.prefixPhysSet κ b jumps spec D k ⊆ range α := by
    rw [hRange, ← SB.prefixPhysSet_length]
    exact prefixPhysSet_mono spec D hk.le
  have hOldHist : ArcHistory (α 0) (SB.prefixPhysSet κ b jumps spec D k) (f (η 0)) := by
    rw [hf0, hα0]
    exact hold
  obtain ⟨a, ha, hend⟩ := arcHistory_endpoint_initial_segment hα hOldHist hOldRange
  refine ⟨A, f, W, η, d, hpcRange,
    strictMonoOn_piece_curveTime hα d hhist hA hpcRange, ?_, ?_⟩
  · rw [hf0]
    exact Complex.ofReal_im _
  · intro z hz
    have hzOld : z ∈ SB.prefixPhysSet κ b jumps spec D k := by
      apply Or.inl ∘ Or.inr
      rw [hpre]
      exact hz
    refine ⟨hOldRange hzOld, ?_⟩
    rw [ha] at hzOld
    obtain ⟨u, hu, rfl⟩ := hzOld
    rw [hend, curveTime_apply hα.2.1, curveTime_apply hα.2.1]
    exact hu.2

end InteractingSLE.Theorem14.WalkIntBoundCut
