/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntRunChronPair

/-!
# Compatible actual PieceData and chronological histories

The same continuous physical extension supplies both PieceData and the
endpoint of the actual pre-launch history. Thus the earlier hChronR and
hChronL interface can be filled without selecting unrelated extensions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.WalkIntRunChron

open GW1WalkChain GW1Bookkeep Exist Exist.Staged Exist.StagedLaw WalkBdry WalkWords

/-- The exact per-piece chronology input of the earlier common-arc
adapter, for actual runs. The old set includes all real connectors. -/
theorem recorded_piece_data_history {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {θ : ℝ} {right : Bool} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hSimple : ∀ k c θ', (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
        (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1Z.IsSimplePiece c (D k).1 (min (instrTime (boundaryWalkSpec b jumps θ right) k) (D k).2)
        (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D k))
    (hTip : WalkTipCoordinates κ b jumps (boundaryWalkSpec b jumps θ right) D)
    (hC : WalkConnectorClearance (κ := κ) (b := b) (jumps := jumps)
      (boundaryWalkSpec b jumps θ right) D)
    {α : ℝ≥0 → ℂ} (hα0 : α 0 = 0)
    (hRange : range α = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ right) D)
    {pc : Piece} (hmem : pc ∈ (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (boundaryWalkSpec b jumps θ right).2.2.length).1) :
    ∃ (A : Set ℂ) (f : ℂ → ℂ) (W : ℝ≥0 → ℝ) (η : ℝ≥0 → ℂ),
      PieceData pc A f W η ∧ ArcHistory (α 0) A (f (η 0)) ∧ A ⊆ range α := by
  let spec := boundaryWalkSpec b jumps θ right
  have hP := fun k c θ' hl hseed => pieceSimpleAt_at_launch spec D hSimple hTip
    (k := k) (c := c) (θ' := θ') hl hseed
  obtain ⟨pre, post, hs⟩ := List.append_of_mem hmem
  obtain ⟨k, hk, θ', hl, _, hpc⟩ :=
    WalkSide.exists_launch_of_pieces_eq spec D spec.2.2.length hs
  have hh := arcHistory_at_launch hP hC hl
  obtain ⟨f, η, C, hf, hCbound, _, hW0, hW, hη, htrans, hinj, hstart, _, hmeet⟩ :=
    hP k _ θ' hl hh.endpoint_mem
  have hreg : ∀ j c θ', (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j = some (c, θ') →
      GW1P.PieceRegular (D j).1 (min (instrTime spec j) (D j).2) := by
    intro j c θ' hj
    obtain ⟨_, η', _, _, _, h0, hW', hη', htr, _, _⟩ := hSimple j c θ' hj
    exact ⟨h0, hW', η', hη', htr⟩
  have hconf : pc.1.IsConformal := by
    rw [hpc]
    exact (GW2aCont.isConformal_runChart (κ := κ) (b := b) (jumps := jumps) spec D k
      (fun j _ c θ' hj => hreg j c θ' hj)).1
  refine ⟨SB.prefixPhysSet κ b jumps spec D k, f, (D k).1, η, ?_, ?_, ?_⟩
  · rw [hpc]
    rw [hpc] at hconf
    refine ⟨hconf, hf, ⟨C, hCbound⟩, hW0, hW, hη, htrans, hinj, ?_, rfl⟩
    intro t ht htS hA
    have htip := CounterflowRange.tendsto_tip_stopped_of_tendsto hη hW hW0 htS
      (hf _ (Sec7.IsGeneratingTrace.mem_Hbar hη
        (hW.mono fun _ hr => mem_ofPred.2 hr.le) hW0 htS))
    have heq : f (η t) = f (η 0) := by
      have : f (η t) ∈ ({f (η 0)} : Set ℂ) := by
        rw [← hmeet]
        exact ⟨⟨t, htS, htip⟩, hA⟩
      exact mem_singleton_iff.1 this
    exact (ne_of_gt ht) (hinj htS (by simp) heq)
  · rw [hstart, hα0]
    exact hh
  · rw [hRange, ← SB.prefixPhysSet_length]
    exact prefixPhysSet_mono spec D hk.le

end InteractingSLE.Theorem14.WalkIntRunChron
