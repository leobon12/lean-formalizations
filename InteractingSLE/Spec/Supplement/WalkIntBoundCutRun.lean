/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntBoundCutModel

/-!
# Every full-walk raw cutoff has an actual recorded model

The first instruction always records a piece, even at zero lifetime.
Its zero-time prefix is the empty raw set. All other inputs of the finite
cut construction follow from the proved actual-run chronology.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntBoundCut

open WalkBdry WalkWords WalkIntOrient WalkIntClosed WalkIntRunChron GW1WalkChain GW1Bookkeep
open Exist Exist.Staged Exist.StagedLaw
open GW1WalkFinish

/-- The first ordinary launch is recorded even if its lifetime is zero. -/
theorem boundary_run_pieces_ne_nil {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (θ : ℝ) (right : Bool) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (boundaryWalkSpec b jumps θ right).2.2.length).1 ≠ [] := by
  let spec := boundaryWalkSpec b jumps θ right
  let pc := WalkSide.recPiece (ExplState.init 0) (D 0) ⊤
  have hr : ExplState.run κ b jumps spec D 1 =
      ExplState.launch (ExplState.init 0) 0 (D 0) θ ⊤ := by
    rw [show 1 = 0 + 1 from rfl, GW1W.run_succ_walk_flow
      (by rw [boundaryWalk_length]; omega) (by rfl)]
    rfl
  have hmem : pc ∈ (ExplState.run κ b jumps spec D 1).1 := by
    rw [hr, CounterflowRange.pieces_launch]
    exact List.mem_singleton_self _
  have hfull := WalkSide.mem_pieces_run_mono spec D hmem spec.2.2.length
    (by rw [boundaryWalk_length]; omega)
  exact List.ne_nil_of_mem hfull

/-- The raw prefix at the real seed of a first piece is empty. -/
theorem prefixSet_nil_zero_eq_empty {pc : Piece} {A : Set ℂ} {f : ℂ → ℂ}
    {W : ℝ≥0 → ℝ} {η : ℝ≥0 → ℂ} (d : PieceData pc A f W η)
    (hseed : (f (η 0)).im = 0) : prefixSet [] pc 0 = ∅ := by
  rw [prefixSet, tipSet_prefix_eq_image d (by simp)]
  simp only [List.not_mem_nil, iUnion_of_empty, iUnion_empty, empty_union, Icc_self, image_singleton]
  apply Set.disjoint_iff_inter_eq_empty.1
  rw [disjoint_singleton_left]
  intro hz
  change 0 < (f (η 0)).im at hz
  exact (ne_of_gt hz) hseed

/-- Every finite full-walk raw initial segment is one actual recorded
closed prefix. No prefix-selection or chronology hypothesis is retained. -/
theorem exists_actual_closedPrefix_at_parameter {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {θ : ℝ} {right : Bool} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hSimple : ∀ k c θ', (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
        (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1Z.IsSimplePiece c (D k).1 (min (instrTime (boundaryWalkSpec b jumps θ right) k) (D k).2)
        (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D k))
    (hTip : WalkTipCoordinates κ b jumps (boundaryWalkSpec b jumps θ right) D)
    (hC : WalkConnectorClearance (κ := κ) (b := b) (jumps := jumps)
      (boundaryWalkSpec b jumps θ right) D)
    (hD : ∀ k, IsRegularDriver (D k))
    {α : ℝ≥0 → ℂ} (hα : Supp9B.IsProperCurve α) (hα0 : α 0 = 0)
    (hRange : range α = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ right) D)
    (a : ℝ≥0) :
    ∃ R : ClosedPrefix (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (boundaryWalkSpec b jumps θ right).2.2.length), R.raw = (α '' Icc 0 a) ∩ H := by
  let spec := boundaryWalkSpec b jumps θ right
  let s := ExplState.run κ b jumps spec D spec.2.2.length
  have hreg : ∀ k c θ', (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2) := by
    intro k c θ' hl
    obtain ⟨_, η, _, _, _, h0, hW, hη, htr, _, _⟩ := hSimple k c θ' hl
    exact ⟨h0, hW, η, hη, htr⟩
  have hModel (pre post : List Piece) (pc : Piece) (hs : s.1 = pre ++ pc :: post)
      (τ : ℝ≥0) (hτ : (τ : ℝ≥0∞) ≤ pc.2.2) :
      ∃ R : ClosedPrefix s, R.raw = prefixSet pre pc τ := by
    obtain ⟨R, hpre, _, hpc, htime⟩ := exists_closedPrefix θ right D hreg hD hs hτ
    refine ⟨R, ?_⟩
    rw [ClosedPrefix.raw, hpre, hpc, htime]
  have hEmpty : ∃ R : ClosedPrefix s, R.raw = ∅ := by
    cases hlist : s.1 with
    | nil => exact False.elim (boundary_run_pieces_ne_nil θ right D hlist)
    | cons pc post =>
      have hs : s.1 = [] ++ pc :: post := hlist
      obtain ⟨A, f, W, η, d, _, _, hseed, _⟩ :=
        exists_ordered_piece_data hSimple hTip hC hα hα0 hRange hs
      obtain ⟨R, hR⟩ := hModel [] post pc hs 0 (by simp)
      exact ⟨R, hR.trans (prefixSet_nil_zero_eq_empty d hseed)⟩
  apply exists_closedPrefix_at_parameter hα ?_ hEmpty ?_ hModel a
  · rw [hRange]
    exact WalkIntFiber.physOf_inter_H spec s
  · intro pre post pc hs
    obtain ⟨A, f, W, η, d, hrange, hm, _, hpre⟩ :=
      exists_ordered_piece_data hSimple hTip hC hα hα0 hRange hs
    exact ⟨A, f, W, η, d, hrange, hm, hpre⟩

end InteractingSLE.Theorem14.WalkIntBoundCut
