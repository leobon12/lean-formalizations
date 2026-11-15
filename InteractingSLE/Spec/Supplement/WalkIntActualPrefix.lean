/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntActualTail

/-!
# Actual terminal infinite pieces supply live recorded prefix collars

The launch bookkeeping and run regularity provide the terminal piece's
proper chart and regular trace. Selecting its finite own-time truncation
then uses the existing WalkPrefix constructor, including its hull model.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntActual

open WalkBdry WalkIntFill Exist.StagedLaw

/-- Regularity and the proper launch chart of a recorded infinite piece
follow from the actual launch record and the regular run. -/
theorem recorded_infinite_piece_facts {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (w : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps w D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime w k) (D k).2))
    {pre post : List Piece} {pc : Piece}
    (hs : (ExplState.run κ b jumps w D w.2.2.length).1 = pre ++ pc :: post)
    (htop : pc.2.2 = ⊤) :
    GW1P.HasProperBdryExt pc.1 ∧ GW1P.PieceRegular pc.2.1 ⊤ := by
  obtain ⟨k, _, θ', hl, _, hpc⟩ := WalkSide.exists_launch_of_pieces_eq
    w D w.2.2.length hs
  have hS : min (instrTime w k) (D k).2 = ⊤ := by
    simpa only [hpc, WalkSide.recPiece] using htop
  have hp := hreg k _ θ' hl
  rw [hS] at hp
  constructor
  · rw [hpc]
    exact (GW1P.isClosed_pieces_run w D hreg k).1
  · simpa only [hpc, WalkSide.recPiece, hS, min_top_right,
      ENNReal.toNNReal_coe] using hp

/-- When the last recorded piece is infinite, a finite prefix contains
the entire ordinary walk in a ball of radius one around any point. -/
theorem exists_prefixSet_collar_of_last_infinite {s : ExplState}
    {pre : List Piece} {pc : Piece} (hs : s.1 = pre ++ [pc]) (htop : pc.2.2 = ⊤)
    (hc : GW1P.HasProperBdryExt pc.1) (hreg : GW1P.PieceRegular pc.2.1 ⊤) (p : ℂ) :
    ∃ τ : ℝ≥0, wsetOf s ∩ ball p 1 ⊆ prefixSet pre pc τ := by
  obtain ⟨τ, hτ⟩ := exists_tipSet_prefix_collar hc hreg p
  refine ⟨τ, ?_⟩
  rintro z ⟨⟨hz, hzH⟩, hzp⟩
  refine ⟨?_, hzH⟩
  obtain ⟨q, hq, hzq⟩ := mem_iUnion₂.1 hz
  rw [hs] at hq
  rcases List.mem_append.1 hq with hq | hq
  · exact Or.inl (mem_iUnion₂.2 ⟨q, hq, hzq⟩)
  · rw [List.mem_singleton] at hq
    subst q
    rw [htop] at hzq
    exact Or.inr (hτ ⟨hzq, hzp⟩)

/-- This collar uses an actual live prefix with the normalized chart and
physical filling supplied by the existing regular-run constructor. -/
theorem exists_walkPrefix_collar_of_last_infinite {κ : ℝ} {b : ℝ → ℝ}
    {jumps : Finset ℝ} (θ : ℝ) (right : Bool) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right)
      D (k + 1)).2.2.2.1 k = some (c, θ') → GW1P.PieceRegular (D k).1
        (min (instrTime (boundaryWalkSpec b jumps θ right) k) (D k).2))
    (hD : ∀ k, Exist.Staged.IsRegularDriver (D k)) {pre : List Piece} {pc : Piece}
    (hs : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (boundaryWalkSpec b jumps θ right).2.2.length).1 = pre ++ [pc])
    (htop : pc.2.2 = ⊤) (p : ℂ) :
    ∃ R : WalkPrefix (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (boundaryWalkSpec b jumps θ right).2.2.length),
      wsetOf (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
        (boundaryWalkSpec b jumps θ right).2.2.length) ∩ ball p 1 ⊆ R.raw := by
  obtain ⟨hc, hp⟩ := recorded_infinite_piece_facts _ D hreg hs htop
  obtain ⟨τ, hτ⟩ := exists_prefixSet_collar_of_last_infinite hs htop hc hp p
  have halive : (τ : ℝ≥0∞) < pc.2.2 := by rw [htop]; exact ENNReal.coe_lt_top
  obtain ⟨R, hpre, _, hpc, htime⟩ := exists_walkPrefix θ right D hreg hD hs halive
  refine ⟨R, ?_⟩
  rw [WalkPrefix.raw, hpre, hpc, htime]
  exact hτ

end InteractingSLE.Theorem14.WalkIntActual
