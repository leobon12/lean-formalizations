/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntBoundCutData

/-!
# Raw recorded prefixes cut at a full-walk parameter

The selected own-time prefix contains exactly the portion of its piece
before the full-walk cutoff. Every earlier piece precedes the seed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntBoundCut

open WalkBdry WalkWords WalkIntOrient

/-- A recorded driver's finite prefix uses the same continuous physical
extension, including its finite endpoint. -/
theorem tipSet_prefix_eq_image {pc : Piece} {A : Set ℂ} {f : ℂ → ℂ}
    {W : ℝ≥0 → ℝ} {η : ℝ≥0 → ℂ} (d : PieceData pc A f W η)
    {τ : ℝ≥0} (hτ : (τ : ℝ≥0∞) ≤ pc.2.2) :
    pc.1.tipSet pc.2.1 τ = (fun t => f (η t)) '' Icc 0 τ := by
  ext z
  constructor
  · rintro ⟨t, ht, hz⟩
    exact ⟨t, ⟨zero_le, ENNReal.coe_le_coe.1 ht⟩,
      Chart.tipAt_unique (d.tipAt (ht.trans hτ)) hz⟩
  · rintro ⟨t, ht, rfl⟩
    have htτ : (t : ℝ≥0∞) ≤ (τ : ℝ≥0∞) := ENNReal.coe_le_coe.2 ht.2
    exact ⟨t, htτ, d.tipAt (htτ.trans hτ)⟩

/-- Cut the selected piece at the full-walk cutoff. The resulting actual
raw prefix stays before the cutoff and contains every such point of pc. -/
theorem exists_raw_piece_cut {α : ℝ≥0 → ℂ} (hα : Supp9B.IsProperCurve α)
    {pre : List Piece} {pc : Piece} {A : Set ℂ} {f : ℂ → ℂ}
    {W : ℝ≥0 → ℝ} {η : ℝ≥0 → ℂ} (d : PieceData pc A f W η)
    (hrange : pc.1.tipSet pc.2.1 pc.2.2 ⊆ range α)
    (hmono : StrictMonoOn (fun t => curveTime α (f (η t)))
      {t : ℝ≥0 | (t : ℝ≥0∞) ≤ pc.2.2})
    (hpre : ∀ z ∈ (⋃ p ∈ pre, p.1.tipSet p.2.1 p.2.2),
      z ∈ range α ∧ curveTime α z ≤ curveTime α (f (η 0)))
    {a : ℝ≥0} (hstart : curveTime α (f (η 0)) ≤ a) :
    ∃ τ : ℝ≥0, (τ : ℝ≥0∞) ≤ pc.2.2 ∧
      prefixSet pre pc τ ⊆ (α '' Icc 0 a) ∩ H ∧
      pc.1.tipSet pc.2.1 pc.2.2 ∩ ((α '' Icc 0 a) ∩ H) ⊆ prefixSet pre pc τ := by
  obtain ⟨τ, hτ, hcut⟩ := exists_piece_clock_cut hα d hrange hmono hstart
  refine ⟨τ, hτ, ?_, ?_⟩
  · rintro z ⟨hz, hzH⟩
    refine ⟨?_, hzH⟩
    rcases hz with hz | hz
    · have hzpre := hpre z hz
      exact ⟨curveTime α z, ⟨zero_le, hzpre.2.trans hstart⟩, apply_curveTime hzpre.1⟩
    · rw [tipSet_prefix_eq_image d hτ] at hz
      obtain ⟨t, ht, rfl⟩ := hz
      have htS := (ENNReal.coe_le_coe.2 ht.2).trans hτ
      have hmem : f (η t) ∈ range α := hrange (by rw [d.tipSet_eq]; exact ⟨t, htS, rfl⟩)
      exact ⟨curveTime α (f (η t)), ⟨zero_le, (hcut t htS).2 ht.2⟩, apply_curveTime hmem⟩
  · rintro z ⟨hz, ⟨u, hu, heq⟩, hzH⟩
    rw [d.tipSet_eq] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    change α u = f (η t) at heq
    have hta : curveTime α (f (η t)) ≤ a := by
      rw [← heq, curveTime_apply hα.2.1]
      exact hu.2
    refine ⟨Or.inr ?_, hzH⟩
    rw [tipSet_prefix_eq_image d hτ]
    exact ⟨t, ⟨zero_le, (hcut t ht).1 hta⟩, rfl⟩

end InteractingSLE.Theorem14.WalkIntBoundCut
