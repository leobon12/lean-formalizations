/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11GatePrefix
import InteractingSLE.Spec.Supplement.GB11GateBoundary
import InteractingSLE.Spec.Supplement.GW4FixPhysGeom
import InteractingSLE.Spec.Sec7.R5WallOuterGeom

/-! # GW4: visited wall neighborhoods in the physical counterflow chart -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW4Fix

open GW4Traverse GW4Reg GB11Chart GB11Conn WangWu

/-- The global GB11 wall cut gives the R.5 visited-neighborhood property
after physical inversion. The finite cut endpoint and zero are excluded;
all other visited points, including original-real contacts, are covered. -/
theorem exists_ball_inverted_wall_subset_trace {γ α : ℝ≥0 → ℂ} (hγ : Continuous γ)
    (hα : GB11.IsCompleteSimpleFlow α) {t : ℝ≥0} {cut : ℝ≥0∞}
    (hcut : ∀ r : ℝ≥0, r ∈ wallHitParameters γ α t ↔ cut ≤ (r : ℝ≥0∞))
    {p : ℂ} (hp : p ∈ γ '' Icc 0 t) (hp0 : p ≠ 0)
    (hpCut : p ≠ negInv (α cut.toNNReal)) :
    ∃ ε > 0, (negInv '' range α) ∩ ball p ε ⊆ γ '' Icc 0 t := by
  have hcutp : ∀ r : ℝ≥0, α r = negInv p → cut ≤ (r : ℝ≥0∞) := by
    intro r hr
    obtain ⟨u, hu, he⟩ := hp
    apply (hcut r).1
    refine ⟨u, hu, ?_⟩
    rw [hr, he]
    change -p⁻¹ * p = -1
    rw [neg_mul, inv_mul_cancel₀ hp0]
  induction cut using ENNReal.recTopCoe with
  | top =>
    have hpOut : negInv p ∉ range α := by
      rintro ⟨r, hr⟩
      exact (not_le.2 ENNReal.coe_lt_top) (hcutp r hr)
    have hnear := (WangWu.continuousAt_negInv hp0).eventually
      ((isClosed_range_of_isCompleteSimpleFlow hα).isOpen_compl.mem_nhds hpOut)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hnear
    refine ⟨ε, hε, ?_⟩
    rintro _ ⟨⟨_, ⟨r, rfl⟩, rfl⟩, hz⟩
    exact (hball hz ⟨r, negInv_negInv _ |>.symm⟩).elim
  | coe a =>
    have hpOut : negInv p ∉ α '' Icc 0 a := by
      rintro ⟨r, hr, he⟩
      have hra : r = a := le_antisymm hr.2 (ENNReal.coe_le_coe.1 (hcutp r he))
      subst r
      apply hpCut
      simp only [ENNReal.toNNReal_coe]
      rw [he, negInv_negInv]
    have hClosed : IsClosed (α '' Icc 0 a) := (isCompact_Icc.image hα.1).isClosed
    have hnear := (WangWu.continuousAt_negInv hp0).eventually (hClosed.isOpen_compl.mem_nhds hpOut)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hnear
    refine ⟨ε, hε, ?_⟩
    rintro _ ⟨⟨_, ⟨r, rfl⟩, rfl⟩, hz⟩
    have har : a < r := by
      by_contra h
      exact hball hz ⟨r, ⟨zero_le, not_lt.1 h⟩, (negInv_negInv _).symm⟩
    have hHit := (mem_wallHitParameters_iff hγ).1 ((hcut r).2 (ENNReal.coe_le_coe.2 har.le))
    exact negInv_mem_image_of_firstVisit_le hγ (hHit.trans_lt ENNReal.coe_lt_top) hHit

/-- A finite set of wall-cut points suffices to control the entire
component frontier in the ambient chart near any already visited point. -/
theorem Frame.exists_ball_frontier_relDom_subset_trace {F : Frame} (hF : F.IsOk)
    {w : ℝ≥0 → ℝ} (hw : F.IsPathOk w) {t : ℝ≥0} {cutR cutL : ℝ≥0∞}
    (hR : ∀ r : ℝ≥0, r ∈ wallHitParameters (trc w) F.αR t ↔ cutR ≤ (r : ℝ≥0∞))
    (hL : ∀ r : ℝ≥0, r ∈ wallHitParameters (trc w) F.αL t ↔ cutL ≤ (r : ℝ≥0∞))
    {p : ℂ} (hp : p ∈ trc w '' Icc 0 t) (hp0 : p ≠ 0)
    (hpR : p ≠ negInv (F.αR cutR.toNNReal)) (hpL : p ≠ negInv (F.αL cutL.toNNReal)) :
    ∃ ε > 0, frontier (relDom F.C) ∩ ball p ε ∩ H ⊆ trc w '' Icc 0 t := by
  obtain ⟨rR, hrR, hballR⟩ := exists_ball_inverted_wall_subset_trace (Frame.continuous_trc hw)
    hw.2.2.2.2.1 hR hp hp0 hpR
  obtain ⟨rL, hrL, hballL⟩ := exists_ball_inverted_wall_subset_trace (Frame.continuous_trc hw)
    hw.2.2.2.2.2.1 hL hp hp0 hpL
  refine ⟨min rR rL, lt_min hrR hrL, ?_⟩
  rintro z ⟨⟨hzF, hzBall⟩, hzH⟩
  have hz0 : z ≠ 0 := ne_zero_of_mem_H hzH
  have hzFC := negInv_mem_frontier_of_mem_frontier_relDom (Frame.isOpen_C hF hw)
    (subset_H_of_mem_betweenComponents hF.2.1) hzF hz0
  rcases hF.2.2.1.frontier_subset hzFC with ⟨r, _, he⟩ | ⟨r, _, he⟩
  · apply hballR
    exact ⟨⟨F.αR r, ⟨r, rfl⟩, by rw [he]; exact negInv_negInv z⟩,
      ball_subset_ball (min_le_left _ _) hzBall⟩
  · apply hballL
    exact ⟨⟨F.αL r, ⟨r, rfl⟩, by rw [he]; exact negInv_negInv z⟩,
      ball_subset_ball (min_le_right _ _) hzBall⟩

end InteractingSLE.Theorem14.GW4Fix
