/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7InfinityAccessExterior
import InteractingSLE.WangWu.Prop418Side

/-!
# Real exterior accesses arbitrarily far from the gates

PROVE-R7-GAPEQ. Reuse the Loewner cluster lemma and bounded boundary displacement.
The inverted left exterior adheres to every positive real point, and the right
exterior to every negative one. Their lifts have real accesses outside any interval.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)
open scoped NNReal

namespace InteractingSLE.Sec7.R7InfinityAccess

open Sec6 WangWu Lemma71I PocketJordan

/-- The cluster lemma lifts a physical real exterior access to a real chart
access with the existing uniform boundary displacement bound. -/
theorem exists_real_lift_near {W : ℝ → ℝ} {η : ℝ → ℂ} {s K x : ℝ} {E : Set ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s)
    (hED : E ⊆ H \ fwdHull W s) (hx : (x : ℂ) ∈ closure E)
    (hK : ∀ w ∈ Hbar, ‖trMap W 0 s w - w‖ ≤ K) :
    ∃ y : ℝ, (y : ℂ) ∈ closure (fwdMap W s '' E) ∧ |x - y| ≤ K := by
  have := mem_closure_iff_nhdsWithin_neBot.1 hx
  let U := Ultrafilter.of (𝓝[E] (x : ℂ))
  obtain ⟨y, hyH, hy, hFy⟩ := exists_tendsto_fwdMap_ultrafilter hη hW hW0 hs hED U
    (Ultrafilter.of_le _)
  have hFy' : trMap W 0 s y = x := by
    rw [YuanSimpleApprox.trMap_zero_left hW0]
    exact hFy
  have hyim : y.im = 0 := by
    refine le_antisymm (not_lt.1 fun hpos => ?_) hyH
    have h := (trMap_zero_mem_domain hW hW0 hs hpos).1
    rw [hFy'] at h
    exact not_mem_H_ofReal x h
  have he : y = ((y.re : ℝ) : ℂ) := Complex.ext (by simp only [ofReal_re])
    (by simp only [ofReal_im, hyim])
  have hUS : ∀ᶠ z in (U : Filter ℂ), z ∈ E := Ultrafilter.of_le _ self_mem_nhdsWithin
  have hcl : y ∈ closure (fwdMap W s '' E) :=
    mem_closure_of_tendsto hy (hUS.mono fun z hz => mem_image_of_mem _ hz)
  have hb := hK y hyH
  rw [hFy', he, ← ofReal_sub, norm_real, Real.norm_eq_abs] at hb
  exact ⟨y.re, he ▸ hcl, hb⟩

/-- If an untouched set adheres to either entire real half-line, its lift has a
real access outside every prescribed finite interval. -/
theorem exists_real_lift_outside_interval {W : ℝ → ℝ} {η : ℝ → ℂ} {s : ℝ} {E : Set ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s)
    (hED : E ⊆ H \ fwdHull W s)
    (hreal : (∀ x : ℝ, 0 < x → (x : ℂ) ∈ closure E) ∨
      (∀ x : ℝ, x < 0 → (x : ℂ) ∈ closure E)) (A B : ℝ) :
    ∃ y : ℝ, y ∉ Icc A B ∧ (y : ℂ) ∈ closure (fwdMap W s '' E) := by
  obtain ⟨K, hK⟩ := exists_norm_trMap_zero_sub_le_Hbar hη hW hW0 hs
  rcases hreal with hpos | hneg
  · let x := |K| + |B| + 1
    have hx : 0 < x := by dsimp [x]; linarith only [abs_nonneg K, abs_nonneg B]
    obtain ⟨y, hy, hxy⟩ := exists_real_lift_near hη hW hW0 hs hED (hpos x hx) hK
    have hlarge : B < y := by
      have := (abs_le.1 hxy).2
      dsimp [x] at this
      linarith only [this, le_abs_self K, le_abs_self B]
    exact ⟨y, fun h => (not_le.2 hlarge) h.2, hy⟩
  · let x := -(|K| + |A| + 1)
    have hx : x < 0 := by dsimp [x]; linarith only [abs_nonneg K, abs_nonneg A]
    obtain ⟨y, hy, hxy⟩ := exists_real_lift_near hη hW hW0 hs hED (hneg x hx) hK
    have hsmall : y < A := by
      have := (abs_le.1 hxy).1
      dsimp [x] at this
      linarith only [this, le_abs_self K, neg_abs_le A]
    exact ⟨y, fun h => (not_le.2 hsmall) h.1, hy⟩

/-- The inverted left exterior adheres to every positive real point. -/
theorem positive_real_mem_closure_left_exterior {L : ℝ≥0 → ℂ} (hL : IsSimpleProper L)
    {x : ℝ} (hx : 0 < x) : (x : ℂ) ∈ closure (negInv '' leftSideOf (range L)) := by
  have hx' : -(x⁻¹) < 0 := neg_neg_of_pos (inv_pos.2 hx)
  obtain ⟨r, hr, hsub⟩ := hL.isProperArc.exists_ball_inter_H_subset_leftSideOf hx'
  rw [arcRange_realPath] at hsub
  have hc := closure_mono hsub (ofReal_mem_closure_ball_inter_H (-(x⁻¹)) hr)
  have hm := (WangWu.continuousAt_negInv
    (ofReal_ne_zero.2 (ne_of_lt hx'))).continuousWithinAt.mem_closure_image hc
  simpa only [negInv, ofReal_neg, ofReal_inv, inv_neg, inv_inv, neg_neg] using hm

/-- The inverted right exterior adheres to every negative real point. -/
theorem negative_real_mem_closure_right_exterior {R : ℝ≥0 → ℂ} (hR : IsSimpleProper R)
    {x : ℝ} (hx : x < 0) : (x : ℂ) ∈ closure (negInv '' rightSideOf (range R)) := by
  have hx' : 0 < -(x⁻¹) := neg_pos.2 (inv_lt_zero'.2 hx)
  obtain ⟨r, hr, hsub⟩ := hR.isProperArc.exists_ball_inter_H_subset_rightSideOf hx'
  rw [arcRange_realPath] at hsub
  have hc := closure_mono hsub (ofReal_mem_closure_ball_inter_H (-(x⁻¹)) hr)
  have hm := (WangWu.continuousAt_negInv
    (ofReal_ne_zero.2 (ne_of_gt hx'))).continuousWithinAt.mem_closure_image hc
  simpa only [negInv, ofReal_neg, ofReal_inv, inv_neg, inv_inv, neg_neg] using hm

end InteractingSLE.Sec7.R7InfinityAccess
