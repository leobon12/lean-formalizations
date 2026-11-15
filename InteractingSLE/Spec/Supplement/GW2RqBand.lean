/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RqAvoid
import InteractingSLE.Spec.Supplement.GW2RqWord

/-!
# The angle regions of every raised stage word are avoided (decision D33)

PROVE-GW2-ROOTX round 8. The bands alone (no pairing) put the two angle regions of a word into `avoidQ κ 0 β`
(**`mem_avoidQ_of_bands`**). Every raised stage word `upW (θa χ) (stageWord W₀ θ n past)` has the bands at SDE's
junctions (`GW2Sdp.sideInv_stageWord`), so its real points `≠ 0` in `(junctionL, junctionR)` are avoided by its
angle-`0` flow lines (**`mem_avoidQ_stageWord`**).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Finset Filter Topology
open scoped NNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW2Rq

open Restart Exist.StagedLaw GW2TipSystem GW2TipSystem.RootH10
open PiecewiseConstantBoundaryData (jumpSet leftLim rightLim)

variable {κ : ℝ} {β : BoundaryWord} {φ0 aL aR : ℝ}

theorem cumR_of_bands (hκ : 0 < κ) (hκ4 : κ < 4) (hs : φ0 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hbR : ∀ z, 0 < z → z < aR → z ∉ β.jumps →
      φ0 + (sleLambda κ - β.fn z) / chiC κ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    {z : ℝ} (hz0 : 0 < z) (hza : z < aR) (hzJ : z ∉ β.jumps) :
    κ / 2 - 2 ≤ Sec4.cumWeightRight κ (β.fn z + 0 * chiC κ) := by
  have hχ := Sec4.chiC_pos hκ hκ4
  rw [zero_mul, add_zero, Sec4.le_cumWeightRight_iff hκ]
  have hb := hbR z hz0 hza hzJ
  have h1 : (sleLambda κ - β.fn z) / chiC κ ≤ Real.pi := by linarith [hb.2, hs.1]
  have h2 := (div_le_iff₀ hχ).1 h1
  linarith

theorem cumL_of_bands (hκ : 0 < κ) (hκ4 : κ < 4) (hs : φ0 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hbL : ∀ z, aL < z → z < 0 → z ∉ β.jumps →
      φ0 - (sleLambda κ + β.fn z) / chiC κ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    {z : ℝ} (hza : aL < z) (hz0 : z < 0) (hzJ : z ∉ β.jumps) :
    κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (β.fn z + 0 * chiC κ) := by
  have hχ := Sec4.chiC_pos hκ hκ4
  rw [zero_mul, add_zero, Sec4.le_cumWeightLeft_iff hκ]
  have hb := hbL z hza hz0 hzJ
  have h1 : (sleLambda κ + β.fn z) / chiC κ ≤ Real.pi := by linarith [hb.1, hs.2]
  have h2 := (div_le_iff₀ hχ).1 h1
  linarith

/-- **The bands alone put the angle regions in the avoided set.** -/
theorem mem_avoidQ_of_bands (hκ : 0 < κ) (hκ4 : κ < 4) (hs : φ0 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hbR : ∀ z, 0 < z → z < aR → z ∉ β.jumps →
      φ0 + (sleLambda κ - β.fn z) / chiC κ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hbL : ∀ z, aL < z → z < 0 → z ∉ β.jumps →
      φ0 - (sleLambda κ + β.fn z) / chiC κ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    {z : ℝ} (hzL : aL < z) (hzR : z < aR) (hz0 : z ≠ 0) : (z : ℂ) ∈ avoidQ κ 0 β := by
  have hb := β.isPiecewiseConstantBoundaryData
  refine ⟨by simp, ?_⟩
  simp only [Complex.ofReal_re]
  rcases lt_or_gt_of_ne hz0 with hneg | hpos
  · right
    refine ⟨hneg, ?_⟩
    by_cases hzJ : z ∈ β.jumps
    · right
      refine ⟨hzJ, ?_⟩
      obtain ⟨lo, hlo, hc⟩ := GW2Rd.exists_Ioo_eq_leftLim hb z
      obtain ⟨y, hy1, hy2, hyJ⟩ := Sec4.exists_mem_Ioo_not_mem β.jumps (show max lo aL < z from max_lt hlo hzL)
      rw [← hc y ⟨(le_max_left _ _).trans_lt hy1, hy2⟩]
      have := cumL_of_bands hκ hκ4 hs hbL ((le_max_right _ _).trans_lt hy1) (hy2.trans hneg) hyJ
      linarith
    · exact Or.inl ⟨hzJ, cumL_of_bands hκ hκ4 hs hbL hzL hneg hzJ⟩
  · left
    refine ⟨hpos, ?_⟩
    by_cases hzJ : z ∈ β.jumps
    · right
      refine ⟨hzJ, ?_⟩
      obtain ⟨hi, hhi, hc⟩ := GW2Rd.exists_Ioo_eq_rightLim hb z
      obtain ⟨y, hy1, hy2, hyJ⟩ := Sec4.exists_mem_Ioo_not_mem β.jumps (show z < min hi aR from lt_min hhi hzR)
      rw [← hc y ⟨hy1, hy2.trans_le (min_le_left _ _)⟩]
      have := cumR_of_bands hκ hκ4 hs hbR (hpos.trans hy1) (hy2.trans_le (min_le_right _ _)) hyJ
      linarith
    · exact Or.inl ⟨hzJ, cumR_of_bands hκ hκ4 hs hbR hpos hzR hzJ⟩

/-- **The angle regions of a raised stage word are avoided** by its angle-`0` flow lines. -/
theorem mem_avoidQ_stageWord (hκ : 0 < κ) (hκ4 : κ < 4) {S : Type*} (W₀ : S → BoundaryWord) (θ : ℕ → ℝ)
    (hθ : ∀ j, θ j ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (n : ℕ) (x : GW2JDetR5.Past S n) {θa : ℝ}
    (hθa : θa ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) {z : ℝ} (hzL : GW2Sdp.junctionL n x < z)
    (hzR : z < GW2Sdp.junctionR n x) (hz0 : z ≠ 0) :
    (z : ℂ) ∈ avoidQ κ 0 (GW2Rd.upW (θa * chiC κ) (GW2JDetR5.stageWord (κ := κ) W₀ θ n x)) := by
  have hχ := Sec4.chiC_pos hκ hκ4
  have hS := GW2Sdp.sideInv_stageWord hκ W₀ θ hθ n x
  refine mem_avoidQ_of_bands hκ hκ4 hθa (fun z hz0 hza hzJ => ?_) (fun z hza hz0 hzJ => ?_) hzL hzR hz0
  · obtain ⟨α, hα, he⟩ := hS.oldR z hz0 hza hzJ
    rw [GW2Rd.upW_fn]
    simp only
    rw [← he]
    have e : θa + (sleLambda κ - (sleLambda κ - α * chiC κ + θa * chiC κ)) / chiC κ = α := by
      field_simp; ring
    rw [e]; exact hα
  · obtain ⟨α, hα, he⟩ := hS.oldL z hza hz0 hzJ
    rw [GW2Rd.upW_fn]
    simp only
    rw [← he]
    have e : θa - (sleLambda κ + (-sleLambda κ - α * chiC κ + θa * chiC κ)) / chiC κ = α := by
      field_simp; ring
    rw [e]; exact hα

end InteractingSLE.Theorem14.GW2Rq
