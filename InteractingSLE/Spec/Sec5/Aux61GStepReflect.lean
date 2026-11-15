/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GNextTarget
import InteractingSLE.Spec.Sec5.Aux61TwoSSeedR1

/-! # Reflection of the actual own-to-retained seed transition

Mapping-out boundary properness and the physical inverse boundary extension
supply reflection on the free current collar. The positive boundary derivative
is a consequence of reflection, rather than an extra seed-coordinate input.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Metric Filter Topology
open QuantumZipper (H Hbar fwdHull fwdMapInv)

namespace InteractingSLE.Sec5.Aux61GStep
open Aux61Restart Aux61TwoS

/-- At a real own coordinate whose physical image differs from the target,
the normalized retained chart has imaginary part tending to zero. -/
theorem tendsto_im_transition_zero {W : ℝ → ℝ} {η : ℝ → ℂ} {r : ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) (hη : IsLoewnerTrace W η) (hr : 0 ≤ r)
    {c : Chart} (hc : c.IsConformal) (hsub : (c.dom : Set ℂ) ⊆ H \ fwdHull W r)
    (hB : IsHPHull (stripTargetHull (c.dom : Set ℂ))) {a ξ : ℝ}
    (hscale : EqOn c.1 (fun z => (a : ℂ) *
      (ConformalImage.mapOut (stripTargetHull (c.dom : Set ℂ)) (stripRightRetarget z) - ξ)) c.dom)
    {x : ℝ} (hx : extendFrom H (fwdMapInv W r) x ≠ 1)
    (hcollar : ∀ᶠ z in 𝓝[H] (x : ℂ), fwdMapInv W r z ∈ c.dom) :
    Tendsto (fun z => (c.1 (fwdMapInv W r z)).im) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  let q := extendFrom H (fwdMapInv W r) x
  have hqD : q ∉ c.dom := fun hq =>
    extendFrom_notMem_compl_fwdHull hW hW0 hη hr x (hsub hq)
  have hFq : Tendsto (fwdMapInv W r) (𝓝[H] (x : ℂ)) (𝓝 q) :=
    (hη.hasBdryLimits hW hW0 hr).tendsto (mem_Hbar_of_im_eq_zero (by simp))
  have hqbar : q ∈ Hbar := by
    have := GlueImg.nhdsWithin_H_neBot x
    have hqcl := mem_closure_of_tendsto hFq
      (eventually_nhdsWithin_of_forall fun z hz =>
        (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 hr hz).1)
    rwa [closure_H] at hqcl
  have hRD := H_diff_stripTargetHull hc.dom_subset
  have hRq : stripRightRetarget q ∉ H \ stripTargetHull (c.dom : Set ℂ) := by
    rw [hRD]
    rintro ⟨z, hz, he⟩
    by_cases hqH : q ∈ H
    · exact hqD ((isConformalBijection_stripRightRetarget.2.injOn
        hqH (hc.dom_subset hz) he.symm) ▸ hz)
    · have hq0 : q.im = 0 := le_antisymm (not_lt.1 hqH) hqbar
      have him : (stripRightRetarget q).im = 0 := by
        rw [stripRightRetarget_eq, div_im, sub_im, one_im, hq0]
        simp only [mul_zero, zero_mul, sub_zero, zero_div]
      have hzH := isConformalBijection_stripRightRetarget.2.mapsTo (hc.dom_subset hz)
      rw [he] at hzH
      change 0 < (stripRightRetarget q).im at hzH
      rw [him] at hzH
      exact lt_irrefl _ hzH
  have hRF : Tendsto (fun z => stripRightRetarget (fwdMapInv W r z))
      (𝓝[H] (x : ℂ)) (𝓝[H \ stripTargetHull (c.dom : Set ℂ)] (stripRightRetarget q)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨(continuousAt_stripRightRetarget hx).tendsto.comp hFq, ?_⟩
    exact hcollar.mono fun z hz => by rw [hRD]; exact mem_image_of_mem _ hz
  have ht := ((ConformalImage.isMapOut_mapOut hB).tendsto_im_nhdsWithin hB hRq).comp hRF
  have ht' := ht.const_mul a
  simp only [mul_zero] at ht'
  refine ht'.congr' ?_
  filter_upwards [hcollar] with z hz
  dsimp only [Function.comp_apply]
  rw [hscale hz]
  simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, sub_im, sub_zero]

/-- The actual current collar and chart normalization give a positive
reflection fixing zero for the own-to-retained coordinate transition. -/
theorem exists_posReflect_seed_transition {W : ℝ → ℝ} {η : ℝ → ℂ} {r : ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) (hη : IsLoewnerTrace W η)
    (htipH : η r ∈ H) (hr : 0 < r)
    {c : Chart} (hc : c.IsConformal) (hsub : (c.dom : Set ℂ) ⊆ H \ fwdHull W r)
    (hB : IsHPHull (stripTargetHull (c.dom : Set ℂ))) {a ξ : ℝ}
    (hscale : EqOn c.1 (fun z => (a : ℂ) *
      (ConformalImage.mapOut (stripTargetHull (c.dom : Set ℂ)) (stripRightRetarget z) - ξ)) c.dom)
    (hcollar : ∃ δ > 0, MapsTo (fwdMapInv W r) (ball 0 δ ∩ H) c.dom)
    (hzero : Tendsto (c.1 ∘ fwdMapInv W r) (𝓝[H] 0) (𝓝 0)) :
    ∃ ε > 0, ∃ G, IsPosReflect (c.1 ∘ fwdMapInv W r) G 0 ε ∧ G 0 = 0 ∧
      MapsTo (fwdMapInv W r) (H ∩ ball ((0 : ℝ) : ℂ) ε) c.dom := by
  obtain ⟨δ, hδ, hcol⟩ := hcollar
  have hbd := hη.hasBdryLimits hW hW0 hr.le
  have htip : extendFrom H (fwdMapInv W r) 0 = η r := by
    have := GlueImg.nhdsWithin_H_neBot 0
    exact tendsto_nhds_unique (hbd.tendsto (by change (0 : ℝ) ≤ 0; exact le_rfl))
      (hη.tendsto_fwdMapInv_tip hW hW0 hr.le)
  have htip1 : extendFrom H (fwdMapInv W r) 0 ≠ 1 := by
    rw [htip]
    intro he
    have hm := htipH
    rw [he] at hm
    exact (lt_irrefl (0 : ℝ)) hm
  have hev : ∀ᶠ z in 𝓝[Hbar] (0 : ℂ), extendFrom H (fwdMapInv W r) z ≠ 1 :=
    (hbd.continuousOn 0 (by change (0 : ℝ) ≤ 0; exact le_rfl)).eventually
      (isOpen_ne.mem_nhds htip1)
  obtain ⟨ε₀, hε₀, hsafe⟩ := Metric.mem_nhdsWithin_iff.1 hev
  let ε := min δ ε₀
  have hε : 0 < ε := lt_min hδ hε₀
  have hcol' : MapsTo (fwdMapInv W r) (H ∩ ball ((0 : ℝ) : ℂ) ε) c.dom :=
    fun z hz => hcol ⟨ball_subset_ball (min_le_left _ _) hz.2, hz.1⟩
  have hd := hc.differentiableOn_fwd.comp
    ((QuantumZipper.RS.differentiableOn_fwdMapInv hW hW0 hr.le).mono inter_subset_left) hcol'
  obtain ⟨G, hG⟩ := exists_isPosReflect hε hd
    (fun z hz => hc.fwd_mem (hcol' hz)) (fun z hz w hw he => by
      have he' := congrArg c.2.1 he
      dsimp only [Function.comp_apply] at he'
      rw [hc.inv_fwd (hcol' hz), hc.inv_fwd (hcol' hw)] at he'
      exact QuantumZipper.RS.injOn_fwdMapInv_H hW hW0 hr.le hz.1 hw.1 he') fun x hx => by
        apply tendsto_im_transition_zero hW hW0 hη hr.le hc hsub hB hscale
        · exact hsafe ⟨ball_subset_ball (min_le_right _ _) hx,
            mem_Hbar_of_im_eq_zero (by simp only [ofReal_im])⟩
        · have hnear : ∀ᶠ z in 𝓝[H] (x : ℂ), z ∈ H ∩ ball ((0 : ℝ) : ℂ) ε :=
            inter_mem_nhdsWithin H (isOpen_ball.mem_nhds hx)
          exact hnear.mono hcol'
  refine ⟨ε, hε, G, hG, ?_, hcol'⟩
  have := GlueImg.nhdsWithin_H_neBot 0
  have ht := hG.tendsto (y := 0) (mem_ball_self hε)
  rw [ofReal_zero] at ht
  exact tendsto_nhds_unique ht hzero

end InteractingSLE.Sec5.Aux61GStep
