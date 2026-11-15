/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GNextTarget

/-! # Finite access landing from the original-target normalization -/

set_option autoImplicit false
noncomputable section
open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Sec5.Aux61GNext
open Aux61Restart Aux61FibData Aux61GInst Aux61GCont

/-- The actual collar normalization of R1 supplies the inverse-target
condition; no additional condition at infinity is required. -/
theorem boundedInverse_target_of_collar_normalization {D₀ : Set ℂ} {c : Chart}
    (hD₀o : IsOpen D₀) (hD₀s : IsSimplyConnected D₀) (hD₀H : D₀ ⊆ H)
    (hc : c.IsConformal) (hDs : IsSimplyConnected (c.dom : Set ℂ)) (hsub : (c.dom : Set ℂ) ⊆ D₀)
    {F₀ : ℂ → ℂ} (hF₀ : IsConformalBijection F₀ H D₀) {z₀ : ℂ} (hz₀ : z₀ ∈ H)
    (hlim : Tendsto F₀ (𝓝[H] 0) (𝓝 z₀))
    (hcurrent : ∃ δ > 0, MapsTo F₀ (ball 0 δ ∩ H) c.dom)
    (htarget : ∃ δ > 0, ball (1 : ℂ) δ ∩ H ⊆ c.dom)
    (hc₀ : Tendsto (c.1 ∘ F₀) (𝓝[H] 0) (𝓝 0))
    (hc₁ : Tendsto (fun w => ‖c.1 (w + 1)‖) (𝓝[H] 0) atTop) :
    ∀ ε > 0, ∃ R : ℝ, ∀ z ∈ H, R ≤ ‖z‖ → dist (boundedInverse c z) (cayley 1) < ε := by
  have hcf : IsConformalBijection c.1 (c.dom : Set ℂ) H := by
    refine ⟨hc.differentiableOn_fwd, fun _ hz => hc.fwd_mem hz, ?_, fun z hz =>
      ⟨c.2.1 z, hc.inv_mem_dom hz, hc.2.2 z hz⟩⟩
    intro z hz w hw he
    have hi := congrArg c.2.1 he
    rwa [hc.inv_fwd hz, hc.inv_fwd hw] at hi
  obtain ⟨a, x, ha, hscale⟩ := exists_original_target_chart_scale hD₀o hD₀s hD₀H
    c.dom.isOpen hDs hsub hF₀ hz₀ hlim hcurrent htarget
    hcf hc₀ hc₁
  exact boundedInverse_target_of_scale hc
    (isHPHull_stripTargetHull c.dom.isOpen hDs hc.dom_subset htarget) ha hscale

/-- The bounded inverse of the chart path approaches the actual physical
contact in bounded physical coordinates. -/
theorem tendsto_boundedInverse_inPath_at_contact {X : Type*} [MeasurableSpace X]
    {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞}
    (hs : IsRestartSpec E c ρ T) {x : X} (hx : x ∈ E)
    (hpos : 0 < T x) (hfin : T x < ⊤) :
    Tendsto (boundedInverse (c x) ∘ inPath E c ρ T x) (𝓝[<] (T x).toNNReal)
      (𝓝 (cayley (ρ x (T x).toNNReal))) := by
  have hxev : x ∈ exitEv E c ρ T univ := mem_exitEv_of_finite hx hpos hfin
  have hbar : ρ x (T x).toNNReal ∈ Hbar := closure_H ▸
    closure_mono (hs.conf x hx).dom_subset (hs.mem_closure_at_T hxev hfin)
  have ht : Tendsto (fun u => cayley (ρ x u)) (𝓝[<] (T x).toNNReal)
      (𝓝 (cayley (ρ x (T x).toNNReal))) := ((QuantumZipper.CA.differentiableAt_cayley
    (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg hbar)).continuousAt.tendsto.comp
      (hs.contρ x hx).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  refine ht.congr' ?_
  have he : ((T x).toNNReal : ℝ≥0∞) = T x := ENNReal.coe_toNNReal hfin.ne
  have he0 : 0 < (T x).toNNReal := ENNReal.toNNReal_pos hpos.ne' hfin.ne
  filter_upwards [Ioo_mem_nhdsLT he0] with u hu
  have huT : (u : ℝ≥0∞) < T x := by rw [← he]; exact ENNReal.coe_lt_coe.2 hu.2
  dsimp only [Function.comp_apply]
  rw [hs.inPath_eq_fwd hx hu.1 huT,
    boundedInverse_eqOn_of_conformal (hs.conf x hx)
      ((hs.conf x hx).fwd_mem (hs.inside x hx u hu.1 huT))]
  dsimp only [Function.comp_apply]
  rw [(hs.conf x hx).inv_fwd (hs.inside x hx u hu.1 huT)]

/-- A finite physical contact away from the original target lands at a
finite real coordinate along its selected access. The retained chart's
inverse-target condition is proved from its canonical scale formula. -/
theorem exists_real_accessEndpoint_of_scale {X : Type*} [MeasurableSpace X]
    {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞}
    (hs : IsRestartSpec E c ρ T) {x : X} (hx : x ∈ E)
    (hpos : 0 < T x) (hfin : T x < ⊤)
    (hB : IsHPHull (stripTargetHull ((c x).dom : Set ℂ)))
    {a ξ : ℝ} (ha : 0 < a)
    (hscale : EqOn (c x).1 (fun z => (a : ℂ) *
      (ConformalImage.mapOut (stripTargetHull ((c x).dom : Set ℂ)) (stripRightRetarget z) - ξ)) (c x).dom)
    (hF : ContinuousOn (boundedInverse (c x)) Hbar ∧
      DifferentiableOn ℂ (boundedInverse (c x)) H ∧ InjOn (boundedInverse (c x)) H ∧
      ∀ z : ℂ, z.im = 0 → boundedInverse (c x) z ∉ boundedInverse (c x) '' H)
    (hcontact : ρ x (T x).toNNReal ∉ (c x).dom)
    (hnot_target : ρ x (T x).toNNReal ≠ 1) :
    ∃ y : ℝ, boundedInverse (c x) (y : ℂ) = cayley (ρ x (T x).toNNReal) ∧
      Tendsto (inPath E c ρ T x) (𝓝[<] (T x).toNNReal) (𝓝 (y : ℂ)) := by
  have hc := hs.conf x hx
  have hxev : x ∈ exitEv E c ρ T univ := mem_exitEv_of_finite hx hpos hfin
  have hbar : ρ x (T x).toNNReal ∈ Hbar := closure_H ▸
    closure_mono hc.dom_subset (hs.mem_closure_at_T hxev hfin)
  have htargetbar : (1 : ℂ) ∈ Hbar := by change 0 ≤ (1 : ℂ).im; simp only [one_im, le_refl]
  have hp : cayley (ρ x (T x).toNNReal) ≠ cayley 1 :=
    fun he => hnot_target (QuantumZipper.CA.bijOn_cayley_Hbar.injOn hbar htargetbar he)
  obtain ⟨L, hLbar, hFL, hlim⟩ := exists_finite_accessEndpoint_of_target hs hx
    (ENNReal.toNNReal_pos hpos.ne' hfin.ne) (ENNReal.coe_toNNReal hfin.ne).le
    hF.2.1 hF.1 hF.2.2.1 hF.2.2.2 (tendsto_boundedInverse_inPath_at_contact hs hx hpos hfin) hp
    (boundedInverse_target_of_scale hc hB ha hscale)
  have hL0 : L.im = 0 := by
    apply le_antisymm _ hLbar
    by_contra hn
    have hLH : L ∈ H := lt_of_not_ge hn
    have he := hFL
    rw [boundedInverse_eqOn_of_conformal hc hLH] at he
    have hinvbar : (c x).2.1 L ∈ Hbar := H_subset_Hbar (hc.dom_subset (hc.inv_mem_dom hLH))
    have hephys := QuantumZipper.CA.bijOn_cayley_Hbar.injOn hinvbar hbar he
    exact hcontact (hephys ▸ hc.inv_mem_dom hLH)
  have heL : (L.re : ℂ) = L := Complex.ext rfl (by simp only [ofReal_im, hL0])
  exact ⟨L.re, heL ▸ hFL, heL ▸ hlim⟩

end InteractingSLE.Sec5.Aux61GNext
