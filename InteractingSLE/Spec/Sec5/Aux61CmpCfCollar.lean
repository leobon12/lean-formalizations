/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CmpSeedCollar
import InteractingSLE.Spec.Sec5.GlueCondUnionImg
import InteractingSLE.Spec.Sec5.GlueCondUnionImgMean

/-! # Counterflow-side germs along a counterflow collar

The counterflow chart is `Ψ_s = revChart w s = R ∘ f_s ∘ R` (`R = negInv`), with
inverse `Ψ_s⁻¹ = revChartInv w s = R ∘ F_s ∘ R`. A **counterflow collar** of the
retained chart `c` is a half-disc `ℍ ∩ B(ξ₀, δ)` (in `Ψ_s`-coordinates) mapped by
`Ψ_s⁻¹` into `dom c`, whose real points have finite physical images
`cfBdry w s x = R(F̄_s(R x))` different from the target `1`.

On such a collar the transition `c ∘ Ψ_s⁻¹` reflects (`exists_isPosReflect_cfCollar`);
at a chart point `b = (c ∘ Ψ_s⁻¹)(x)` the transition `Ψ_s ∘ c⁻¹` tends to `x`
inside `ℍ` (`tendsto_cfTransition`), the inherited relative phase
`c.2.2 ∘ c⁻¹ − Im (log Ψ_s′) ∘ c⁻¹` has a lattice limit `2πn`
(`exists_int_tendsto_cfPhase`), and the inverse chart lands at `cfBdry w s x`
(`tendsto_inv_cfCollar`). If every physical preimage of that point (in
`R`-coordinates) lies in the collar, a ball around it minus the counterflow
hull lies in `dom c` (`exists_ball_inter_subset_dom_cf`, from the general
open-collar form `exists_ball_inter_subset_of_open`).

Deterministic; no source statement is replaced.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Metric Filter Topology
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd)

namespace InteractingSLE.Sec5.Aux61Cmp
open Aux61Restart Aux61TwoS WangWu

/-! ### Full-ball containment along an open collar -/

section OpenCollar

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {r : ℝ}
  (hW : Continuous W) (hW0 : W 0 = 0) (hη : IsLoewnerTrace W η) (hr : 0 ≤ r)
  {D U : Set ℂ} (hU : IsOpen U) (hcol : MapsTo (fwdMapInv W r) (U ∩ H) D)

include hW hW0 hη hr hU hcol in
/-- **Full-ball containment along an open collar**: if every real preimage of
`F̄_r(t)` lies in the open set `U` whose upper part `F_r` maps into `D`, a whole
ball around `F̄_r(t)` minus the hull lies in `D`. -/
theorem exists_ball_inter_subset_of_open (t : ℝ)
    (hpre : ∀ y : ℝ, extendFrom H (fwdMapInv W r) y = extendFrom H (fwdMapInv W r) t → (y : ℂ) ∈ U) :
    ∃ ρ > 0, ball (extendFrom H (fwdMapInv W r) t) ρ ∩ (H \ fwdHull W r) ⊆ D := by
  set Fb := extendFrom H (fwdMapInv W r) with hFb
  set z₀ := Fb t with hz₀
  obtain ⟨C, hC⟩ := QuantumZipper.R18.exists_norm_fwdMapInv_sub_le hW hW0 hr
  have hcont : ContinuousOn Fb Hbar := (hη.hasBdryLimits hW hW0 hr).continuousOn
  set R : ℝ := ‖z₀‖ + 1 + C with hR
  set K : Set ℂ := (Hbar ∩ Uᶜ) ∩ closedBall 0 R with hK
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (QuantumZipper.isClosed_Hbar.inter hU.isClosed_compl).inter isClosed_closedBall
    · exact Metric.isBounded_closedBall.subset inter_subset_right
  have hFK : IsClosed (Fb '' K) :=
    (hKc.image_of_continuousOn (hcont.mono fun y hy => hy.1.1)).isClosed
  have hz₀K : z₀ ∉ Fb '' K := by
    rintro ⟨y, hyK, hy⟩
    by_cases hyH : y ∈ H
    · have hn := extendFrom_notMem_compl_fwdHull hW hW0 hη hr t
      rw [← hFb, ← hz₀, ← hy, hFb, WangWu.extendFrom_fwdMapInv_eq hW hW0 hr hyH] at hn
      exact hn (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 hr hyH)
    · have hy0 : y.im = 0 := le_antisymm (not_lt.1 hyH) hyK.1.1
      have hyr : ((y.re : ℝ) : ℂ) = y := ofReal_re_eq hy0
      have h := hpre y.re (by rw [hyr]; exact hy)
      rw [hyr] at h
      exact hyK.1.2 h
  obtain ⟨ρ₁, hρ₁, hball⟩ := Metric.isOpen_iff.1 hFK.isOpen_compl z₀ hz₀K
  refine ⟨min ρ₁ 1, lt_min hρ₁ one_pos, fun w hw => ?_⟩
  obtain ⟨hwb, hwH, hwK⟩ := hw
  have hyH : fwdMap W r w ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hW hr ⟨hwH, hwK⟩
  have hFy : fwdMapInv W r (fwdMap W r w) = w :=
    QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hr ⟨hwH, hwK⟩
  by_cases hyU : fwdMap W r w ∈ U
  · rw [← hFy]
    exact hcol ⟨hyU, hyH⟩
  · exfalso
    have hwz : dist w z₀ < 1 := lt_of_lt_of_le hwb (min_le_right _ _)
    have h1 := hC _ hyH
    rw [hFy] at h1
    have h2 : ‖w‖ ≤ ‖z₀‖ + 1 := by
      have := norm_sub_norm_le w z₀
      rw [dist_eq_norm] at hwz
      linarith
    have h3 : ‖fwdMap W r w‖ ≤ ‖w‖ + ‖w - fwdMap W r w‖ := by
      have := norm_sub_le w (w - fwdMap W r w)
      rwa [sub_sub_cancel] at this
    have h4 : ‖w - fwdMap W r w‖ ≤ C := h1
    have hyK : fwdMap W r w ∈ K := ⟨⟨QuantumZipper.H_subset_Hbar hyH, hyU⟩, by
      rw [mem_closedBall, dist_zero_right]; linarith⟩
    refine hball (mem_ball.2 (lt_of_lt_of_le hwb (min_le_left _ _))) ⟨_, hyK, ?_⟩
    rw [hFb, WangWu.extendFrom_fwdMapInv_eq hW hW0 hr hyH, hFy]

end OpenCollar

/-! ### Imaginary part of the retained chart at a boundary point -/

section ChartIm

variable {c : Chart} (hc : c.IsConformal) (hB : IsHPHull (stripTargetHull (c.dom : Set ℂ))) {a ξ : ℝ}
  (hscale : EqOn c.1 (fun z => (a : ℂ) *
      (ConformalImage.mapOut (stripTargetHull (c.dom : Set ℂ)) (stripRightRetarget z) - ξ)) c.dom)

include hc hB hscale in
/-- Along any approach to a boundary point `q ∈ ℍ̄ ∖ dom c` other than the target
`1`, the normalized retained chart has imaginary part tending to zero. -/
theorem tendsto_im_chart_of_bdry {l : Filter ℂ} {φ : ℂ → ℂ} {q : ℂ}
    (hφ : Tendsto φ l (𝓝 q)) (hev : ∀ᶠ z in l, φ z ∈ (c.dom : Set ℂ))
    (hq1 : q ≠ 1) (hqD : q ∉ (c.dom : Set ℂ)) (hqbar : q ∈ Hbar) :
    Tendsto (fun z => (c.1 (φ z)).im) l (𝓝 0) := by
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
  have hRF : Tendsto (fun z => stripRightRetarget (φ z)) l
      (𝓝[H \ stripTargetHull (c.dom : Set ℂ)] (stripRightRetarget q)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨(continuousAt_stripRightRetarget hq1).tendsto.comp hφ, ?_⟩
    exact hev.mono fun z hz => by rw [hRD]; exact mem_image_of_mem _ hz
  have ht := ((ConformalImage.isMapOut_mapOut hB).tendsto_im_nhdsWithin hB hRq).comp hRF
  have ht' := ht.const_mul a
  simp only [mul_zero] at ht'
  refine ht'.congr' ?_
  filter_upwards [hev] with z hz
  dsimp only [Function.comp_apply]
  rw [hscale hz]
  simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, sub_im, sub_zero]

include hc hB hscale in
/-- R1's positive-scale logarithm of the retained chart's derivative. -/
theorem isDerivLog_chart (ha : 0 < a) : IsDerivLog c.1 (fun z => (Real.log a : ℂ) +
    physicalRestartLog (stripTargetHull (c.dom : Set ℂ)) z) c.dom := by
  have hdom : IsOpen (c.dom : Set ℂ) := c.dom.isOpen
  have hRD := H_diff_stripTargetHull hc.dom_subset
  have hmaps : MapsTo stripRightRetarget (c.dom : Set ℂ) (H \ stripTargetHull (c.dom : Set ℂ)) :=
    fun z hz => by rw [hRD]; exact mem_image_of_mem _ hz
  have hgd : DifferentiableOn ℂ
      (ConformalImage.mapOut (stripTargetHull (c.dom : Set ℂ)) ∘ stripRightRetarget) c.dom :=
    (ConformalImage.isMapOut_mapOut hB).1.1.comp
      (isConformalBijection_stripRightRetarget.1.mono hc.dom_subset) hmaps
  exact isDerivLog_pos_scale_sub hdom hgd
    (isDerivLog_physicalRestartLog hdom hB hc.dom_subset hmaps) ha hscale

end ChartIm

/-! ### The counterflow collar -/

/-- The physical boundary point of the counterflow-chart real point `x`. -/
def cfBdry (w : ℝ → ℝ) (s : ℝ) (x : ℝ) : ℂ :=
  negInv (extendFrom H (fwdMapInv w s) (negInv (x : ℂ)))

theorem negInv_ofReal_im (x : ℝ) : (negInv (x : ℂ)).im = 0 := by
  simp [negInv]

theorem negInv_ne_zero {z : ℂ} (hz : z ≠ 0) : negInv z ≠ 0 := by
  simp only [negInv, ne_eq, neg_eq_zero, inv_eq_zero]
  exact hz

/-- The inverse counterflow chart is a derivative logarithm's inverse branch. -/
theorem isDerivLog_revChartInv {w : ℝ → ℝ} {s : ℝ} (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s) :
    IsDerivLog (revChartInv w s) (fun y => -GlueImg.logDerivPsi w s (revChartInv w s y)) H := by
  have hRi := isConformalBijection_revChartInv hw hw0 hs
  have hL := GlueImg.isDerivLog_revChart hw hs
  refine ⟨(hL.1.comp hRi.1 hRi.2.mapsTo).neg, fun y hy => ?_⟩
  have hy' := revChartInv_mem hw hw0 hs hy
  have hdR := GlueImg.differentiableAt_revChart hw hs hy'
  have hdRi : DifferentiableAt ℂ (revChartInv w s) y :=
    hRi.1.differentiableAt (QuantumZipper.isOpen_H.mem_nhds hy)
  have hid : revChart w s ∘ revChartInv w s =ᶠ[𝓝 y] id :=
    Filter.eventuallyEq_of_mem (QuantumZipper.isOpen_H.mem_nhds hy) fun ζ hζ =>
      revChart_revChartInv hw hw0 hs hζ
  have hchain := (hdR.hasDerivAt.comp y hdRi.hasDerivAt).deriv
  rw [hid.deriv_eq, deriv_id] at hchain
  rw [exp_neg, hL.2 _ hy']
  exact (eq_inv_of_mul_eq_one_right hchain.symm).symm

section CfCollar

variable {w : ℝ → ℝ} {γ : ℝ → ℂ} {s : ℝ}
  (hw : Continuous w) (hw0 : w 0 = 0) (hγ : IsLoewnerTrace w γ) (hs : 0 ≤ s)
  {c : Chart} (hc : c.IsConformal) (hsubK : (c.dom : Set ℂ) ⊆ H \ negInv '' fwdHull w s)
  (hB : IsHPHull (stripTargetHull (c.dom : Set ℂ))) {a ξ : ℝ}
  (hscale : EqOn c.1 (fun z => (a : ℂ) *
      (ConformalImage.mapOut (stripTargetHull (c.dom : Set ℂ)) (stripRightRetarget z) - ξ)) c.dom)
  {ξ₀ δ : ℝ} (hδ : 0 < δ) (hcol : MapsTo (revChartInv w s) (H ∩ ball (ξ₀ : ℂ) δ) c.dom)
  (hfin : ∀ x : ℝ, (x : ℂ) ∈ ball (ξ₀ : ℂ) δ →
    x ≠ 0 ∧ extendFrom H (fwdMapInv w s) (negInv (x : ℂ)) ≠ 0 ∧ cfBdry w s x ≠ 1)

include hw hw0 hγ hs in
/-- The inverse counterflow chart lands at the physical boundary point. -/
theorem tendsto_revChartInv_cfBdry {x : ℝ} (hx0 : x ≠ 0)
    (hF0 : extendFrom H (fwdMapInv w s) (negInv (x : ℂ)) ≠ 0) :
    Tendsto (revChartInv w s) (𝓝[H] (x : ℂ)) (𝓝 (cfBdry w s x)) := by
  have hx0' : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx0
  have hN : Tendsto negInv (𝓝[H] (x : ℂ)) (𝓝 (negInv (x : ℂ))) :=
    (continuousAt_negInv hx0').tendsto.mono_left nhdsWithin_le_nhds
  have hN' : Tendsto negInv (𝓝[H] (x : ℂ)) (𝓝[H] (negInv (x : ℂ))) :=
    tendsto_nhdsWithin_iff.2 ⟨hN, eventually_nhdsWithin_of_forall fun z hz => negInv_mem_H hz⟩
  have hbar : negInv (x : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (negInv_ofReal_im x)
  have hF := ((hγ.hasBdryLimits hw hw0 hs).tendsto hbar).comp hN'
  exact (continuousAt_negInv hF0).tendsto.comp hF

include hw hw0 hγ hs hsubK in
/-- The physical boundary point of a counterflow-chart real point is not in the
retained domain and lies in `ℍ̄`. -/
theorem cfBdry_notMem_dom (x : ℝ) :
    cfBdry w s x ∉ (c.dom : Set ℂ) ∧ cfBdry w s x ∈ Hbar := by
  have hbar : negInv (x : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (negInv_ofReal_im x)
  have hFbar : extendFrom H (fwdMapInv w s) (negInv (x : ℂ)) ∈ Hbar := by
    have := Prop49Exit.extendFrom_mem_Hbar hγ hw hw0 hs (negInv (x : ℂ)).re
    rwa [ofReal_re_eq (negInv_ofReal_im x)] at this
  refine ⟨fun hd => ?_, Sec7.PocketJordan.negInv_mem_Hbar hFbar⟩
  have h := negInv_notMem_fwdHull (hsubK hd)
  rw [cfBdry, negInv_negInv'] at h
  have hn := extendFrom_notMem_compl_fwdHull hw hw0 hγ hs (negInv (x : ℂ)).re
  rw [ofReal_re_eq (negInv_ofReal_im x)] at hn
  exact hn h

include hw hw0 hγ hs hc hsubK hB hscale hδ hcol hfin in
/-- The transition `c ∘ Ψ_s⁻¹` reflects across the counterflow collar. -/
theorem exists_isPosReflect_cfCollar : ∃ G, IsPosReflect (c.1 ∘ revChartInv w s) G ξ₀ δ := by
  have hRi := isConformalBijection_revChartInv hw hw0 hs
  have hd := hc.differentiableOn_fwd.comp (hRi.1.mono inter_subset_left) hcol
  refine exists_isPosReflect hδ hd (fun z hz => hc.fwd_mem (hcol hz)) (fun z hz u hu he => ?_)
    fun x hx => ?_
  · have he' := congrArg c.2.1 he
    dsimp only [Function.comp_apply] at he'
    rw [hc.inv_fwd (hcol hz), hc.inv_fwd (hcol hu)] at he'
    exact hRi.2.injOn hz.1 hu.1 he'
  · obtain ⟨hx0, hF0, h1⟩ := hfin x hx
    obtain ⟨hqD, hqbar⟩ := cfBdry_notMem_dom hw hw0 hγ hs hsubK x
    have hnear : ∀ᶠ z in 𝓝[H] (x : ℂ), z ∈ H ∩ ball (ξ₀ : ℂ) δ :=
      inter_mem_nhdsWithin H (isOpen_ball.mem_nhds hx)
    exact tendsto_im_chart_of_bdry hc hB hscale (tendsto_revChartInv_cfBdry hw hw0 hγ hs hx0 hF0)
      (hnear.mono hcol) h1 hqD hqbar

/-- The logarithm of the derivative of `c ∘ Ψ_s⁻¹`. -/
def cfCollarLog (w : ℝ → ℝ) (s : ℝ) (c : Chart) (a : ℝ) (y : ℂ) : ℂ :=
  (Real.log a : ℂ) + physicalRestartLog (stripTargetHull (c.dom : Set ℂ)) (revChartInv w s y) +
    -GlueImg.logDerivPsi w s (revChartInv w s y)

include hw hw0 hs hc hB hscale hcol in
theorem isDerivLog_cfCollarLog (ha : 0 < a) :
    IsDerivLog (c.1 ∘ revChartInv w s) (cfCollarLog w s c a) (H ∩ ball (ξ₀ : ℂ) δ) := by
  have hRi := isConformalBijection_revChartInv hw hw0 hs
  have hDo : IsOpen (H ∩ ball (ξ₀ : ℂ) δ) := QuantumZipper.isOpen_H.inter isOpen_ball
  exact IsDerivLog.comp hDo c.dom.isOpen hc.differentiableOn_fwd (hRi.1.mono inter_subset_left) hcol
    (isDerivLog_chart hc hB hscale ha) ((isDerivLog_revChartInv hw hw0 hs).mono inter_subset_left)

include hw hw0 hγ hs hc hsubK hB hscale hδ hcol hfin in
/-- **The inherited relative phase has a lattice limit** at every collar point. -/
theorem exists_int_tendsto_cfLog (ha : 0 < a)
    (hlift : ∀ z ∈ (c.dom : Set ℂ),
      c.2.2 z = (physicalRestartLog (stripTargetHull (c.dom : Set ℂ)) z).im)
    {x : ℝ} (hx : (x : ℂ) ∈ ball (ξ₀ : ℂ) δ) :
    ∃ n : ℤ, Tendsto (fun y => c.2.2 (revChartInv w s y) -
      (GlueImg.logDerivPsi w s (revChartInv w s y)).im) (𝓝[H] (x : ℂ)) (𝓝 (2 * Real.pi * n)) := by
  obtain ⟨G, hG⟩ := exists_isPosReflect_cfCollar hw hw0 hγ hs hc hsubK hB hscale hδ hcol hfin
  have hL := isDerivLog_cfCollarLog hw hw0 hs hc hB hscale hcol (δ := δ) (ξ₀ := ξ₀) ha
  obtain ⟨r', hr', hsubb⟩ := Aux61TwoS.exists_ball_subset_ball hx
  have hG' := hG.of_subset hr' hsubb
  have hsub' : H ∩ ball (x : ℂ) r' ⊆ H ∩ ball (ξ₀ : ℂ) δ := fun z hz => ⟨hz.1, hsubb hz.2⟩
  obtain ⟨n, hn⟩ := hG'.exists_int_tendsto_im (hL.1.continuousOn.mono hsub')
    fun z hz => hL.2 z (hsub' hz)
  refine ⟨n, hn.congr' ?_⟩
  filter_upwards [inter_mem_nhdsWithin H (isOpen_ball.mem_nhds (mem_ball_self hr'))] with z hz
  rw [hlift _ (hcol (hsub' hz))]
  simp only [cfCollarLog, add_im, ofReal_im, zero_add, neg_im, sub_eq_add_neg]

include hw hw0 hγ hs hc hsubK hB hscale hδ hcol hfin in
/-- **The transition into the counterflow chart** at a collar chart point. -/
theorem tendsto_cfTransition {x b : ℝ} (hx : (x : ℂ) ∈ ball (ξ₀ : ℂ) δ)
    (hxb : Tendsto (fun z => c.1 (revChartInv w s z)) (𝓝[H] (x : ℂ)) (𝓝 (b : ℂ))) :
    Tendsto (fun z => revChart w s (c.2.1 z)) (𝓝[H] (b : ℂ)) (𝓝[H] (x : ℂ)) := by
  obtain ⟨G, hG⟩ := exists_isPosReflect_cfCollar hw hw0 hγ hs hc hsubK hB hscale hδ hcol hfin
  have hNB := GlueImg.nhdsWithin_H_neBot x
  have hGx : G x = (b : ℂ) := tendsto_nhds_unique (hG.tendsto hx) hxb
  obtain ⟨r', hr', hsubb⟩ := Aux61TwoS.exists_ball_subset_ball hx
  have hG' := hG.of_subset hr' hsubb
  have hleft : ∀ u ∈ H ∩ ball (x : ℂ) r',
      (fun z => revChart w s (c.2.1 z)) ((c.1 ∘ revChartInv w s) u) = u := by
    intro u hu
    have hu' : u ∈ H ∩ ball (ξ₀ : ℂ) δ := ⟨hu.1, hsubb hu.2⟩
    dsimp only [Function.comp_apply]
    rw [hc.inv_fwd (hcol hu')]
    exact revChart_revChartInv hw hw0 hs hu.1
  have h := hG'.tendsto_leftInv (Θ := fun z => revChart w s (c.2.1 z)) hleft
  rwa [hGx] at h

include hw hw0 hγ hs hc hsubK hB hscale hδ hcol hfin in
/-- At a collar chart point the relative phase of the inherited lift has a
lattice limit and the inverse chart lands at the physical boundary point. -/
theorem cfCollar_limits (ha : 0 < a)
    (hlift : ∀ z ∈ (c.dom : Set ℂ),
      c.2.2 z = (physicalRestartLog (stripTargetHull (c.dom : Set ℂ)) z).im)
    {x b : ℝ} (hx : (x : ℂ) ∈ ball (ξ₀ : ℂ) δ)
    (hxb : Tendsto (fun z => c.1 (revChartInv w s z)) (𝓝[H] (x : ℂ)) (𝓝 (b : ℂ))) :
    (∃ n : ℤ, Tendsto (fun z => c.2.2 (c.2.1 z) - (GlueImg.logDerivPsi w s (c.2.1 z)).im)
      (𝓝[H] (b : ℂ)) (𝓝 (2 * Real.pi * n))) ∧
    Tendsto c.2.1 (𝓝[H] (b : ℂ)) (𝓝 (cfBdry w s x)) := by
  have hT := tendsto_cfTransition hw hw0 hγ hs hc hsubK hB hscale hδ hcol hfin hx hxb
  have hback : ∀ᶠ z in 𝓝[H] (b : ℂ), revChartInv w s (revChart w s (c.2.1 z)) = c.2.1 z :=
    eventually_nhdsWithin_of_forall fun z hz =>
      revChartInv_revChart hw hw0 hs (hsubK (hc.inv_mem_dom hz))
  obtain ⟨hx0, hF0, -⟩ := hfin x hx
  refine ⟨?_, ?_⟩
  · obtain ⟨n, hn⟩ := exists_int_tendsto_cfLog hw hw0 hγ hs hc hsubK hB hscale hδ hcol hfin ha hlift hx
    refine ⟨n, (hn.comp hT).congr' ?_⟩
    filter_upwards [hback] with z hz
    simp only [Function.comp_apply, hz]
  · refine ((tendsto_revChartInv_cfBdry hw hw0 hγ hs hx0 hF0).comp hT).congr' ?_
    filter_upwards [hback] with z hz
    simp only [Function.comp_apply, hz]

include hw hw0 hγ hs hcol in
/-- **Full-ball containment on the counterflow side**: if every real preimage
(in `R`-coordinates) of the physical boundary point lies in the collar, a ball
around it minus the counterflow hull lies in the retained domain. -/
theorem exists_ball_inter_subset_dom_cf {x : ℝ}
    (hF0 : extendFrom H (fwdMapInv w s) (negInv (x : ℂ)) ≠ 0)
    (hpre : ∀ y : ℝ, extendFrom H (fwdMapInv w s) y = extendFrom H (fwdMapInv w s) (negInv (x : ℂ)) →
      (y : ℂ) ≠ 0 ∧ negInv (y : ℂ) ∈ ball (ξ₀ : ℂ) δ) :
    ∃ ρ > 0, ball (cfBdry w s x) ρ ∩ (H \ negInv '' fwdHull w s) ⊆ c.dom := by
  set U : Set ℂ := {u | u ≠ 0} ∩ negInv ⁻¹' ball (ξ₀ : ℂ) δ with hUdef
  have hcon : ContinuousOn negInv {u : ℂ | u ≠ 0} := fun u hu =>
    (continuousAt_negInv hu).continuousWithinAt
  have hU : IsOpen U := hcon.isOpen_inter_preimage isOpen_ne isOpen_ball
  have hcolU : MapsTo (fwdMapInv w s) (U ∩ H) {z | negInv z ∈ (c.dom : Set ℂ)} := by
    intro u hu
    have h := hcol ⟨negInv_mem_H hu.2, hu.1.2⟩
    simp only [revChartInv, negInv_negInv'] at h
    exact h
  have hxr : (((negInv (x : ℂ)).re : ℝ) : ℂ) = negInv (x : ℂ) := ofReal_re_eq (negInv_ofReal_im x)
  obtain ⟨ρ, hρ, hball⟩ := exists_ball_inter_subset_of_open hw hw0 hγ hs hU hcolU
    (negInv (x : ℂ)).re fun y hy => by
      rw [hxr] at hy
      exact hpre y hy
  rw [hxr] at hball
  have hz₀ : cfBdry w s x ≠ 0 := negInv_ne_zero hF0
  obtain ⟨ρ', hρ', hcont⟩ := Metric.continuousAt_iff.1 (continuousAt_negInv hz₀) ρ hρ
  refine ⟨ρ', hρ', fun v hv => ?_⟩
  have hvK := negInv_notMem_fwdHull hv.2
  have hd : dist (negInv v) (negInv (cfBdry w s x)) < ρ := hcont hv.1
  rw [cfBdry, negInv_negInv'] at hd
  have h : negInv (negInv v) ∈ (c.dom : Set ℂ) := hball ⟨hd, hvK⟩
  rwa [negInv_negInv'] at h

include hw hw0 hγ hs in
/-- The physical boundary point lies in the counterflow hull or on `ℝ`. -/
theorem cfBdry_mem_hull_or_real (x : ℝ) :
    cfBdry w s x ∈ negInv '' fwdHull w s ∪ {z : ℂ | z.im = 0} := by
  have hxr : (((negInv (x : ℂ)).re : ℝ) : ℂ) = negInv (x : ℂ) := ofReal_re_eq (negInv_ofReal_im x)
  have hbar := Prop49Exit.extendFrom_mem_Hbar hγ hw hw0 hs (negInv (x : ℂ)).re
  rw [hxr] at hbar
  by_cases hH : extendFrom H (fwdMapInv w s) (negInv (x : ℂ)) ∈ H
  · left
    refine ⟨_, ?_, rfl⟩
    by_contra hK
    have hn := extendFrom_notMem_compl_fwdHull hw hw0 hγ hs (negInv (x : ℂ)).re
    rw [hxr] at hn
    exact hn ⟨hH, hK⟩
  · right
    have h0 : (extendFrom H (fwdMapInv w s) (negInv (x : ℂ))).im = 0 := le_antisymm (not_lt.1 hH) hbar
    show (negInv (extendFrom H (fwdMapInv w s) (negInv (x : ℂ)))).im = 0
    generalize extendFrom H (fwdMapInv w s) (negInv (x : ℂ)) = v at h0 ⊢
    simp only [negInv, neg_im, inv_im, h0, neg_zero, zero_div]

end CfCollar

end InteractingSLE.Sec5.Aux61Cmp
