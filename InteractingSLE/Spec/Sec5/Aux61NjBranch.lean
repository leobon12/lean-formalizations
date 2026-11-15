/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61NjSecant
import InteractingSLE.Spec.Sec5.Aux61NjHeight

/-!
# The branch integer at an eastern landing is one

Packet PROVE-AUX61-NOJUMP, second target. In R103's per-outcome family the landing height is the
returned counterflow value `+ θχ + 2πχn`, where `2πn` is the limit of the relative phase
`c.2.2 ∘ c⁻¹ − Im (log Ψ_s′) ∘ c⁻¹` at the landing chart point (`Aux61Cmp.cfCollar_limits`). In
counterflow coordinates this phase is the imaginary part of the logarithm `cfCollarLog` of the
derivative of the transition `T = c ∘ Ψ_s⁻¹` on `cfDom = Ψ_s(dom c)`.

* `cfDom`, `isOpen_cfDom`, `isPathConnected_cfDom`, `isDerivLog_cfCollarLog_cfDom`, `injOn_cfDom`:
  the transition on all of `Ψ_s(dom c)`;
* `cfPhase` (`= Im cfCollarLog`, `im_cfCollarLog`);
* `TargetSideBranch w s c` (deterministic per sample; proved in `Aux61NjTarget`): counterflow-chart real points
  `y ≤ junR` with arbitrarily negative transition value, at which `T` reflects positively (upper
  half-disc in `cfDom`) and the phase tends to `2π`. These are the points just right of the target
  `Ψ_s(1)` on the free part of `ℝ₊`: there `c.2.2 → 2π` (the retarget's `−2 log(1 − z)` branch past `1`
  and Aux. lemma 57 for the canonical logarithm), `Im log Ψ_s′ → 0` (Aux. lemma 57 in the hull frame,
  `arg g_s(−1/x) = π`, `arg x = 0`), and `T → −∞` at the pole;
* **`tendsto_cfPhase_two_pi`**: given `TargetSideBranch`, at every counterflow collar point `x > junR` the
  phase tends to `2π` (the secant comparison `im_eq_of_posReflect_pair` with a target-side point
  `y ≤ junR < x`, `T(y) < T(x)`);
* **`tendsto_chartPhase_two_pi`**: the same in chart coordinates at `b` (the limit in `CfAccess`'s
  height clause), so the branch integer is `n = 1`;
* **`height_eq_eastHeight_one`**: the realized landing height is `eastHeight S 1 = λ + πχ + (θ₂ − θ₁)χ`,
  which satisfies both RefPos's and RefNeg's bounds (`cumWeightRight_eastHeight`,
  `cumWeightLeft_eastHeight`): no index for `n` is needed in the per-outcome family.

`TargetSideBranch` is proved in `Aux61NjTarget` (`targetSideBranch_of_target`, from the target half-disc and
the strict left base gap); the unconditional source form is `Aux61NjTarget.ae_height_eq_eastHeight_one`. R48: no
Theorem 1.2/1.3 input; R77: no post-contact kernel. Nothing here replaces a source statement.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Metric Filter Topology
open scoped Real
open QuantumZipper (H Hbar chiC fwdHull fwdMapInv)

namespace InteractingSLE.Sec5.Aux61Nj
open Aux61TwoS Aux61Restart Aux61Cmp WangWu CrossCond.Word49
open Aux61SlitW Aux61SlitW.SourceSetting Aux61GAlign LawUnique GlueCond Cond44Ref Aux61GWord
universe u

/-! ### The transition on the whole chart domain -/

/-- The retained chart domain in counterflow coordinates. -/
def cfDom (w : ℝ → ℝ) (s : ℝ) (c : Chart) : Set ℂ := H ∩ revChartInv w s ⁻¹' (c.dom : Set ℂ)

/-- The relative phase `Im physicalRestartLog ∘ Ψ⁻¹ − Im log Ψ′ ∘ Ψ⁻¹` in counterflow coordinates. -/
def cfPhase (w : ℝ → ℝ) (s : ℝ) (c : Chart) (ζ : ℂ) : ℝ :=
  (physicalRestartLog (stripTargetHull (c.dom : Set ℂ)) (revChartInv w s ζ)).im -
    (GlueImg.logDerivPsi w s (revChartInv w s ζ)).im

theorem im_cfCollarLog (w : ℝ → ℝ) (s : ℝ) (c : Chart) (a : ℝ) (ζ : ℂ) :
    (cfCollarLog w s c a ζ).im = cfPhase w s c ζ := by
  simp only [cfCollarLog, cfPhase, add_im, ofReal_im, zero_add, neg_im, sub_eq_add_neg]

section Branch

variable {w : ℝ → ℝ} {γ : ℝ → ℂ} {s : ℝ}
  (hw : Continuous w) (hw0 : w 0 = 0) (hγ : IsLoewnerTrace w γ) (hs : 0 ≤ s)
  {c : Chart} (hc : c.IsConformal) (hsubK : (c.dom : Set ℂ) ⊆ H \ negInv '' fwdHull w s)
  (hB : IsHPHull (stripTargetHull (c.dom : Set ℂ))) {a ξ : ℝ}
  (hscale : EqOn c.1 (fun z => (a : ℂ) *
      (ConformalImage.mapOut (stripTargetHull (c.dom : Set ℂ)) (stripRightRetarget z) - ξ)) c.dom)

theorem cfDom_subset_H : cfDom w s c ⊆ H := inter_subset_left

include hw hw0 hs in
theorem isOpen_cfDom : IsOpen (cfDom w s c) := by
  have hRi := isConformalBijection_revChartInv hw hw0 hs
  have hcont : ContinuousOn (revChartInv w s) H := hRi.1.continuousOn
  exact hcont.isOpen_inter_preimage QuantumZipper.isOpen_H c.dom.isOpen

include hw hw0 hs hsubK in
theorem cfDom_eq_image : cfDom w s c = revChart w s '' (c.dom : Set ℂ) := by
  ext ζ
  constructor
  · rintro ⟨hζ, hd⟩
    exact ⟨_, hd, revChart_revChartInv hw hw0 hs hζ⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨revChart_mem_H hw hs (hsubK hz), ?_⟩
    show revChartInv w s (revChart w s z) ∈ (c.dom : Set ℂ)
    rw [revChartInv_revChart hw hw0 hs (hsubK hz)]
    exact hz

include hw hw0 hs hsubK in
theorem isPathConnected_cfDom (hsimply : IsSimplyConnected (c.dom : Set ℂ)) :
    IsPathConnected (cfDom w s c) := by
  have hpc : IsPathConnected (c.dom : Set ℂ) := by
    have : SimplyConnectedSpace (c.dom : Set ℂ) := hsimply
    exact isPathConnected_iff_pathConnectedSpace.2 inferInstance
  rw [cfDom_eq_image hw hw0 hs hsubK]
  exact hpc.image' fun z hz =>
    (GlueImg.differentiableAt_revChart hw hs (hsubK hz)).continuousAt.continuousWithinAt

include hw hw0 hs hc in
theorem injOn_cfDom : InjOn (c.1 ∘ revChartInv w s) (cfDom w s c) := by
  have hRi := isConformalBijection_revChartInv hw hw0 hs
  intro z hz z' hz' he
  have he' := congrArg c.2.1 he
  dsimp only [Function.comp_apply] at he'
  rw [hc.inv_fwd hz.2, hc.inv_fwd hz'.2] at he'
  exact hRi.2.injOn hz.1 hz'.1 he'

include hw hw0 hs hc in
theorem differentiableOn_cfDom : DifferentiableOn ℂ (c.1 ∘ revChartInv w s) (cfDom w s c) := by
  have hRi := isConformalBijection_revChartInv hw hw0 hs
  exact hc.differentiableOn_fwd.comp (hRi.1.mono inter_subset_left) fun _ hz => hz.2

include hc in
theorem mapsTo_cfDom : MapsTo (c.1 ∘ revChartInv w s) (cfDom w s c) H := fun _ hz =>
  hc.fwd_mem hz.2

include hw hw0 hs hc hB hscale in
theorem isDerivLog_cfCollarLog_cfDom (ha : 0 < a) :
    IsDerivLog (c.1 ∘ revChartInv w s) (cfCollarLog w s c a) (cfDom w s c) := by
  have hRi := isConformalBijection_revChartInv hw hw0 hs
  exact IsDerivLog.comp (isOpen_cfDom hw hw0 hs) c.dom.isOpen hc.differentiableOn_fwd
    (hRi.1.mono inter_subset_left) (fun z hz => hz.2) (isDerivLog_chart hc hB hscale ha)
    ((isDerivLog_revChartInv hw hw0 hs).mono inter_subset_left)

end Branch

/-! ### The target-side input and the branch integer -/

/-- **The target-side comparison points** (deterministic per sample; proved in `Aux61NjTarget`). For every bound `M`
there is a counterflow-chart real point `y ≤ junR` with transition value `< M` at which the transition
`c ∘ Ψ_s⁻¹` has a positive real reflection with upper half-disc in `cfDom`, and at which the relative
phase tends to `2π`. -/
def TargetSideBranch (w : ℝ → ℝ) (s : ℝ) (c : Chart) : Prop :=
  ∀ M : ℝ, ∃ (y ry : ℝ) (Gy : ℂ → ℂ), IsPosReflect (c.1 ∘ revChartInv w s) Gy y ry ∧
    H ∩ ball (y : ℂ) ry ⊆ cfDom w s c ∧ y ≤ junR w s ∧ (Gy y).re < M ∧
    Tendsto (cfPhase w s c) (𝓝[H] (y : ℂ)) (𝓝 (2 * π))

section Main

variable {w : ℝ → ℝ} {γ : ℝ → ℂ} {s : ℝ}
  (hw : Continuous w) (hw0 : w 0 = 0) (hγ : IsLoewnerTrace w γ) (hs : 0 ≤ s)
  {c : Chart} (hc : c.IsConformal) (hsubK : (c.dom : Set ℂ) ⊆ H \ negInv '' fwdHull w s)
  (hB : IsHPHull (stripTargetHull (c.dom : Set ℂ))) {a ξ : ℝ}
  (hscale : EqOn c.1 (fun z => (a : ℂ) *
      (ConformalImage.mapOut (stripTargetHull (c.dom : Set ℂ)) (stripRightRetarget z) - ξ)) c.dom)
  {ξ₀ δ : ℝ} (hδ : 0 < δ) (hcol : MapsTo (revChartInv w s) (H ∩ ball (ξ₀ : ℂ) δ) c.dom)
  (hfin : ∀ x : ℝ, (x : ℂ) ∈ ball (ξ₀ : ℂ) δ →
    x ≠ 0 ∧ extendFrom H (fwdMapInv w s) (negInv (x : ℂ)) ≠ 0 ∧ cfBdry w s x ≠ 1)

include hw hw0 hγ hs hc hsubK hB hscale hδ hcol hfin in
/-- **The phase is `2π` at every eastern collar point**, given the target-side comparison points. -/
theorem tendsto_cfPhase_two_pi (ha : 0 < a) (hsimply : IsSimplyConnected (c.dom : Set ℂ))
    (htarget : TargetSideBranch w s c) {x : ℝ} (hx : (x : ℂ) ∈ ball (ξ₀ : ℂ) δ)
    (hxe : junR w s < x) :
    Tendsto (cfPhase w s c) (𝓝[H] (x : ℂ)) (𝓝 (2 * π)) := by
  obtain ⟨G, hG⟩ := exists_isPosReflect_cfCollar hw hw0 hγ hs hc hsubK hB hscale hδ hcol hfin
  obtain ⟨r', hr', hsubb⟩ := Aux61TwoS.exists_ball_subset_ball hx
  have hG' := hG.of_subset hr' hsubb
  have hL := isDerivLog_cfCollarLog_cfDom hw hw0 hs hc hB hscale ha
  have hxD : H ∩ ball (x : ℂ) r' ⊆ cfDom w s c := fun z hz => ⟨hz.1, hcol ⟨hz.1, hsubb hz.2⟩⟩
  obtain ⟨n, hn⟩ := hG'.exists_int_tendsto_im (L := cfCollarLog w s c a)
    (hL.1.continuousOn.mono hxD) fun z hz => hL.2 z (hxD hz)
  obtain ⟨y, ry, Gy, hGy, hyD, hyj, hyM, hyl⟩ := htarget (G x).re
  have hyl' : Tendsto (fun z => (cfCollarLog w s c a z).im) (𝓝[H] (y : ℂ)) (𝓝 (2 * π)) := by
    simp only [im_cfCollarLog]; exact hyl
  have heq := im_eq_of_posReflect_pair (isOpen_cfDom hw hw0 hs) cfDom_subset_H
    (isPathConnected_cfDom hw hw0 hs hsubK hsimply) (differentiableOn_cfDom hw hw0 hs hc)
    (injOn_cfDom hw hw0 hs hc) (mapsTo_cfDom hc) hL.1.continuousOn hL.2 hG' hGy hxD hyD
    (hyj.trans_lt hxe) hyM hn hyl'
  simp only [im_cfCollarLog] at hn
  rwa [heq] at hn

include hw hw0 hγ hs hc hsubK hB hscale hδ hcol hfin in
/-- **The branch integer is one**: in chart coordinates, the relative phase at the landing chart
point `b` of an eastern collar point tends to `2π`. -/
theorem tendsto_chartPhase_two_pi (ha : 0 < a) (hsimply : IsSimplyConnected (c.dom : Set ℂ))
    (hlift : ∀ z ∈ (c.dom : Set ℂ),
      c.2.2 z = (physicalRestartLog (stripTargetHull (c.dom : Set ℂ)) z).im)
    (htarget : TargetSideBranch w s c) {x b : ℝ} (hx : (x : ℂ) ∈ ball (ξ₀ : ℂ) δ)
    (hxe : junR w s < x)
    (hxb : Tendsto (fun z => c.1 (revChartInv w s z)) (𝓝[H] (x : ℂ)) (𝓝 (b : ℂ))) :
    Tendsto (fun z => c.2.2 (c.2.1 z) - (GlueImg.logDerivPsi w s (c.2.1 z)).im)
      (𝓝[H] (b : ℂ)) (𝓝 (2 * π)) := by
  have hT := tendsto_cfTransition hw hw0 hγ hs hc hsubK hB hscale hδ hcol hfin hx hxb
  refine ((tendsto_cfPhase_two_pi hw hw0 hγ hs hc hsubK hB hscale hδ hcol hfin ha hsimply htarget hx
    hxe).comp hT).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hd := hc.inv_mem_dom hz
  simp only [Function.comp_apply, cfPhase, revChartInv_revChart hw hw0 hs (hsubK hd), hlift _ hd]

end Main

/-! ### The realized landing height -/

/-- **The realized landing height is `eastHeight S 1`**: at a chart point `b` whose height obeys
`CfAccess`'s height clause at an eastern counterflow point `x > 0` with physical point in `ℍ`, and at
which the relative phase tends to `2π`. -/
theorem height_eq_eastHeight_one (S : SourceSetting.{u}) (p : S.Ω × HistorySpace 0 0)
    {F : SourceRestartData S.Ω S.nL S.nR} {i : F.ι} {γ : ℝ → ℂ} (hγ : IsLoewnerTrace (cfW S p) γ)
    (hw0 : cfW S p 0 = 0) {x b : ℝ} (hx : 0 < x)
    (hF : extendFrom H (fwdMapInv (cfW S p) (rationalTime S.s)) (negInv (x : ℂ)) ∈ H)
    (hphase : Tendsto (fun z => ((S.marksData F).chart i p).2.2 (((S.marksData F).chart i p).2.1 z) -
      (GlueImg.logDerivPsi (cfW S p) (rationalTime S.s) (((S.marksData F).chart i p).2.1 z)).im)
      (𝓝[H] (b : ℂ)) (𝓝 (2 * π)))
    (hword : ∀ phase : ℝ, Tendsto (fun z => ((S.marksData F).chart i p).2.2
        (((S.marksData F).chart i p).2.1 z) -
        (GlueImg.logDerivPsi (cfW S p) (rationalTime S.s) (((S.marksData F).chart i p).2.1 z)).im)
        (𝓝[H] (b : ℂ)) (𝓝 phase) →
      (F.data i).bR b = returnedCfData S.κ (sourceCounterBoundary S)
        (forceJumpFinset S.xL S.xR) (rationalTime S.s) p.2 x + S.θ * chiC S.κ + chiC S.κ * phase) :
    (F.data i).bR b = eastHeight S 1 := by
  rw [hword _ hphase]
  have h := returned_add_eq_eastHeight S 1
    (returnedCfData_eq_of_extendFrom_mem_H S p hγ hw0 hx hF)
  rw [Int.cast_one, mul_one] at h
  exact h

/-! ### The source form -/

/-- **The branch integer on the selected records** (source form): almost surely on the selected
records, if the target-side comparison points exist for the record's chart, then at every chart point
`b` with a counterflow collar access (no fibre clause) whose counterflow point `x` lies east of the
junction, the relative phase tends to `2π`; if moreover the physical point of `x` is in `ℍ`, the word
height at `b` is `eastHeight S 1`. -/
theorem ae_phase_two_pi_of_access {S : SourceSetting.{u}} {F : SourceRestartData S.Ω S.nL S.nR}
    (hR : SourceRestartFacts F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life
      (μ := S.μ) S.κ) (i : F.ι)
    (hgeometry : ∀ᵐ p ∂S.μ, p ∈ F.event i →
      SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
        (cfHullQ (rationalTime S.s) p.2) (F.start i)
        (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p))
    (hcf : ∀ᵐ p ∂S.μ, cfW S p 0 = 0 ∧ ∃ γ : ℝ → ℂ, IsLoewnerTrace (cfW S p) γ) :
    ∀ᵐ p ∂S.μ, (S.marksData F).Z i p ∈ (S.marksData F).B i →
      TargetSideBranch (cfW S p) (rationalTime S.s) ((S.marksData F).chart i p) →
      ∀ (b ξ₀ δ x : ℝ), 0 < δ → (x : ℂ) ∈ ball (ξ₀ : ℂ) δ →
      MapsTo (revChartInv (cfW S p) (rationalTime S.s)) (H ∩ ball (ξ₀ : ℂ) δ)
        ((S.marksData F).chart i p).dom →
      (∀ x' : ℝ, (x' : ℂ) ∈ ball (ξ₀ : ℂ) δ → x' ≠ 0 ∧
        extendFrom H (fwdMapInv (cfW S p) (rationalTime S.s)) (negInv (x' : ℂ)) ≠ 0 ∧
        cfBdry (cfW S p) (rationalTime S.s) x' ≠ 1) →
      Tendsto (fun z => ((S.marksData F).chart i p).1 (revChartInv (cfW S p) (rationalTime S.s) z))
        (𝓝[H] (x : ℂ)) (𝓝 (b : ℂ)) →
      junR (cfW S p) (rationalTime S.s) < x →
      Tendsto (fun z => ((S.marksData F).chart i p).2.2 (((S.marksData F).chart i p).2.1 z) -
        (GlueImg.logDerivPsi (cfW S p) (rationalTime S.s) (((S.marksData F).chart i p).2.1 z)).im)
        (𝓝[H] (b : ℂ)) (𝓝 (2 * π)) := by
  filter_upwards [hgeometry, S.physical_path, hR.physical_stop i, hcf]
    with p hg hp hstop hcfp hB htarget b ξ₀ δ x hδ hx hcol hfin hxb hxe
  obtain ⟨hw0, γ, hγ⟩ := hcfp
  have hw : Continuous (cfW S p) := Sec4.continuous_rpath_regPath _
  have hs : (0 : ℝ) ≤ (rationalTime S.s : ℝ) := NNReal.coe_nonneg _
  have hsel : sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈ F.selected i := hB
  have he : p ∈ F.event i := (hstop hsel).1
  have hc : ((S.marksData F).chart i p).IsConformal := (hR.spec i).conf p he
  have hgeo := hg he
  have hW := hp.1.continuous_rpath
  have hW0 : (fun t : ℝ => S.own.W t.toNNReal p.1) 0 = 0 := by
    simpa only [Real.toNNReal_zero] using hp.1.2.1
  obtain ⟨a, ξ, ha, hscale⟩ := hgeo.scale hW hW0 hp.2.1 hp.2.2 hc
  have hBh := isHPHull_stripTargetHull ((S.marksData F).chart i p).dom.isOpen
    hgeo.simply hc.dom_subset hgeo.target
  have hsub : (((S.marksData F).chart i p).dom : Set ℂ) ⊆ H \ cfHullQ (rationalTime S.s) p.2 :=
    fun z hz => ⟨(hgeo.retained hz).1, fun hK => (hgeo.retained hz).2 (Or.inl hK)⟩
  have hKsub : negInv '' fwdHull (cfW S p) (rationalTime S.s) ⊆ cfHullQ (rationalTime S.s) p.2 :=
    image_mono (fwdHull_subset_hullAt (rationalTime S.s) p.2)
  have hsubK : (((S.marksData F).chart i p).dom : Set ℂ) ⊆
      H \ negInv '' fwdHull (cfW S p) (rationalTime S.s) :=
    fun z hz => ⟨(hsub hz).1, fun hK => (hsub hz).2 (hKsub hK)⟩
  exact tendsto_chartPhase_two_pi hw hw0 hγ hs hc hsubK hBh hscale hδ hcol hfin ha hgeo.simply
    hgeo.lift htarget hx hxe hxb

end InteractingSLE.Sec5.Aux61Nj
