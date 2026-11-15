/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61NjCrosscut
import InteractingSLE.Spec.Sec5.Aux61CmpCfGerm

/-!
# Pinch-free component germs on both sides of the fibre cover

Packet PROVE-AUX61-NOJUMP (ruling R103). COMPARE's accesses `Aux61Cmp.CfAccess` and
`Aux61Cmp.SeedAccess` carry a **fibre clause** (every physical preimage of the landing point lies in
the collar), used only to get a *full* ball around the landing point inside the retained domain. At
a pinch point of the counterflow hull (a point of both hull sides) this clause fails, and R103 left
open whether such landings are null. The component comparisons `Aux61GPrime.ZeroComparisons` that
the fibre cover actually consumes (R102) need only the *component* of the small ball reached by the
inverse chart (`freeNear`). This file proves that component form with **no fibre clause**:

* `exists_component_subset_cfCollar` / `exists_component_subset_ownCollar`: the collar lemma
  `exists_component_subset_of_collar` for the counterflow chart `Ψ_s⁻¹ = revChartInv w s` and for the
  own inverse Loewner map `F_r`;
* `CfAccessNP`, `SeedAccessNP`, `OwnCollarPointNP`: COMPARE's accesses without the fibre clause
  (`CfAccess.toNP`, `OwnCollarPoint.toNP`);
* **`cfComponentGerm_of_access`**, **`ownComponentGerm_of_access`**: almost surely on the selected
  records, at such a chart point `b`, the exact counterflow (index `.inr ()`) resp. own (index
  `.inl q`) clause of the component cover: landing point, `freeNear` containment of the zero-time
  marked set, landing limit and mean limit.

Deterministic in the access data (plus the landed a.s. facts of COMPARE's own proofs). R48: no
Theorem 1.2/1.3 input; R77: no post-contact kernel. Nothing here replaces a source statement.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar chiC fwdHull fwdMap fwdMapInv)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Nj
open Aux61SlitW Aux61SlitW.SourceSetting Aux61GAlign Aux61GChoice16 Aux61Restart Aux61FibData
open Aux61ChLoc LawUnique GlueCond Aux61R1C Aux61Asm2 Aux61GInst Aux61GR1F
open WangWu Cond44Ref Aux61GWord Aux61Cmp Aux61TwoS
open InteractingSLE.Theorem14.SB.FinRel
universe u

/-! ### The two charts -/

section Charts

variable {w : ℝ → ℝ} {γ : ℝ → ℂ} {s : ℝ}
  (hw : Continuous w) (hw0 : w 0 = 0) (hγ : IsLoewnerTrace w γ)

include hw hw0 hγ in
/-- **The counterflow collar form**: the component of `Ψ_s⁻¹ ζ` in the part of a small ball around
the physical landing point off the counterflow hull lies in the collar's target `D`. -/
theorem exists_component_subset_cfCollar (hs : 0 ≤ s) {D : Set ℂ} {ξ₀ δ x : ℝ}
    (hcol : MapsTo (revChartInv w s) (H ∩ ball (ξ₀ : ℂ) δ) D)
    (hfin : ∀ x' : ℝ, (x' : ℂ) ∈ ball (ξ₀ : ℂ) δ →
      x' ≠ 0 ∧ extendFrom H (fwdMapInv w s) (negInv (x' : ℂ)) ≠ 0)
    (hx : (x : ℂ) ∈ ball (ξ₀ : ℂ) δ) :
    ∃ ρ > 0, ∀ᶠ ζ in 𝓝[H] (x : ℂ),
      revChartInv w s ζ ∈ (H \ negInv '' fwdHull w s) ∩ ball (cfBdry w s x) ρ ∧
      connectedComponentIn ((H \ negInv '' fwdHull w s) ∩ ball (cfBdry w s x) ρ)
        (revChartInv w s ζ) ⊆ D := by
  have hRi := isConformalBijection_revChartInv hw hw0 hs
  refine exists_component_subset_of_collar (Ψ := revChart w s) (φ := cfBdry w s) hRi.1
    hRi.2.injOn hRi.2.mapsTo (fun z hz => ?_) (fun z hz => revChart_mem_H hw hs hz)
    (fun z hz => revChartInv_revChart hw hw0 hs hz) (fun ζ hζ => revChart_revChartInv hw hw0 hs hζ)
    hcol (fun a ha => ?_) hx ?_
  · exact (GlueImg.differentiableAt_revChart hw hs hz).continuousAt.continuousWithinAt
  · obtain ⟨h0, hF0⟩ := hfin a ha
    exact tendsto_revChartInv_cfBdry hw hw0 hγ hs h0 hF0
  · intro hmem
    rcases cfBdry_mem_hull_or_real hw hw0 hγ hs x with h | h
    · exact hmem.2 h
    · have h1 : (0 : ℝ) < (cfBdry w s x).im := hmem.1
      rw [show (cfBdry w s x).im = 0 from h] at h1
      exact lt_irrefl _ h1

include hw hw0 hγ in
/-- **The own collar form**: the component of `F_r ζ` in the part of a small ball around the
landing point `F̄_r(t)` off the own hull lies in the collar's target `D`. -/
theorem exists_component_subset_ownCollar {r : ℝ} (hr : 0 ≤ r) {D : Set ℂ} {δ t : ℝ}
    (hcol : MapsTo (fwdMapInv w r) (ball 0 δ ∩ H) D) (ht : |t| < δ) :
    ∃ ρ > 0, ∀ᶠ ζ in 𝓝[H] (t : ℂ),
      fwdMapInv w r ζ ∈ (H \ fwdHull w r) ∩ ball (extendFrom H (fwdMapInv w r) t) ρ ∧
      connectedComponentIn ((H \ fwdHull w r) ∩ ball (extendFrom H (fwdMapInv w r) t) ρ)
        (fwdMapInv w r ζ) ⊆ D := by
  have hF := isConformalBijection_fwdMapInv hw hw0 hr
  have hB := hγ.hasBdryLimits hw hw0 hr
  have hcol' : MapsTo (fwdMapInv w r) (H ∩ ball ((0 : ℝ) : ℂ) δ) D := fun z hz =>
    hcol ⟨by simpa using hz.2, hz.1⟩
  have htb : (t : ℂ) ∈ ball ((0 : ℝ) : ℂ) δ := by
    rw [Complex.ofReal_zero, mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    exact ht
  exact exists_component_subset_of_collar (Ψ := fwdMap w r)
    (φ := fun a : ℝ => extendFrom H (fwdMapInv w r) a) hF.1 hF.2.injOn hF.2.mapsTo
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hw hr).continuousOn
    (QuantumZipper.FwdHolo.mapsTo_fwdMap hw hr)
    (fun z hz => QuantumZipper.RS.fwdMapInv_fwdMap hw hw0 hr hz)
    (fun ζ hζ => QuantumZipper.RS.fwdMap_fwdMapInv hw hw0 hr hζ) hcol'
    (fun a _ => hB.tendsto (mem_Hbar_of_im_eq_zero (by simp))) htb
    (extendFrom_notMem_compl_fwdHull hw hw0 hγ hr t)

end Charts

/-! ### Accesses without the fibre clause -/

variable {S : SourceSetting.{u}} {F : SourceRestartData S.Ω S.nL S.nR}

/-- **A counterflow collar access without the fibre clause**: `Aux61Cmp.CfAccess` minus "every
physical preimage of the landing point lies in the collar". -/
def CfAccessNP (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR) (i : F.ι)
    (p : S.Ω × HistorySpace 0 0) (b : ℝ) : Prop :=
  ∃ ξ₀ δ x : ℝ, 0 < δ ∧ (x : ℂ) ∈ ball (ξ₀ : ℂ) δ ∧
    MapsTo (revChartInv (cfW S p) (rationalTime S.s)) (H ∩ ball (ξ₀ : ℂ) δ)
      ((S.marksData F).chart i p).dom ∧
    (∀ x' : ℝ, (x' : ℂ) ∈ ball (ξ₀ : ℂ) δ → x' ≠ 0 ∧
      extendFrom H (fwdMapInv (cfW S p) (rationalTime S.s)) (negInv (x' : ℂ)) ≠ 0 ∧
      cfBdry (cfW S p) (rationalTime S.s) x' ≠ 1) ∧
    Tendsto (fun z => ((S.marksData F).chart i p).1 (revChartInv (cfW S p) (rationalTime S.s) z))
      (𝓝[H] (x : ℂ)) (𝓝 (b : ℂ)) ∧
    b ≠ 0 ∧ b ∉ (F.data i).JR ∧
    x ∉ returnedCfJumps S.κ (sourceCounterBoundary S) (forceJumpFinset S.xL S.xR)
      (rationalTime S.s) p.2 ∧
    ∀ phase : ℝ, Tendsto (fun z => ((S.marksData F).chart i p).2.2 (((S.marksData F).chart i p).2.1 z) -
        (GlueImg.logDerivPsi (cfW S p) (rationalTime S.s) (((S.marksData F).chart i p).2.1 z)).im)
        (𝓝[H] (b : ℂ)) (𝓝 phase) →
      (F.data i).bR b = returnedCfData S.κ (sourceCounterBoundary S)
        (forceJumpFinset S.xL S.xR) (rationalTime S.s) p.2 x + S.θ * chiC S.κ + chiC S.κ * phase

theorem CfAccess.toNP {i : F.ι} {p : S.Ω × HistorySpace 0 0} {b : ℝ} (h : CfAccess S F i p b) :
    CfAccessNP S F i p b := by
  obtain ⟨ξ₀, δ, x, hδ, hx, hcol, hfin, -, hxb, hb0, hbJ, hξ, hword⟩ := h
  exact ⟨ξ₀, δ, x, hδ, hx, hcol, hfin, hxb, hb0, hbJ, hξ, hword⟩

/-- **A free-collar access without the fibre clause**: `Aux61Cmp.SeedAccess` minus "every physical
preimage of `F̄_r(t)` lies in the collar". -/
def SeedAccessNP (W : ℝ → ℝ) (r : ℝ) (c : Chart) (t b : ℝ) : Prop :=
  ∃ δ > 0, |t| < δ ∧ MapsTo (fwdMapInv W r) (ball 0 δ ∩ H) c.dom ∧
    (∀ x : ℝ, |x| < δ → extendFrom H (fwdMapInv W r) x ≠ 1) ∧
    Tendsto (fun z => c.1 (fwdMapInv W r z)) (𝓝[H] (t : ℂ)) (𝓝 (b : ℂ))

theorem SeedAccess.toNP {W : ℝ → ℝ} {r : ℝ} {c : Chart} {t b : ℝ} (h : SeedAccess W r c t b) :
    SeedAccessNP W r c t b := by
  obtain ⟨δ, hδ, ht, hcol, hone, -, htb⟩ := h
  exact ⟨δ, hδ, ht, hcol, hone, htb⟩

/-- **The own side without the fibre clause** (`Aux61Cmp.OwnCollarPoint` with `SeedAccessNP`). -/
def OwnCollarPointNP (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR) (i : F.ι)
    (p : S.Ω × HistorySpace 0 0) (b : ℝ) : Prop :=
  ∃ t : ℝ, SeedAccessNP (fun s : ℝ => S.own.W s.toNNReal p.1) (F.start i)
      ((S.marksData F).chart i p) t b ∧
    (b = 0 ∨ (b ∉ (F.data i).JR ∧
      t ∉ Impl.forceJumpSet (Ito.weightWord S.ρL S.ρR) (ownVL S F i p) (ownVR S F i p) ∧
      (F.data i).bR b = Impl.forceBoundaryData (F.data i).κ (Ito.weightWord S.ρL S.ρR)
        (ownVL S F i p) (ownVR S F i p) t))

theorem OwnCollarPoint.toNP {i : F.ι} {p : S.Ω × HistorySpace 0 0} {b : ℝ}
    (h : OwnCollarPoint S F i p b) : OwnCollarPointNP S F i p b := by
  obtain ⟨t, ht, hreg⟩ := h
  exact ⟨t, SeedAccess.toNP ht, hreg⟩

/-! ### The counterflow component germ -/

/-- The mean clause of the counterflow germ from a regular transition (the computation of
`Aux61Cmp.counterGerm_of_transition`, which needs no containment). -/
theorem cfMean_tendsto_of_transition {i : F.ι} {p : S.Ω × HistorySpace 0 0}
    (hc : ((S.marksData F).chart i p).IsConformal)
    (hsub : (((S.marksData F).chart i p).dom : Set ℂ) ⊆ H \ cfHullQ (rationalTime S.s) p.2)
    {b ξ phase : ℝ} (hb0 : b ≠ 0) (hbJ : b ∉ (F.data i).JR)
    (hξ : ξ ∉ returnedCfJumps S.κ (sourceCounterBoundary S) (forceJumpFinset S.xL S.xR)
      (rationalTime S.s) p.2)
    (htransition : Tendsto (fun z => revChart (cfW S p) (rationalTime S.s)
      (((S.marksData F).chart i p).2.1 z)) (𝓝[H] (b : ℂ)) (𝓝[H] (ξ : ℂ)))
    (hphase : Tendsto (fun z => ((S.marksData F).chart i p).2.2 (((S.marksData F).chart i p).2.1 z) -
      (GlueImg.logDerivPsi (cfW S p) (rationalTime S.s) (((S.marksData F).chart i p).2.1 z)).im)
      (𝓝[H] (b : ℂ)) (𝓝 phase))
    (hword : (F.data i).bR b = returnedCfData S.κ (sourceCounterBoundary S)
      (forceJumpFinset S.xL S.xR) (rationalTime S.s) p.2 ξ + S.θ * chiC S.κ + chiC S.κ * phase) :
    Tendsto (fun z => sourceReferenceMean S (.inr ()) p (((S.marksData F).chart i p).2.1 z) +
      (S.marksData F).scale + (S.marksData F).constant * ((S.marksData F).chart i p).2.2
        (((S.marksData F).chart i p).2.1 z) - Aux61GlueK.refMean0 ((S.marksData F).data i) z)
      (𝓝[H] (b : ℂ)) (𝓝 0) := by
  have hheight := (tendsto_returnedCfMean S.κ (sourceCounterBoundary S)
    (forceJumpFinset S.xL S.xR) (rationalTime S.s) p.2 hξ).comp htransition
  have ht := ((hheight.add_const (S.θ * chiC S.κ)).add (hphase.const_mul (chiC S.κ))).sub
    (Aux61GNext.tendsto_refMean0_regular (F.data i) hb0 hbJ)
  rw [← hword, sub_self] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have he := CrossCond.Theta.cfMeanQ_add_eq_retMean_addT S.κ_pos S.θ S.ρL S.ρR S.xL S.xR
    (Impl.isBoundedHarmonicExtension_forceExt S.κ (Ito.weightWord S.ρL S.ρR) S.xL S.xR)
    (sourceCounterExtension_spec S) (rationalTime S.s) p.2 (hsub (hc.inv_mem_dom hz))
  change _ = sourceReferenceMean S (.inr ()) p (((S.marksData F).chart i p).2.1 z) + 0 +
    chiC S.κ * ((S.marksData F).chart i p).2.2 (((S.marksData F).chart i p).2.1 z) -
    Aux61GlueK.refMean0 (F.data i) z
  have he' : cfMeanQ S.κ (sourceCounterBoundary S) (forceJumpFinset S.xL S.xR)
      (sourceCounterExtension S) (rationalTime S.s) p.2 (((S.marksData F).chart i p).2.1 z) +
      Impl.forceExt S.κ (Ito.weightWord S.ρL S.ρR) S.xL S.xR (((S.marksData F).chart i p).2.1 z) +
      chiC S.κ * (GlueImg.logDerivPsi (cfW S p) (rationalTime S.s)
        (((S.marksData F).chart i p).2.1 z)).im =
      GlueImg.retMean S.κ (cfU S.κ (sourceCounterBoundary S) (forceJumpFinset S.xL S.xR)
        (rationalTime S.s) (cfStop (rationalTime S.s) p.2))
        (revChart (cfW S p) (rationalTime S.s) (((S.marksData F).chart i p).2.1 z)) +
      S.θ * chiC S.κ := he
  simp only [sourceReferenceMean, Function.comp_apply]
  linarith only [he']

/-- **The counterflow component germ** (pinch-free): almost surely on the selected records, at a
chart point with a counterflow collar access without the fibre clause, the counterflow clause of
the component cover holds — landing point in the counterflow hull or on `ℝ`, `freeNear` containment
of the zero-time marked set, landing limit and mean limit. -/
theorem cfComponentGerm_of_access
    (hR : SourceRestartFacts F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life
      (μ := S.μ) S.κ) (i : F.ι)
    (hgeometry : ∀ᵐ p ∂S.μ, p ∈ F.event i →
      SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
        (cfHullQ (rationalTime S.s) p.2) (F.start i)
        (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p))
    (hcf : ∀ᵐ p ∂S.μ, cfW S p 0 = 0 ∧ ∃ γ : ℝ → ℂ, IsLoewnerTrace (cfW S p) γ) :
    ∀ᵐ p ∂S.μ, (S.marksData F).Z i p ∈ (S.marksData F).B i → ∀ b : ℝ, CfAccessNP S F i p b →
      ∃ z₀ : ℂ, z₀ ∈ sourceReferenceSet S (.inr ()) p ∪ {z : ℂ | z.im = 0} ∧
        (∃ r > 0, ∀ᶠ z in 𝓝[H] (b : ℂ), ((S.marksData F).chart i p).2.1 z ∈
          freeNear ((S.marksData F).baseSets i 0 p) (sourceReferenceSet S (.inr ()) p) z₀ r) ∧
        Tendsto ((S.marksData F).chart i p).2.1 (𝓝[H] (b : ℂ)) (𝓝 z₀) ∧
        Tendsto (fun z => sourceReferenceMean S (.inr ()) p (((S.marksData F).chart i p).2.1 z) +
          (S.marksData F).scale + (S.marksData F).constant * ((S.marksData F).chart i p).2.2
            (((S.marksData F).chart i p).2.1 z) - Aux61GlueK.refMean0 ((S.marksData F).data i) z)
          (𝓝[H] (b : ℂ)) (𝓝 0) := by
  filter_upwards [hgeometry, S.physical_path, hR.physical_stop i, source_zero_alive_iff S F hR i, hcf]
    with p hg hp hstop halive hcfp hB b hacc
  obtain ⟨hw0, γ, hγ⟩ := hcfp
  have hw : Continuous (cfW S p) := Sec4.continuous_rpath_regPath _
  have hs : (0 : ℝ) ≤ (rationalTime S.s : ℝ) := NNReal.coe_nonneg _
  have hsel : sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈ F.selected i := hB
  have he : p ∈ F.event i := (hstop hsel).1
  have hlive : p ∈ liveEv ((S.marksData F).Z i) ((S.marksData F).B i) ((S.marksData F).code i) 0 :=
    ⟨hB, by rw [ENNReal.coe_zero]; exact halive.2 hsel⟩
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
  obtain ⟨ξ₀, δ, x, hδ, hx, hcol, hfin, hxb, hb0, hbJ, hξ, hword⟩ := hacc
  obtain ⟨⟨n, hn⟩, hland⟩ := cfCollar_limits hw hw0 hγ hs hc hsubK hBh hscale hδ hcol hfin ha
    hgeo.lift hx hxb
  have hT := tendsto_cfTransition hw hw0 hγ hs hc hsubK hBh hscale hδ hcol hfin hx hxb
  have hz₀ : cfBdry (cfW S p) (rationalTime S.s) x ∈
      cfHullQ (rationalTime S.s) p.2 ∪ {z : ℂ | z.im = 0} := by
    rcases cfBdry_mem_hull_or_real hw hw0 hγ hs x with h | h
    · exact Or.inl (hKsub h)
    · exact Or.inr h
  obtain ⟨ρ, hρ, hcomp⟩ := exists_component_subset_cfCollar hw hw0 hγ hs hcol
    (fun x' hx' => ⟨(hfin x' hx').1, (hfin x' hx').2.1⟩) hx
  refine ⟨cfBdry (cfW S p) (rationalTime S.s) x, hz₀, ⟨ρ, hρ, ?_⟩, hland,
    cfMean_tendsto_of_transition hc hsub hb0 hbJ hξ hT hn (hword _ hn)⟩
  filter_upwards [hT.eventually hcomp, self_mem_nhdsWithin] with z hz hzH
  have hdom : ((S.marksData F).chart i p).2.1 z ∈ ((S.marksData F).chart i p).dom :=
    hc.inv_mem_dom hzH
  rw [revChartInv_revChart hw hw0 hs (hsubK hdom)] at hz
  obtain ⟨⟨-, hball⟩, hsubD⟩ := hz
  refine ⟨⟨hsub hdom, hball⟩, ?_⟩
  rw [baseSets_zero_eq S F hc hlive, Set.disjoint_left]
  intro v hv hvB
  have hmono : (H \ sourceReferenceSet S (.inr ()) p) ∩ ball (cfBdry (cfW S p) (rationalTime S.s) x) ρ ⊆
      (H \ negInv '' fwdHull (cfW S p) (rationalTime S.s)) ∩
        ball (cfBdry (cfW S p) (rationalTime S.s) x) ρ :=
    inter_subset_inter_left _ (sdiff_subset_sdiff_right hKsub)
  exact hvB.2 (hsubD (connectedComponentIn_mono _ hmono hv))

/-! ### The own component germ -/

/-- **The own component germ** (pinch-free): almost surely on the selected records, at an own
collar point without the fibre clause, the own clause (index `.inl q`) of the component cover holds
— the landing point `F̄_r(t)`, `freeNear` containment of the zero-time marked set, landing limit and
the charted own germ (the landed seed theorem at `b = 0`, the collar theorem elsewhere). -/
theorem ownComponentGerm_of_access
    (hR : SourceRestartFacts F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life
      (μ := S.μ) S.κ) (i : F.ι) (q : ℚ) (hq : F.start i = rationalTime q)
    (hleft : PiecewiseConstantBoundaryData.leftLim (F.data i).bR 0 = -sleLambda (F.data i).κ)
    (hright : PiecewiseConstantBoundaryData.rightLim (F.data i).bR 0 = sleLambda (F.data i).κ)
    (hgeometry : ∀ᵐ p ∂S.μ, p ∈ F.event i →
      SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
        (cfHullQ (rationalTime S.s) p.2) (F.start i)
        (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)) :
    ∀ᵐ p ∂S.μ, (S.marksData F).Z i p ∈ (S.marksData F).B i → ∀ b : ℝ, OwnCollarPointNP S F i p b →
      ∃ z₀ : ℂ, z₀ ∈ sourceReferenceSet S (pastReferenceIndex q (.inl q)) p ∪ {z : ℂ | z.im = 0} ∧
        (∃ r > 0, ∀ᶠ z in 𝓝[H] (b : ℂ), ((S.marksData F).chart i p).2.1 z ∈
          freeNear ((S.marksData F).baseSets i 0 p)
            (sourceReferenceSet S (pastReferenceIndex q (.inl q)) p) z₀ r) ∧
        Tendsto ((S.marksData F).chart i p).2.1 (𝓝[H] (b : ℂ)) (𝓝 z₀) ∧
        Tendsto (fun z => sourceReferenceMean S (pastReferenceIndex q (.inl q)) p
          (((S.marksData F).chart i p).2.1 z) + (S.marksData F).scale +
          (S.marksData F).constant * ((S.marksData F).chart i p).2.2
            (((S.marksData F).chart i p).2.1 z) - Aux61GlueK.refMean0 ((S.marksData F).data i) z)
          (𝓝[H] (b : ℂ)) (𝓝 0) := by
  filter_upwards [hgeometry, S.physical_path, source_own_seed_germ S F hR i q hq hleft hright hgeometry,
    hR.physical_stop i, source_zero_alive_iff S F hR i] with p hg hp hseed hstop halive hB b hb
  have hsel : sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈ F.selected i := hB
  have he : p ∈ F.event i := (hstop hsel).1
  have hlive : p ∈ liveEv ((S.marksData F).Z i) ((S.marksData F).B i) ((S.marksData F).code i) 0 :=
    ⟨hB, by rw [ENNReal.coe_zero]; exact halive.2 hsel⟩
  have hpi : pastReferenceIndex q (.inl q) = .inl q := by simp only [pastReferenceIndex, min_self]
  rw [hpi]
  have hW := hp.1.continuous_rpath
  have hW0 : (fun t : ℝ => S.own.W t.toNNReal p.1) 0 = 0 := by
    simpa only [Real.toNNReal_zero] using hp.1.2.1
  have hc := (hR.spec i).conf p he
  have hgeo := hg he
  have hsub : (((S.marksData F).chart i p).dom : Set ℂ) ⊆
      H \ fwdHull (fun t : ℝ => S.own.W t.toNNReal p.1) (F.start i) := by
    rw [WangWu.fwdHull_eq_image_Ioc hp.2.1 hp.2.2 (F.start i).coe_nonneg]
    intro z hz
    exact ⟨(hgeo.retained hz).1, fun hP => (hgeo.retained hz).2
      (Or.inr (image_mono Ioc_subset_Icc_self hP))⟩
  have hBh := isHPHull_stripTargetHull ((S.marksData F).chart i p).dom.isOpen
    hgeo.simply hc.dom_subset hgeo.target
  obtain ⟨a, ξ, ha, hscale⟩ := hgeo.scale hW hW0 hp.2.1 hp.2.2 hc
  have hr0 : (0 : ℝ) < F.start i := NNReal.coe_pos.2 hgeo.start_pos
  have hh : sourceReferenceSet S (.inl q) p =
      fwdHull (fun t : ℝ => S.own.W t.toNNReal p.1) (F.start i) := by
    have h := Aux50Hit.regHull_stopHistory_cstop hp.1 (rationalTime q)
    change hullAt (rationalTime q) (killedHistory S.own.W S.own.VL S.own.VR S.life p.1) =
      fwdHull (fun t : ℝ => S.own.W t.toNNReal p.1) (rationalTime q) at h
    rw [hq]
    exact h
  obtain ⟨t, ⟨δ, hδ, ht, hcol, hone, htb⟩, hreg⟩ := hb
  refine ⟨extendFrom H (fwdMapInv (fun t : ℝ => S.own.W t.toNNReal p.1) (F.start i)) t, ?_, ?_, ?_, ?_⟩
  · rw [hh]
    exact extendFrom_mem_hull_or_real hW hW0 hp.2.1 hr0 t
  · obtain ⟨ρ, hρ, hcomp⟩ := exists_component_subset_ownCollar hW hW0 hp.2.1 hr0.le hcol ht
    refine ⟨ρ, hρ, ?_⟩
    have hT := tendsto_transition_collar hW hW0 hp.2.1 hr0 hc hsub hBh hscale hδ hcol hone ht htb
    filter_upwards [hT.eventually hcomp, self_mem_nhdsWithin] with z hz hzH
    have hdom := hc.inv_mem_dom hzH
    rw [QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hr0.le (hsub hdom)] at hz
    obtain ⟨⟨-, hball⟩, hsubD⟩ := hz
    rw [hh]
    refine ⟨⟨hsub hdom, hball⟩, ?_⟩
    rw [baseSets_zero_eq S F hc hlive, Set.disjoint_left]
    intro v hv hvB
    exact hvB.2 (hsubD hv)
  · exact tendsto_inv_collar hW hW0 hp.2.1 hr0 hc hsub hBh hscale hδ hcol hone ht htb
  · by_cases hb0 : b = 0
    · subst hb0
      rw [Complex.ofReal_zero]
      exact hseed he
    · obtain ⟨hbJ, htJ, hheight⟩ := hreg.resolve_left hb0
      have hm := tendsto_charted_couplingMean_sub_refMean0_collar hW hW0 hp.2.1 hr0 hc hsub hBh
        hscale hδ hcol hone ha (hp.2.2.inj.mono Icc_subset_Ici_self)
        (fun u hu => hp.2.2.mem_H u hu.1) hgeo.lift (F.data i) (Ito.weightWord S.ρL S.ρR)
        (ownVL S F i p) (ownVR S F i p) ht htb htJ hb0 hbJ hheight
      rw [hR.kappa i] at hm
      change Tendsto (fun z =>
        couplingMean S.κ (fun t : ℝ => S.own.W t.toNNReal p.1) (rationalTime q)
          (sourcePatchExtension S.own.W S.own.VL S.own.VR S.κ S.ρL S.ρR q p.1)
          (((S.marksData F).chart i p).2.1 z) + 0 + chiC S.κ *
          ((S.marksData F).chart i p).2.2 (((S.marksData F).chart i p).2.1 z) -
          Aux61GlueK.refMean0 (F.data i) z) (𝓝[H] (b : ℂ)) (𝓝 0)
      have heq : Ito.rpath (fun t => S.own.W t p.1) = (fun t : ℝ => S.own.W t.toNNReal p.1) := rfl
      rw [heq] at hm
      simp only [sourcePatchExtension, ← hq, add_zero]
      exact hm

end InteractingSLE.Sec5.Aux61Nj
