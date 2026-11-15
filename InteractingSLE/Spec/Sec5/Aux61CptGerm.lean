/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CmpCfGerm
import InteractingSLE.Spec.Sec5.Aux61GChoice16Compare
import InteractingSLE.Spec.Sec5.Aux61GPrimeCompare

/-!
# Component (prime-end) counterflow germs: pinch points are not exceptional

Packet PROVE-AUX61-CAPTURE (ruling R103). COMPARE's counterflow access `Aux61Cmp.CfAccess` asks that every
physical preimage of the landing's physical point lie in the counterflow collar (`hpre`). That clause is only used for
the *full-ball* containment `exists_ball_inter_subset_dom_cf`, and it fails at pinch points of the counterflow
boundary (two prime ends over one physical point). The comparison record actually consumed by the fibre cover,
`Aux61GPrime.ZeroComparisons`, is in *component* form (`freeNear`): only the component of the small ball reached by
the inverse chart must avoid the marked set. This is the source's "protected prime-end collars" (spec p. 302: "an old
common physical contact in an interval is not an exceptional point").

* `mem_freeNear_of_component`: if the chart domain is a component of `ℍ ∖ (K ∪ η[0, r])` and a ball about `z₀` misses
  the own prefix `η[0, r]`, every domain point of the ball is a `freeNear` point. No pinch condition is needed.
* `mem_freeNear_of_ball_subset`: the full-ball clause gives the component clause (as in `Aux61Cmp.toComponent`).
* `CfAccessC`: `CfAccess` with the preimage clause replaced by "the physical point is off the closed own prefix".
* `counterGermC_of_cfAccessC`: a.s. on the selected records a component access is a component counterflow germ.
* `sourceComponentComparisons`: the component comparison record from component (or full-ball) germs.

R48: no Theorem 1.2/1.3 input; R77: no post-contact kernel. Nothing here replaces a source theorem.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H chiC fwdHull fwdMapInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Cpt
open Aux61SlitW Aux61SlitW.SourceSetting Aux61GAlign Aux61ChLoc LawUnique GlueCond
open WangWu Cond44Ref Aux61GWord Aux61Restart Aux61SlitWX Aux61Asm2 Aux61Cmp Aux61GChoice16
open Aux61Marks Aux61ULoc LocalSets WholeField
open InteractingSLE.Theorem14.SB.FinRel (freeNear)
universe u

/-! ### Two deterministic `freeNear` criteria -/

/-- **Component criterion.** If the chart domain is a component of the retained domain `ℍ ∖ (K ∪ η[0, r])` and the
ball `B(z₀, ρ)` misses the own prefix, then every domain point of the ball is `freeNear` the complement of the
domain: its component in `(ℍ ∖ K) ∩ B(z₀, ρ)` stays inside the domain. -/
theorem mem_freeNear_of_component {K : Set ℂ} {η : ℝ → ℂ} {r : ℝ} {b' z₀ w : ℂ} {ρ : ℝ} {dom : Set ℂ}
    (hdom : dom = restartComponent K η r b') (hρ : Disjoint (ball z₀ ρ) (η '' Icc 0 r))
    (hw : w ∈ dom) (hwb : w ∈ ball z₀ ρ) :
    w ∈ freeNear (H \ dom) K z₀ ρ := by
  have hw' : w ∈ connectedComponentIn (retainedDomain K η r) b' := by
    rw [hdom] at hw
    exact hw
  have hwR : w ∈ retainedDomain K η r := connectedComponentIn_subset _ _ hw'
  have hmem : w ∈ (H \ K) ∩ ball z₀ ρ := ⟨⟨hwR.1, fun hK => hwR.2 (Or.inl hK)⟩, hwb⟩
  refine ⟨hmem, ?_⟩
  have hCsub : connectedComponentIn ((H \ K) ∩ ball z₀ ρ) w ⊆ retainedDomain K η r := by
    intro v hv
    have hv' := connectedComponentIn_subset _ _ hv
    refine ⟨hv'.1.1, fun hvK => ?_⟩
    rcases hvK with hvK | hvη
    · exact hv'.1.2 hvK
    · exact Set.disjoint_left.1 hρ hv'.2 hvη
  have hCd : connectedComponentIn ((H \ K) ∩ ball z₀ ρ) w ⊆ dom := by
    have h1 := (isPreconnected_connectedComponentIn).subset_connectedComponentIn
      (mem_connectedComponentIn hmem) hCsub
    rw [← connectedComponentIn_eq hw'] at h1
    rw [hdom]
    exact h1
  exact Set.disjoint_left.2 fun v hv hv' => hv'.2 (hCd hv)

/-- **Full-ball criterion.** A full-ball containment of the marked set in the patch gives the component clause at
every point of `ℍ ∖ P` in the ball. -/
theorem mem_freeNear_of_ball_subset {A P : Set ℂ} {z₀ w : ℂ} {ρ : ℝ}
    (hsub : A ∩ ball z₀ ρ ⊆ P) (hwH : w ∈ H) (hwP : w ∉ P) (hwb : w ∈ ball z₀ ρ) :
    w ∈ freeNear A P z₀ ρ := by
  refine ⟨⟨⟨hwH, hwP⟩, hwb⟩, Set.disjoint_left.2 fun v hv hvA => ?_⟩
  have hv' := connectedComponentIn_subset _ _ hv
  exact hv'.1.2 (hsub ⟨hvA, hv'.2⟩)

variable {S : SourceSetting.{u}} {F : SourceRestartData S.Ω S.nL S.nR}

/-! ### The component counterflow access -/

/-- **A component counterflow collar access** of the chart point `b`: COMPARE's `CfAccess` with the prime-end preimage
clause replaced by "a ball about the physical point misses the own prefix". -/
def CfAccessC (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR) (i : F.ι)
    (p : S.Ω × HistorySpace 0 0) (b : ℝ) : Prop :=
  ∃ ξ₀ δ x : ℝ, 0 < δ ∧ (x : ℂ) ∈ ball (ξ₀ : ℂ) δ ∧
    MapsTo (revChartInv (cfW S p) (rationalTime S.s)) (H ∩ ball (ξ₀ : ℂ) δ)
      ((S.marksData F).chart i p).dom ∧
    (∀ x' : ℝ, (x' : ℂ) ∈ ball (ξ₀ : ℂ) δ → x' ≠ 0 ∧
      extendFrom H (fwdMapInv (cfW S p) (rationalTime S.s)) (negInv (x' : ℂ)) ≠ 0 ∧
      cfBdry (cfW S p) (rationalTime S.s) x' ≠ 1) ∧
    (∃ ρ > 0, Disjoint (ball (cfBdry (cfW S p) (rationalTime S.s) x) ρ)
      ((fun t : ℝ => S.path p.1 t.toNNReal) '' Icc 0 (F.start i : ℝ))) ∧
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

/-- **The counterflow clause in component form**: the germ of the zero-time comparison cover with the counterflow
reference, the full-ball containment replaced by the `freeNear` clause. -/
def CounterGermC (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR) (i : F.ι)
    (p : S.Ω × HistorySpace 0 0) (b : ℝ) : Prop :=
  ∃ z₀ : ℂ, z₀ ∈ sourceReferenceSet S (.inr ()) p ∪ {z : ℂ | z.im = 0} ∧
    (∃ r > 0, ∀ᶠ z in 𝓝[H] (b : ℂ), ((S.marksData F).chart i p).2.1 z ∈
      freeNear ((S.marksData F).baseSets i 0 p) (sourceReferenceSet S (.inr ()) p) z₀ r) ∧
    Tendsto ((S.marksData F).chart i p).2.1 (𝓝[H] (b : ℂ)) (𝓝 z₀) ∧
    Tendsto (fun z => sourceReferenceMean S (.inr ()) p (((S.marksData F).chart i p).2.1 z) +
      (S.marksData F).scale + (S.marksData F).constant * ((S.marksData F).chart i p).2.2
        (((S.marksData F).chart i p).2.1 z) - Aux61GlueK.refMean0 ((S.marksData F).data i) z)
      (𝓝[H] (b : ℂ)) (𝓝 0)

/-- **The counterflow mean germ from a regular transition** (the mean half of `Aux61Cmp.counterGerm_of_transition`,
which needs no containment clause). -/
theorem tendsto_counterMean_of_transition {i : F.ι} {p : S.Ω × HistorySpace 0 0}
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

/-- **Component counterflow accesses are component counterflow germs**, almost surely on the selected records, given
the chart-domain component identity. No prime-end preimage (pinch) condition is used. -/
theorem counterGermC_of_cfAccessC
    (hR : SourceRestartFacts F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life
      (μ := S.μ) S.κ) (i : F.ι)
    (hgeometry : ∀ᵐ p ∂S.μ, p ∈ F.event i →
      SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
        (cfHullQ (rationalTime S.s) p.2) (F.start i)
        (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p))
    (hdomain : ∀ᵐ p ∂S.μ, p ∈ F.event i → ∃ b' : ℂ,
      ((sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom : Set ℂ) =
        restartComponent (cfHullQ (rationalTime S.s) p.2) (fun t : ℝ => S.path p.1 t.toNNReal)
          (F.start i) b')
    (hcf : ∀ᵐ p ∂S.μ, cfW S p 0 = 0 ∧ ∃ γ : ℝ → ℂ, IsLoewnerTrace (cfW S p) γ) :
    ∀ᵐ p ∂S.μ, (S.marksData F).Z i p ∈ (S.marksData F).B i → ∀ b : ℝ,
      CfAccessC S F i p b → CounterGermC S F i p b := by
  filter_upwards [hgeometry, hdomain, S.physical_path, hR.physical_stop i,
    source_zero_alive_iff S F hR i, hcf] with p hg hdom hp hstop halive hcfp hB b hacc
  obtain ⟨hw0, γ, hγ⟩ := hcfp
  have hw : Continuous (cfW S p) := Sec4.continuous_rpath_regPath _
  have hs : (0 : ℝ) ≤ (rationalTime S.s : ℝ) := NNReal.coe_nonneg _
  have hsel : sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈ F.selected i := hB
  have he : p ∈ F.event i := (hstop hsel).1
  have hlive : p ∈ liveEv ((S.marksData F).Z i) ((S.marksData F).B i) ((S.marksData F).code i) 0 :=
    ⟨hB, by rw [ENNReal.coe_zero]; exact halive.2 hsel⟩
  have hc : ((S.marksData F).chart i p).IsConformal := (hR.spec i).conf p he
  have hgeo := hg he
  obtain ⟨b', hb'⟩ := hdom he
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
  obtain ⟨ξ₀, δ, x, hδ, hx, hcol, hfin, ⟨ρ, hρ, hoff⟩, hxb, hb0, hbJ, hξ, hword⟩ := hacc
  obtain ⟨⟨n, hn⟩, hland⟩ := cfCollar_limits hw hw0 hγ hs hc hsubK hBh hscale hδ hcol hfin ha
    hgeo.lift hx hxb
  have hT := tendsto_cfTransition hw hw0 hγ hs hc hsubK hBh hscale hδ hcol hfin hx hxb
  have hz₀ : cfBdry (cfW S p) (rationalTime S.s) x ∈
      sourceReferenceSet S (.inr ()) p ∪ {z : ℂ | z.im = 0} := by
    rcases cfBdry_mem_hull_or_real hw hw0 hγ hs x with h | h
    · exact Or.inl (hKsub h)
    · exact Or.inr h
  refine ⟨_, hz₀, ⟨ρ, hρ, ?_⟩, hland,
    tendsto_counterMean_of_transition hc hsub hb0 hbJ hξ hT hn (hword _ hn)⟩
  have hball : ∀ᶠ z in 𝓝[H] (b : ℂ), ((S.marksData F).chart i p).2.1 z ∈
      ball (cfBdry (cfW S p) (rationalTime S.s) x) ρ :=
    hland (isOpen_ball.mem_nhds (mem_ball_self hρ))
  filter_upwards [hball, self_mem_nhdsWithin] with z hzb hzH
  rw [baseSets_zero_eq S F hc hlive]
  exact mem_freeNear_of_component hb' hoff (hc.inv_mem_dom hzH) hzb

/-! ### The component comparison record -/

/-- **The component comparison record from component or full-ball germs** (the component twin of
`Aux61GChoice16.source_comparisons_of_past_germs`): every mean and marked-union field is built from the actual source
coupling and retained references; at each window point a germ may come with a full-ball or a component containment. -/
theorem sourceComponentComparisons
    (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR)
    (hR : SourceRestartFacts F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life
      (μ := S.μ) S.κ) (i : F.ι) (q : ℚ) (hq : F.start i = rationalTime q)
    (hsets : Measurable[(S.marksData F).baseMarks i 0, hittingSigma]
      ((S.marksData F).baseSets i 0))
    (hretained : ∀ᵐ p ∂S.μ, p ∈ F.event i →
      (((S.marksData F).chart i p).dom : Set ℂ) ⊆ H \ (cfHullQ (rationalTime S.s) p.2 ∪
        (fun t : ℝ => S.path p.1 t.toNNReal) '' Icc 0 (F.start i : ℝ)))
    (hdom : ∀ᵐ x ∂S.μ, (S.marksData F).Z i x ∈ (S.marksData F).B i → ∀ z ∈ H,
      ((S.marksData F).chart i x).2.1 z ∈ H ∧
        ((S.marksData F).chart i x).2.1 z ∉ (S.marksData F).baseSets i 0 x)
    (hgerms : ∀ᵐ x ∂S.μ, (S.marksData F).Z i x ∈ (S.marksData F).B i →
      ∀ b ∈ ((S.marksData F).data i).O₀,
      ∃ (j : SourceReferenceIndex) (z₀ : ℂ),
        z₀ ∈ sourceReferenceSet S (pastReferenceIndex q j) x ∪ {z : ℂ | z.im = 0} ∧
        ((∃ r > 0, (S.marksData F).baseSets i 0 x ∩ ball z₀ r ⊆
            sourceReferenceSet S (pastReferenceIndex q j) x) ∨
          ∃ r > 0, ∀ᶠ z in 𝓝[H] (b : ℂ), ((S.marksData F).chart i x).2.1 z ∈
            freeNear ((S.marksData F).baseSets i 0 x) (sourceReferenceSet S (pastReferenceIndex q j) x) z₀ r) ∧
        Tendsto ((S.marksData F).chart i x).2.1 (𝓝[H] (b : ℂ)) (𝓝 z₀) ∧
        Tendsto (fun z => sourceReferenceMean S (pastReferenceIndex q j) x
          (((S.marksData F).chart i x).2.1 z) + (S.marksData F).scale +
          (S.marksData F).constant * ((S.marksData F).chart i x).2.2
            (((S.marksData F).chart i x).2.1 z) - Aux61GlueK.refMean0 ((S.marksData F).data i) z)
          (𝓝[H] (b : ℂ)) (𝓝 0)) :
    Nonempty (Aux61GPrime.ZeroComparisons (S.marksData F) i) := by
  obtain ⟨g, hg, hh, hp⟩ := exists_source_reference_family S F i
  exact ⟨{
    index := SourceReferenceIndex
    countable := inferInstance
    patch := fun j => sourceReferenceSet S (pastReferenceIndex q j)
    patchMean := fun j => g (pastReferenceIndex q j)
    physicalMean := fun j => sourceReferenceMean S (pastReferenceIndex q j)
    union := pastReferenceUnion S F i q
    unionMarks := fun _ => (S.marksData F).baseMarks i 0
    event := fun _ => univ
    patch_measurable := fun j => measurable_sourceReferenceSet S (pastReferenceIndex q j)
    patch_closed := fun j => ae_of_all _ (sourceReferenceSet_closed S (pastReferenceIndex q j))
    patch_unbounded := fun j => ae_of_all _ (sourceReferenceSet_unbounded S (pastReferenceIndex q j))
    patch_mean := fun j => hg (pastReferenceIndex q j)
    physical_harmonic := fun j => hh (pastReferenceIndex q j)
    represents := fun j => hp (pastReferenceIndex q j)
    union_marks_le := fun _ => nullMarks_le
    union_measurable := fun j => past_union_recorded S F hR i q hq hsets j
    union_closed := fun j => past_union_closed S F hR i q j
    union_local := fun j => past_union_local S F hR i q hq hsets hretained j
    marks_le := fun _ => le_rfl
    set_recorded := fun _ => hsets
    set_subset := fun _ _ => inter_subset_left.trans subset_union_left
    patch_recorded := fun j => past_reference_recorded S F hR.chart_measurable i q hq j
    patch_subset := fun _ _ => inter_subset_left.trans subset_union_right
    event_measurable := fun _ => MeasurableSet.univ
    union_eq := fun j => by
      filter_upwards [past_union_eq S F hR i q hq hretained j] with x hx _
      exact hx
    cover := by
      have hsubs : ∀ᵐ x ∂S.μ, ∀ j : SourceReferenceIndex,
          sourceReferenceSet S (pastReferenceIndex q j) x ⊆ (S.marksData F).baseSets i 0 x :=
        ae_all_iff.2 fun j => past_reference_subset S F hR i q hq hretained j
      filter_upwards [hgerms, hdom, hsubs] with x hx hd hsx hB b hb
      obtain ⟨j, z₀, hz, hr, hl, hm⟩ := hx hB b hb
      refine ⟨j, z₀, mem_univ _, hz, ?_, hl, hm⟩
      rcases hr with ⟨r, hr0, hsub⟩ | hc
      · refine ⟨r, hr0, ?_⟩
        filter_upwards [hl (isOpen_ball.mem_nhds (mem_ball_self hr0)), self_mem_nhdsWithin]
          with z hzb hzH
        obtain ⟨hcH, hcA⟩ := hd hB z hzH
        exact mem_freeNear_of_ball_subset hsub hcH (fun hP => hcA (hsx j hP)) hzb
      · exact hc }⟩

/-! ### The normalized source: component comparisons from own collars and component counterflow accesses -/

section Normalized

variable (D : R1Restart S) (h : D.HasChart) (R : ReaderFacts D)

include R in
/-- **The `C` input of the normalized-capture fibre cover from component accesses** (the component twin of
`Aux61Cmp.normalizedComparisons`): the installed words' seed heights and, almost surely on each selected record,
every window point an own collar point or a *component* counterflow access. No prime-end preimage clause on the
counterflow side. -/
theorem normalizedComparisonsC_nonempty (hTip : OwnTipForwardLimit S) (V : WindowData D h)
    (hExit : PhysicalExit D h)
    (hleft : ∀ i, PiecewiseConstantBoundaryData.leftLim (D.data i).bR 0 = -sleLambda (D.data i).κ)
    (hright : ∀ i, PiecewiseConstantBoundaryData.rightLim (D.data i).bR 0 = sleLambda (D.data i).κ)
    (haccess : ∀ i, ∀ᵐ p ∂S.μ,
      (S.marksData (normSource D h)).Z i p ∈ (S.marksData (normSource D h)).B i →
      ∀ b ∈ ((S.marksData (normSource D h)).data i).O₀,
        OwnCollarPoint S (normSource D h) i p b ∨ CfAccessC S (normSource D h) i p b)
    (i : (normSource D h).ι) :
    Nonempty (Aux61GPrime.ZeroComparisons (S.marksData (normSource D h)) i) := by
  have hR := Aux61GCaptureNext.normalized_cut_restart D h R hTip V hExit
  have hTa := Aux61GCaptureNext.normalized_contact_rule D h R
  have hTam := fun i => measurable_contactRule
    (measurable_infDist_retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR))
    (rationalTime (D.q i))
  have hTaG := fun i => isGalmarinoRule_contactRule
    (retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR)) (rationalTime (D.q i))
  have hgeo : ∀ᵐ p ∂S.μ, p ∈ (normSource D h).event i →
      SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1)
        (fun t => S.path p.1 t.toNNReal) (cfHullQ (rationalTime S.s) p.2)
        ((normSource D h).start i)
        (sourceChart (normSource D h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p) := by
    filter_upwards [R.ae_geometry h i] with p hp he
    exact hp he.1
  have hdomain : ∀ᵐ p ∂S.μ, p ∈ (normSource D h).event i → ∃ b' : ℂ,
      ((sourceChart (normSource D h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom :
        Set ℂ) = restartComponent (cfHullQ (rationalTime S.s) p.2) (fun t : ℝ => S.path p.1 t.toNNReal)
          ((normSource D h).start i) b' := by
    filter_upwards [R.ae_domain h i] with p hp he
    exact hp he.1
  have hretained : ∀ᵐ p ∂S.μ, p ∈ (normSource D h).event i →
      (((S.marksData (normSource D h)).chart i p).dom : Set ℂ) ⊆ H \ (cfHullQ (rationalTime S.s) p.2 ∪
        (fun t : ℝ => S.path p.1 t.toNNReal) '' Icc 0 ((normSource D h).start i)) := by
    filter_upwards [hgeo] with p hp he
    exact (hp he).retained
  have hown := ownGerm_of_collarPoint hR i (D.q i) rfl (hleft i) (hright i) hgeo
  have hcg := counterGermC_of_cfAccessC hR i hgeo hdomain (ae_cfW_trace S)
  refine sourceComponentComparisons S (normSource D h) hR i (D.q i) rfl
    (sets_marks_cut_of hR hTam hTaG hTa i 0) hretained
    (normalized_inverse_avoids D h R hTip V hExit i) ?_
  filter_upwards [haccess i, hown, hcg] with p hacc hown' hcg' hB b hb
  rcases hacc hB b hb with h' | h'
  · obtain ⟨z₀, h₁, h₂, h₃, h₄⟩ := hown' hB b h'
    exact ⟨.inl (D.q i), z₀, h₁, Or.inl h₂, h₃, h₄⟩
  · obtain ⟨z₀, h₁, h₂, h₃, h₄⟩ := hcg' hB b h'
    exact ⟨.inr (), z₀, h₁, Or.inr h₂, h₃, h₄⟩

/-- **The component comparisons of the normalized source** (the exact `C`/`Cm` input of
`Aux61Wnd.dyCover_of_normalized_capture` / `Aux61WndCap.dyCover_of_finiteRestrict_capture`). -/
def normalizedComparisonsC (hTip : OwnTipForwardLimit S) (V : WindowData D h)
    (hExit : PhysicalExit D h)
    (hleft : ∀ i, PiecewiseConstantBoundaryData.leftLim (D.data i).bR 0 = -sleLambda (D.data i).κ)
    (hright : ∀ i, PiecewiseConstantBoundaryData.rightLim (D.data i).bR 0 = sleLambda (D.data i).κ)
    (haccess : ∀ i, ∀ᵐ p ∂S.μ,
      (S.marksData (normSource D h)).Z i p ∈ (S.marksData (normSource D h)).B i →
      ∀ b ∈ ((S.marksData (normSource D h)).data i).O₀,
        OwnCollarPoint S (normSource D h) i p b ∨ CfAccessC S (normSource D h) i p b) :
    ∀ i, Aux61GPrime.ZeroComparisons (S.marksData (cutSource S (source D h))) i := fun i =>
  Classical.choice (normalizedComparisonsC_nonempty D h R hTip V hExit hleft hright haccess i)

end Normalized

end InteractingSLE.Sec5.Aux61Cpt
