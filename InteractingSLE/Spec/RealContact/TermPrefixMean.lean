/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermHull
import InteractingSLE.Spec.Sec5.CrossCondStagedMean
import InteractingSLE.Spec.Supplement.SB2LkDom
import InteractingSLE.WangWu.PrefixLocalMean

/-!
# The local-set mean of a filled prefix of a flow line at an own time

Packet PROVE-RC-TERM, second run (ruling R124). For a flow line `η` from `x` with a regular measurable driver `E` and
an own time `a` (the line may die before `a`):

* `fwdHull_recOf`: the hull of the record `recOf a e` is the filling of the trace up to `min a ζ`
  (`Theorem14.SB.Lk.fwdHull_eq_fillH_horizon`: also at the lifetime);
* `image_add_fwdHull_recOf`, `dom_physChart₀_recOf`: the translated hull of the record is the filled capped prefix
  `fill(ηc([0, a]))`; the domain of the unrecentred physical chart of the record is the complement of the filled
  capped prefix `fill(ηc([0, a]))`;
* `ae_condExp_recField_own`: (R1) at the own time `a` (the landed single-stage law, both seed cases);
* `prefixMeanFn κ c θ x 𝔥₀ r = 𝔤_β ∘ f(· − x) − χ arg f′(· − x) − 𝔥₀`, with `β` the stop word of the record `r` and
  `f` its centred Loewner map; `harmonicOnNhd_prefixMeanFn`;
* **`ae_eqOn_prefixMean`**: every harmonic representative `v` of the local-set mean of `fill(ηc([0, a]))` — a local
  set, history-avoidance local for the record — is `prefixMeanFn` of the record off the set (the chart-mean lemma
  `Sec5.CrossCond.Staged.ae_apply_eq_chartMean_of_chartLaw`, countably many bumps, uniqueness of harmonic
  representatives).

R48-neutral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.RealContact

namespace Term

open Restart Exist.Staged Exist.StagedLaw Sec2.Assembly LocalSets WholeField

/-! ### The hull and the chart domain of a record at an own time -/

section Det

variable {e : (ℝ≥0 → ℝ) × ℝ≥0∞} {η : ℝ≥0 → ℂ} {x : ℝ} {a : ℝ≥0}

/-- **The hull of the record at an own time** is the filling of the trace up to `min a ζ`. -/
theorem fwdHull_recOf (he : IsRegularDriver e) (hg : LocalExt.IsDrvGood (recHist (recOf (a : ℝ≥0∞) e)))
    (hη : IsGeneratingTrace e.1 e.2 (fun t => η t - x)) :
    fwdHull (rdrv (recOf (a : ℝ≥0∞) e)) (rtime (recOf (a : ℝ≥0∞) e)) =
      fillH ((fun t => η t - (x : ℂ)) '' Icc 0 (min (a : ℝ≥0∞) e.2).toNNReal) := by
  have hfin : min (a : ℝ≥0∞) e.2 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  have hT'e : (((min (a : ℝ≥0∞) e.2).toNNReal : ℝ≥0) : ℝ≥0∞) = min (a : ℝ≥0∞) e.2 := ENNReal.coe_toNNReal hfin
  have hwc : Continuous (retOf (a : ℝ≥0∞) e).1 := continuous_retOf he hg
  have hw0 : (retOf (a : ℝ≥0∞) e).1 0 = 0 := by
    change e.1 (min ((0 : ℝ≥0) : ℝ≥0∞) (min (a : ℝ≥0∞) e.2)).toNNReal = 0
    rw [ENNReal.coe_zero, min_eq_left (zero_le (a := min _ _)), ENNReal.toNNReal_zero]
    exact he.2.1
  have hα : IsGeneratingTrace (retOf (a : ℝ≥0∞) e).1 (((min (a : ℝ≥0∞) e.2).toNNReal : ℝ≥0) : ℝ≥0∞)
      (fun t => η t - x) := by
    rw [hT'e]
    refine StoppedK2.isGeneratingTrace_congr (fun t ht => ?_) (LP.isGeneratingTrace_mono hη (min_le_right _ _))
    change e.1 t = e.1 (min (t : ℝ≥0∞) (min (a : ℝ≥0∞) e.2)).toNNReal
    rw [min_eq_left ht.le, ENNReal.toNNReal_coe]
  have h := Theorem14.SB.Lk.fwdHull_eq_fillH_horizon hwc hw0 hα
  have hd : rdrv (recOf (a : ℝ≥0∞) e) = fun s : ℝ => (retOf (a : ℝ≥0∞) e).1 s.toNNReal :=
    recDrv_eq_stopDrv he hg
  rw [hd]
  exact h

/-- **The translated hull of the record** is the filled capped prefix. -/
theorem image_add_fwdHull_recOf (he : IsRegularDriver e) (hg : LocalExt.IsDrvGood (recHist (recOf (a : ℝ≥0∞) e)))
    (hη : IsGeneratingTrace e.1 e.2 (fun t => η t - x)) {m : ℝ≥0} (ham : a < m) {ηc : ℝ≥0 → ℂ}
    (hag : ∀ s, ηc s = η (capTime m e.2 s)) :
    (fun z : ℂ => z + (x : ℂ)) '' fwdHull (rdrv (recOf (a : ℝ≥0∞) e)) (rtime (recOf (a : ℝ≥0∞) e)) =
      fillH (ηc '' Icc 0 a) := by
  have hfin : min (a : ℝ≥0∞) e.2 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  have hT'e : (((min (a : ℝ≥0∞) e.2).toNNReal : ℝ≥0) : ℝ≥0∞) = min (a : ℝ≥0∞) e.2 := ENNReal.coe_toNNReal hfin
  rw [fwdHull_recOf he hg hη, ← fillH_image_add_real, image_image]
  congr 1
  ext z
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hs' : (s : ℝ≥0∞) ≤ min (a : ℝ≥0∞) e.2 := hT'e ▸ ENNReal.coe_le_coe.2 hs.2
    have hsa : s ≤ a := ENNReal.coe_le_coe.1 (hs'.trans (min_le_left _ _))
    refine ⟨s, ⟨zero_le, hsa⟩, ?_⟩
    rw [hag s, capTime_of_le m e.2 (le_min (hs'.trans (min_le_right _ _))
      (ENNReal.coe_le_coe.2 (hsa.trans ham.le)))]
    exact (sub_add_cancel _ _).symm
  · rintro ⟨s, hs, rfl⟩
    refine ⟨capTime m e.2 s, ⟨zero_le, ?_⟩, ?_⟩
    · have h1 : ((capTime m e.2 s : ℝ≥0) : ℝ≥0∞) ≤ min (a : ℝ≥0∞) e.2 := by
        unfold capTime
        refine le_min ?_ ?_
        · exact ENNReal.coe_le_coe.2 ((min_le_left _ _).trans hs.2)
        · refine (ENNReal.coe_le_coe.2 (min_le_right _ _)).trans ?_
          rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))]
          exact min_le_left _ _
      have h2 := ENNReal.toNNReal_mono hfin h1
      rwa [ENNReal.toNNReal_coe] at h2
    · show η (capTime m e.2 s) - (x : ℂ) + (x : ℂ) = ηc s
      rw [sub_add_cancel, hag s]

/-- **The domain of the unrecentred physical chart of the record** is the complement of the filled capped prefix. -/
theorem dom_physChart₀_recOf (he : IsRegularDriver e) (hg : LocalExt.IsDrvGood (recHist (recOf (a : ℝ≥0∞) e)))
    (hη : IsGeneratingTrace e.1 e.2 (fun t => η t - x)) {m : ℝ≥0} (ham : a < m) {ηc : ℝ≥0 → ℂ}
    (hag : ∀ s, ηc s = η (capTime m e.2 s)) :
    (((Chart.id.recenter x).trans (recChart (recOf (a : ℝ≥0∞) e))).dom : Set ℂ) =
      H \ fillH (ηc '' Icc 0 a) := by
  rw [coe_dom_physChart₀, image_add_real_H_diff, image_add_fwdHull_recOf he hg hη ham hag]

end Det

/-! ### (R1) at an own time -/

/-- **(R1) for one flow line at an own time `a`** (both seed cases of the landed single-stage law). -/
theorem ae_condExp_recField_own {κ : ℝ} (hκ : 0 < κ) (c : BoundaryWord) (θ : ℝ) (a : ℝ≥0) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (g : Ω → DistOn upperHalfPlaneOpens)
    (E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (hE : Measurable E) (hreg : ∀ ω, IsRegularDriver (E ω))
    (hfl : IsFlowLineDriver κ c.fn c.jumps θ P g (fun s ω => (E ω).1 s) (fun ω => (E ω).2))
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P,
      P[fun ω' => Complex.exp (Complex.I * (recField κ (recOf (a : ℝ≥0∞) (E ω')) (g ω') φ : ℂ)) |
          MeasurableSpace.comap (fun ω' => recOf (a : ℝ≥0∞) (E ω')) inferInstance] ω =
        gaussCF (stopWord κ (c, θ, recOf (a : ℝ≥0∞) (E ω))) φ := by
  by_cases hseed : ForceWord.ThresholdCondition (flowLineRhoL κ c.fn c.jumps 0 θ)
      (flowLineRhoR κ c.fn c.jumps 0 θ) 0 (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
  · exact ae_condExp_recField_of_inadmissible hκ c θ a P g E hE hreg hfl hseed φ
  · filter_upwards [ae_condExp_recField_of_admissible hκ c θ a P g E hE hreg hfl hseed φ] with ω hω
    exact hω (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))

/-! ### The mean -/

/-- **The candidate mean of a record**: `𝔤_β ∘ f(· − x) − χ arg f′(· − x) − 𝔥₀`, with `β` the stop word of the record
and `f` its centred Loewner map. -/
def prefixMeanFn (κ : ℝ) (c : BoundaryWord) (θ x : ℝ) (u₀ : ℂ → ℝ) (r : RecData) (z : ℂ) : ℝ :=
  (stopWord κ (c, θ, r)).mean (fwdMap (rdrv r) (rtime r) (z - (x : ℂ))) -
    chiC κ * (logDerivFwd (rdrv r) (rtime r) (z - (x : ℂ))).im - u₀ z

theorem prefixMeanFn_eq (κ : ℝ) (c : BoundaryWord) (θ x : ℝ) (u₀ : ℂ → ℝ) (r : RecData) (z : ℂ) :
    prefixMeanFn κ c θ x u₀ r z =
      (stopWord κ (c, θ, r)).mean (((Chart.id.recenter x).trans (recChart r)).1 z) -
        chiC κ * ((Chart.id.recenter x).trans (recChart r)).2.2 z - u₀ z := by
  rw [physChart₀_fst, physChart₀_lift]
  rfl

/-- The candidate mean is harmonic on the domain of the unrecentred physical chart. -/
theorem harmonicOnNhd_prefixMeanFn (κ : ℝ) (c : BoundaryWord) (θ x : ℝ) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (r : RecData) :
    InnerProductSpace.HarmonicOnNhd (prefixMeanFn κ c θ x u₀ r)
      (((Chart.id.recenter x).trans (recChart r)).dom : Set ℂ) := by
  have hconf := isConformal_physChart₀ x r
  obtain ⟨-, -, hharm, -⟩ := isMeasChart_physChart₀ (m := (⊤ : MeasurableSpace Unit)) (rec := fun _ => r)
    measurable_const x
  have h1 : InnerProductSpace.HarmonicOnNhd
      ((stopWord κ (c, θ, r)).mean ∘ ((Chart.id.recenter x).trans (recChart r)).1)
      ((Chart.id.recenter x).trans (recChart r)).dom :=
    LQGMetric.harmonicOnNhd_comp_holo QuantumZipper.isOpen_H ((Chart.id.recenter x).trans (recChart r)).dom.isOpen
      (BoundaryWord.isBoundedHarmonicExtension_mean _ (isSorted_stopWord κ _)).1 hconf.differentiableOn_fwd
      fun z hz => hconf.fwd_mem hz
  intro z hz
  have h2 := (hharm () z hz).const_smul (c := chiC κ)
  have e : prefixMeanFn κ c θ x u₀ r =
      ((stopWord κ (c, θ, r)).mean ∘ ((Chart.id.recenter x).trans (recChart r)).1 -
        chiC κ • ((Chart.id.recenter x).trans (recChart r)).2.2) - u₀ := by
    funext y
    rw [prefixMeanFn_eq]
    simp only [Pi.sub_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul]
  rw [e]
  exact ((h1 z hz).sub h2).sub (hu₀ z (hconf.dom_subset hz))

section Mean

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The local-set mean of a set retained with a record, test function by test function**: the chart-mean lemma in
the unrecentred physical chart of the record. -/
theorem ae_apply_eq_prefixMeanFn {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hh : IsGFFWithBoundaryData P h b jumps) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {x θ : ℝ} {c : BoundaryWord} {rec : Ω → RecData} (hrec : Measurable rec)
    (hlaw : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      P[fun ω' => Complex.exp (Complex.I * (termField κ x (rec ω') (h ω') ψ : ℂ)) |
          MeasurableSpace.comap rec inferInstance] ω = gaussCF (stopWord κ (c, θ, rec ω)) ψ)
    {A : Ω → Set ℂ} (hAm : Measurable[mΩ, hittingSigma] A) (hloc : IsLocalSet A (centredField h u₀) P)
    (hmark : IsHistoryAvoidanceLocal (MeasurableSpace.comap rec inferInstance) A (centredField h u₀) P)
    (hdomA : ∀ᵐ ω ∂P, (((Chart.id.recenter x).trans (recChart (rec ω))).dom : Set ℂ) = H \ A ω)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean A (centredField h u₀) P g)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, tsupport φ ⊆ H \ A ω → g ω φ = ∫ z, prefixMeanFn κ c θ x u₀ (rec ω) z * φ z := by
  obtain ⟨cc, hcc⟩ : ∃ cc : Ω → Chart, cc = fun ω => (Chart.id.recenter x).trans (recChart (rec ω)) := ⟨_, rfl⟩
  have hMC : Theorem14.WalkInf.IsMeasChart (MeasurableSpace.comap rec inferInstance) cc := by
    rw [hcc]
    exact isMeasChart_physChart₀ (comap_measurable rec) x
  obtain ⟨hconf, hlc, -, hdom, hfwd, hball, hlift⟩ := hMC
  have hYm : Measurable fun ω => termField κ x (rec ω) (h ω) := by
    have hp : Measurable fun ω => (rec ω, h ω) := hrec.prodMk hh.1
    change Measurable ((fun p : RecData × DistOn upperHalfPlaneOpens => termField κ x p.1 p.2) ∘
      fun ω => (rec ω, h ω))
    exact (measurable_termField κ x).comp hp
  have htr : ∀ᵐ ω ∂P, ω ∈ (univ : Set Ω) →
      IsChartTransport (cc ω) 1 0 (chiC κ) (h ω) (termField κ x (rec ω) (h ω)) := by
    refine Eventually.of_forall fun ω _ => ?_
    rw [hcc]
    exact isChartTransport_termField κ x (rec ω) (h ω)
  have hlaw' : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ (univ : Set Ω) →
      P[fun ω' => Complex.exp (Complex.I * (termField κ x (rec ω') (h ω') ψ : ℂ)) |
          MeasurableSpace.comap rec inferInstance] ω = gaussCF (stopWord κ (c, θ, rec ω)) ψ := fun ψ =>
    (hlaw ψ).mono fun ω hω _ => hω
  have hdomA' : ∀ᵐ ω ∂P, ((cc ω).dom : Set ℂ) = H \ A ω := by
    rw [hcc]
    exact hdomA
  have hAD : ∀ᵐ ω ∂P, ω ∈ (univ : Set Ω) → ((cc ω).dom : Set ℂ) ⊆ H \ A ω ∧ IsOpen ((H \ A ω) \ (cc ω).dom) := by
    filter_upwards [hdomA'] with ω hω _
    rw [hω]
    exact ⟨subset_rfl, by rw [Set.sdiff_self]; exact isOpen_empty⟩
  have hmean := Sec5.CrossCond.Staged.ae_apply_eq_chartMean_of_chartLaw
    (𝓗 := MeasurableSpace.comap rec inferInstance) (c := cc) hrec.comap_le hconf hdom hfwd hball hlift hlc hh hu₀
    hYm (χ := chiC κ) (G := univ) MeasurableSet.univ htr (β := fun ω => stopWord κ (c, θ, rec ω)) hlaw' hAm hloc
    hmark hAD hg φ
  filter_upwards [hmean, hdomA'] with ω hω hdω hsupp
  have hsD : tsupport φ ⊆ (cc ω).dom := by
    show tsupport φ ⊆ ((cc ω).dom : Set ℂ)
    rw [hdω]
    exact hsupp
  rw [hω (mem_univ ω) hsD]
  have hmc : ContinuousOn (fun z => (stopWord κ (c, θ, rec ω)).mean ((cc ω).1 z)) (cc ω).dom :=
    (BoundaryWord.continuousOn_mean _).comp (hconf ω).differentiableOn_fwd.continuousOn fun z hz =>
      (hconf ω).fwd_mem hz
  have hc1 : ContinuousOn (fun z => (stopWord κ (c, θ, rec ω)).mean ((cc ω).1 z) - chiC κ * (cc ω).2.2 z)
      (cc ω).dom := hmc.sub (continuousOn_const.mul (hlc ω))
  have hi1 := WholeField.integrable_mul_testOn hc1 φ hsD
  have hi2 := WholeField.integrable_mul_testOn (fun z hz =>
    (hu₀.1 z hz).1.continuousAt.continuousWithinAt) φ φ.tsupport_subset
  rw [← integral_sub hi1 hi2]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show _ = prefixMeanFn κ c θ x u₀ (rec ω) z * φ z
  rw [prefixMeanFn_eq, hcc]
  ring

/-- **The local-set mean of a set retained with a record**: every harmonic representative is the candidate mean. -/
theorem ae_eqOn_prefixMeanFn {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hh : IsGFFWithBoundaryData P h b jumps) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {x θ : ℝ} {c : BoundaryWord} {rec : Ω → RecData} (hrec : Measurable rec)
    (hlaw : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      P[fun ω' => Complex.exp (Complex.I * (termField κ x (rec ω') (h ω') ψ : ℂ)) |
          MeasurableSpace.comap rec inferInstance] ω = gaussCF (stopWord κ (c, θ, rec ω)) ψ)
    {A : Ω → Set ℂ} (hAm : Measurable[mΩ, hittingSigma] A) (hloc : IsLocalSet A (centredField h u₀) P)
    (hmark : IsHistoryAvoidanceLocal (MeasurableSpace.comap rec inferInstance) A (centredField h u₀) P)
    (hdomA : ∀ᵐ ω ∂P, (((Chart.id.recenter x).trans (recChart (rec ω))).dom : Set ℂ) = H \ A ω)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean A (centredField h u₀) P g) :
    ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g ω φ = ∫ z, v z * φ z) →
      EqOn v (prefixMeanFn κ c θ x u₀ (rec ω)) (H \ A ω) := by
  have hφ := ae_apply_eq_prefixMeanFn hh hu₀ hrec hlaw hAm hloc hmark hdomA hg
  have hmh : ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (prefixMeanFn κ c θ x u₀ (rec ω)) (H \ A ω) := by
    filter_upwards [hdomA] with ω hω
    rw [← hω]
    exact harmonicOnNhd_prefixMeanFn κ c θ x hu₀.1 (rec ω)
  have hall := WangWu.ae_forall_apply_eq_of_forall_ae hg.2.1 (hloc.2.1.mono fun ω hω => hω.2) hmh hφ
  filter_upwards [hall, hmh, hloc.2.1] with ω hω hmω hAo v hv hrep
  exact Sec6.eqOn_of_integral_mul_eq hAo.2 sdiff_subset hv hmω fun φ hφs => by
    rw [← hrep φ hφs, hω φ hφs]

/-- **The local-set mean of a filled prefix of a flow line at an own time** (see the module docstring). -/
theorem ae_eqOn_prefixMean {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hh : IsGFFWithBoundaryData P h b jumps) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {x θ : ℝ} {c : BoundaryWord} {E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEm : Measurable E)
    (hreg : ∀ ω, IsRegularDriver (E ω))
    (hfl : IsFlowLineDriver κ c.fn c.jumps θ P (fun ω => Exist.flowField x 0 (h ω)) (fun s ω => (E ω).1 s)
      (fun ω => (E ω).2))
    {η : Ω → ℝ≥0 → ℂ} (htrace : ∀ᵐ ω ∂P, IsGeneratingTrace (E ω).1 (E ω).2 (fun s => η ω s - x))
    {a m : ℝ≥0} (ham : a < m) {ηc : Ω → ℝ≥0 → ℂ}
    (hag : ∀ᵐ ω ∂P, ∀ s, ηc ω s = η ω (capTime m (E ω).2 s))
    (hAm : Measurable[mΩ, hittingSigma] (fillOf ηc a))
    (hloc : IsLocalSet (fillOf ηc a) (centredField h u₀) P)
    (hmark : IsHistoryAvoidanceLocal (MeasurableSpace.comap (fun ω => recOf (a : ℝ≥0∞) (E ω)) inferInstance)
      (fillOf ηc a) (centredField h u₀) P)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean (fillOf ηc a) (centredField h u₀) P g) :
    ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ fillOf ηc a ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ fillOf ηc a ω → g ω φ = ∫ z, v z * φ z) →
      EqOn v (prefixMeanFn κ c θ x u₀ (recOf (a : ℝ≥0∞) (E ω))) (H \ fillOf ηc a ω) := by
  have hdomA : ∀ᵐ ω ∂P, (((Chart.id.recenter x).trans (recChart (recOf (a : ℝ≥0∞) (E ω)))).dom : Set ℂ) =
      H \ fillOf ηc a ω := by
    filter_upwards [ae_isDrvGood_of_isFlowLineDriver hκ (a : ℝ≥0∞) hreg hfl, htrace, hag] with ω hgω htω haω
    exact dom_physChart₀_recOf (hreg ω)
      (hgω (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))) htω ham haω
  exact ae_eqOn_prefixMeanFn hh hu₀ (measurable_recOf hEm hreg _)
    (fun ψ => ae_condExp_recField_own hκ c θ a P (fun ω => Exist.flowField x 0 (h ω)) E hEm hreg hfl ψ)
    hAm hloc hmark hdomA hg

end Mean

end Term

end InteractingSLE.RealContact
