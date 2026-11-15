/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma76GSide
import InteractingSLE.Spec.Sec7.Lemma76GSingle
import InteractingSLE.Spec.Sec7.Lemma76FMain

/-!
# Lemma 7.6's chart boundary values: the probabilistic inputs

Packet PROVE-LEMMA76G (proof of Lemma 7.6, pp. 268–269). The three ingredients of the boundary values of the union
mean in G7's retained chart, as for the first-contact chart (PROVE-SIDEHEIGHT2, PROVE-PRIMEEND2):

* **Aux. lemma 57 in the retained chart** (`RetData.IsMeasGood.tendsto_lift_of_disjoint` at untouched real points;
  `RetData.IsMeasGood.tendsto_lift_sub`: along an approach to a point of a prefix near which the retained union is that
  prefix, the retained lift minus the single-path lift tends to `0`);
* the chart inverse sends approaches to a real chart point to approaches from the domain
  (`RetData.IsMeasGood.tendsto_inv_real`);
* **the stopped union is a field-determined local set** whose lower union has unbounded components only
  (`cstUnion_facts`, from Lemma 7.5, Aux. lemma 56 at first entrances and the two-history versions).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace Sec7

namespace Lemma76G

open LQGMetric (DistOn TestOn)
open LocalSets Sec6 Restart Supp7 Lemma76F SideHeightBox

/-! ### The retained chart -/

section Chart

variable {Ω : Type*} [MeasurableSpace Ω] {d : RetData Ω}

/-- **Aux. 57 in the retained chart**: at a real point `x` with a ball avoiding `fill(K)`, the lift tends to `0`. -/
theorem RetData.IsMeasGood.tendsto_lift_of_disjoint (hd : d.IsMeasGood) (ω : Ω) {x ρ : ℝ} (hρ : 0 < ρ)
    (hdisj : Disjoint (ball (x : ℂ) ρ) (fillH (d.K ω))) : Tendsto (d.lift ω) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  have hA := hd.isHPHull ω
  exact IsCanonicalDerivLog.tendsto_im_nhdsWithin_zero hA (isCanonicalDerivLog_canonDerivLog hA)
    (ConformalImage.isMapOut_mapOut hA) hρ hdisj

/-- **Aux. lemma 57 for the transition from a single-prefix chart to the retained chart, along an approach** (the
retained-chart copy of `SideHeightBox.tendsto_lift_sub`). -/
theorem RetData.IsMeasGood.tendsto_lift_sub (hd : d.IsMeasGood) (ω : Ω) {γ : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ}
    {W : ℝ≥0 → ℝ} {q : ℝ≥0} (hg : IsGeneratingTrace W ζ (fun t => γ t - x))
    (hWc : ContinuousOn W {s | (s : ℝ≥0∞) < ζ}) (hW0 : W 0 = 0) (hi : InjOn γ {t | (t : ℝ≥0∞) ≤ ζ})
    (hq : (q : ℝ≥0∞) < ζ) (hq0 : 0 < q) (hsub : γ '' Icc 0 q ⊆ d.K ω) {p : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hloc : d.K ω ∩ ball p ρ ⊆ γ '' Icc 0 q) (U : Ultrafilter ℂ) (hU : (U : Filter ℂ) ≤ 𝓝[d.D ω] p) {y : ℝ}
    (hfy : Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q (z - x)) U (𝓝 (y : ℂ))) :
    Tendsto (fun z => d.lift ω z - (QuantumZipper.logDerivFwd (fun r : ℝ => W r.toNNReal) q (z - x)).im) U
      (𝓝 0) := by
  have hKc := hd.isCompact_K ω
  have hB := hd.isHPHull ω
  obtain ⟨κ, hK, hgm, hL⟩ := ReverseArc.exists_physChart hg hWc hW0 hq
  obtain ⟨Φ, hΦc, hΦH, -, hinv, hmaps⟩ := ReverseArc.exists_physInv hg hWc hW0 hi hq hq0
  obtain ⟨ε, hε, hno⟩ := ReverseArc.exists_ball_notMem_of_approach hKc.isClosed hsub hmaps hΦc hΦH hinv hρ hloc U hU
    hfy
  have hdisj : Disjoint (ball (((y + κ : ℝ)) : ℂ) ε)
      ((fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q (z - x) + κ) '' (fillH (d.K ω) \
        fillH (γ '' Icc 0 q))) := by
    rw [Set.disjoint_left]
    rintro w hwb ⟨z, ⟨hzK, hzA⟩, rfl⟩
    refine hno z ⟨hzK.1, hzA⟩ hzK ?_
    rw [mem_ball, dist_eq_norm] at hwb ⊢
    convert hwb using 2
    push_cast; ring
  have hF : (U : Filter ℂ) ≤ 𝓟 (H \ fillH (d.K ω)) := hU.trans inf_le_right
  have hq' : Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q (z - x) + κ) U
      (𝓝[H] (((y + κ : ℝ)) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := hfy.add_const (κ : ℂ)
      convert this using 2
      push_cast; ring
    · filter_upwards [hF (mem_principal_self _)] with z hz
      exact hgm.1.2.mapsTo ⟨hz.1, fun h => hz.2 (fillH_mono hsub h)⟩
  exact ReverseArc.tendsto_im_sub_of_le hK hB (fillH_mono hsub) hgm (ConformalImage.isMapOut_mapOut hB) hL
    (isCanonicalDerivLog_canonDerivLog hB) hF hε hdisj hq'

/-- The chart inverse sends the approach to a real chart point within `ℍ` to an approach within the domain. -/
theorem RetData.IsMeasGood.tendsto_inv_real (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) (w : ℝ) :
    Tendsto (d.inv ω) (𝓝[H] (w : ℂ)) (𝓝[d.D ω] (d.inv ω w)) ∧ d.inv ω w ∈ closure (d.D ω) := by
  have hC := (hd.isRetChart hE).2
  have h0₂ : (d.η₂ ω 0).im = 0 := (hd.good ω (RetData.E_subset_G hE)).2.2.2.2.2.1
  have hψbij : BijOn (d.inv ω) H (d.D ω) := by
    have := (hd.isRetChart hE).2.bijOn h0₂
    rwa [← hd.D_of_mem hE] at this
  have hψc : ContinuousOn (d.inv ω) Hbar := (hd.isRetChart hE).2.continuousOn_inv
  have hwH : (w : ℂ) ∈ Hbar := ofReal_mem_Hbar w
  have ht : Tendsto (d.inv ω) (𝓝[H] (w : ℂ)) (𝓝 (d.inv ω w)) :=
    ((hψc w hwH).tendsto).mono_left (nhdsWithin_mono _ H_subset_Hbar)
  have hev : ∀ᶠ z in 𝓝[H] (w : ℂ), d.inv ω z ∈ d.D ω :=
    eventually_nhdsWithin_of_forall fun z hz => hψbij.mapsTo hz
  refine ⟨tendsto_nhdsWithin_iff.2 ⟨ht, hev⟩, ?_⟩
  have := neBot_nhdsWithin_H w
  exact mem_closure_of_tendsto ht hev

end Chart

/-! ### The stopped union of two flow lines -/

section Flow

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The stopped union of two capped flow lines** is a hitting-measurable, field-determined local set of the
centred field whose lower union has only unbounded components. -/
theorem cstUnion_facts (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) {x₁ x₂ θ₁ θ₂ : ℝ} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (m s t : ℝ≥0) {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ} (hc₁ : ∀ ω, Continuous (ηc₁ ω)) (hc₂ : ∀ ω, Continuous (ηc₂ ω))
    (hm₁ : ∀ t, Measurable fun ω => ηc₁ ω t) (hm₂ : ∀ t, Measurable fun ω => ηc₂ ω t)
    (hag₁ : ∀ᵐ ω ∂P, ∀ t, ηc₁ ω t = η₁ ω (capTime m (ζ₁ ω) t))
    (hag₂ : ∀ᵐ ω ∂P, ∀ t, ηc₂ ω t = η₂ ω (capTime m (ζ₂ ω) t)) :
    Measurable[mΩ, hittingSigma] (cstUnion ηc₁ ηc₂ s t) ∧
    IsLocalSet (cstUnion ηc₁ ηc₂ s t) (WholeField.centredField h u₀) P ∧
    MeasurableSpace.comap (cstUnion ηc₁ ηc₂ s t) hittingSigma ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P ∧
    ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (cstUnion ηc₁ ηc₂ s t ω),
      ¬ IsBounded (connectedComponentIn (lowerUnion (cstUnion ηc₁ ηc₂ s t ω)) z) := by
  obtain ⟨ηs, hc, h0, hηm, hdet, -, -, him, hs₁, hs₂⟩ :=
    exists_twoHist_versions hL75 WholeField.retainedRangeEntranceStatement hκ hκ4 hb hh hη₁ hη₂ hu₀ m
  refine ⟨measurable_cstUnion hc₁ hc₂ hm₁ hm₂ s t,
    isLocalSet_cstUnion_of_isFlowLine hL75 hκ hκ4 hb hh hη₁ hη₂ hu₀ m s t hag₁ hag₂, ?_, ?_⟩
  · have hηsm : ∀ i t, Measurable[aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P]
        fun ω => ηs i ω t := fun i t => by
      obtain ⟨f, hf, he⟩ := hdet i t
      exact measurable_aeSigma_of_ae_eq hf he
    have hmeas := @measurable_cstUnion Ω (aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀)
      inferInstance) P) (ηs 0) (ηs 1) (hc 0) (hc 1) (hηsm 0) (hηsm 1) s t
    have hae : cstUnion ηc₁ ηc₂ s t =ᵐ[P] cstUnion (ηs 0) (ηs 1) s t := by
      filter_upwards [hag₁, hag₂, hs₁, hs₂] with ω h1 h2 h3 h4
      have e1 : ηc₁ ω = ηs 0 ω := funext fun t => (h1 t).trans (h3 t).symm
      have e2 : ηc₂ ω = ηs 1 ω := funext fun t => (h2 t).trans (h4 t).symm
      rw [cstUnion_eq, cstUnion_eq, e1, e2]
    exact SideHeight.comap_le_aeSigma_of_ae_eq hae hmeas.comap_le
  · filter_upwards [hag₁, hag₂, hs₁, hs₂, him] with ω h1 h2 h3 h4 h5
    have e1 : ηc₁ ω = ηs 0 ω := funext fun t => (h1 t).trans (h3 t).symm
    have e2 : ηc₂ ω = ηs 1 ω := funext fun t => (h2 t).trans (h4 t).symm
    refine not_isBounded_lowerUnion_explored (η := pairPath ηc₁ ηc₂) (τ := cstLine s t) (ω := ω)
      (fun i => ?_) (fun i => ?_) (fun i t => ?_)
    · fin_cases i
      exacts [hc₁ ω, hc₂ ω]
    · fin_cases i
      · show (ηc₁ ω 0).im = 0
        rw [e1, h0 0 ω]; simp
      · show (ηc₂ ω 0).im = 0
        rw [e2, h0 1 ω]; simp
    · fin_cases i
      · show 0 ≤ (ηc₁ ω t).im
        rw [e1]; exact h5 0 t
      · show 0 ≤ (ηc₂ ω t).im
        rw [e2]; exact h5 1 t

end Flow

end Lemma76G

end Sec7

end InteractingSLE
