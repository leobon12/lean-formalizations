/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondGenLawImage
import InteractingSLE.Spec.Sec5.CrossCondThetaMart

/-!
# From a chart conditional law to contact-word mean martingales

PROVE-CROSSCOND-GEN. This is B4 with weakly ordered force coordinates, including
one-sided collisions. It uses no strict force-gap cutoff. The announcing sequence
implies positive available lifetime almost surely; zero-life samples are not covered
by this conditional helper. Integrability of the transported field is proved from
the time-zero Gaussian law, rather than assumed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.Gen

open Ito WangWu WangWu.ImgDrv MartChar Sec7.Aux117

/-- A fixed-time chart law implies the explicit contact-word coupling means are local
martingales in the usual augmentation. The chart may be random but is known initially. -/
theorem isLocalMartingaleBefore_coupProc_of_chartConst
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {𝓐 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {T : Ω → WithTop ℝ≥0} {σ : ℕ → Ω → ℝ≥0} {c : Ω → Chart} {a k : ℝ}
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hK : IsContactWord W VL VR T)
    (hWa : StronglyAdapted (usualAugmentation 𝓐 P) W)
    (hVLa : ∀ i, StronglyAdapted (usualAugmentation 𝓐 P) (VL i))
    (hVRa : ∀ j, StronglyAdapted (usualAugmentation 𝓐 P) (VR j))
    (hTm : ∀ t : ℝ≥0, MeasurableSet[usualAugmentation 𝓐 P t] {ω | (T ω : ℝ≥0∞) ≤ t})
    (hσ : Coupling.IsAnnouncingSeq (usualAugmentation 𝓐 P) P (fun ω => (T ω : ℝ≥0∞)) σ)
    (hc : ∀ ω, (c ω).IsConformal)
    (hlc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hdom : ∀ z, MeasurableSet[usualAugmentation 𝓐 P 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[usualAugmentation 𝓐 P 0]
      ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hlift : ∀ z, Measurable[usualAugmentation 𝓐 P 0]
      ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hh : Measurable h)
    (hchart : Sec7.Lemma71D.IsChartCouplingCharFunConst κ ρL ρR P 𝓐 W VL VR
      (fun ω => (T ω : ℝ≥0∞)) c a k h) :
    ∀ z ∈ H, IsLocalMartingaleBefore (usualAugmentation 𝓐 P) P
      (fun ω => min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (T ω))
      (coupProc κ ρL ρR W VL VR z) := by
  let 𝓖 := usualAugmentation 𝓐 P
  have : 𝓖.IsRightContinuous := isRightContinuous_usualAugmentation _ _
  have hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s :=
    fun _ hs h0 => measurableSet_usualAugmentation_of_null hs h0 0
  have hcfU := Sec7.Lemma71D.isChartCouplingCharFun_usualAugmentation hh hc hlc hK.contW
    (fun i ω => (hK.pathL ω i).1) (fun j ω => (hK.pathR ω j).1)
    (fun ω t ht => ⟨fun i => hK.ordL ω t i ht, fun j => hK.ordR ω t j ht⟩) hchart
  let h' : Ω → DistOn upperHalfPlaneOpens := fun ω => Sec7.Lemma71K.chartField (c ω) a k (h ω)
  have ht : ∀ ω, IsChartTransport (c ω) 1 a k (h ω) (h' ω) :=
    fun ω => Sec7.Lemma71K.isChartTransport_chartField (hc ω) (hlc ω) _ _ (h ω)
  have hcf' : Coupling.MartMeans.IsCouplingCharFun κ ρL ρR P 𝓖 W VL VR
      (fun ω => (T ω : ℝ≥0∞)) h' :=
    Coupling.MartMeans2.isCouplingCharFun_of_isChartTransport hc hdom hfwd hlift hlc hh
      (Eventually.of_forall fun ω => ⟨hK.w_zero ω, hK.contW ω⟩) hcfU ht
  have hh'm : Measurable h' := by
    have hm := Chart.measurable_chartTransport_random' hc (fun z => 𝓖.le 0 _ (hdom z))
      (fun z => (hfwd z).mono (𝓖.le 0) le_rfl)
      (fun z => (hlift z).mono (𝓖.le 0) le_rfl) hlc hh 1 a k
    have e : h' = fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) := by
      funext ω
      simp only [h', Sec7.Lemma71K.chartField, hc ω, ↓reduceDIte]
    rw [e]
    exact hm
  have hpos : ∀ᵐ ω ∂P, 0 < (T ω : ℝ≥0∞) := by
    filter_upwards [hσ.2.2.1 0] with ω hω
    exact lt_of_le_of_lt (show (0 : ℝ≥0∞) ≤ σ 0 ω from zero_le) hω
  have hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => h' ω φ) P := fun φ =>
    integrable_apply_of_isCouplingCharFun_of_bounded hcf'
      (hpos.mono fun ω hω => ⟨hω, hK.contW ω, hK.w_zero ω⟩) φ
      ((LQGMetric.measurable_distOn_apply φ).comp hh'm)
  intro z hz
  obtain ⟨G, hG, hGae, hloc⟩ := Coupling.MartMeans2.exists_isLocalMartingaleBefore_meanProcOn hnull
    (adaptedBefore_of_stronglyAdapted hTm hWa)
    (fun i => adaptedBefore_of_stronglyAdapted hTm (hVLa i))
    (fun j => adaptedBefore_of_stronglyAdapted hTm (hVRa j))
    (Eventually.of_forall fun ω => ⟨hK.w_zero ω, hK.contW ω,
      ⟨fun i => (hK.pathL ω i).1, fun j => (hK.pathR ω j).1⟩,
      fun t ht => ⟨fun i => hK.ordL ω t i ht, fun j => hK.ordR ω t j ht⟩⟩)
    hσ hint hcf' (fun ω t => meanExt κ ρL ρR (W t ω) (fun i => VL i t ω) (fun j => VR j t ω))
    (fun ω t => isBoundedHarmonicExtension_meanExt κ ρL ρR _ _ _) hz
  exact Restart.ConverseBefore.isLocalMartingaleBefore_coupProc_of_meanProcOn hnull hG hGae
    (Restart.ConverseBefore.measurable_coupProc_zero hK.w_zero
      (fun i => ((hVLa i) 0).measurable.mono (𝓖.le 0) le_rfl)
      (fun j => ((hVRa j) 0).measurable.mono (𝓖.le 0) le_rfl) hz) hloc

end InteractingSLE.Sec5.CrossCond.Gen
