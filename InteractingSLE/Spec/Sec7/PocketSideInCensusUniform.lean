/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInCensusMeans
import InteractingSLE.Spec.Sec7.PocketSideInCensusComparison
import InteractingSLE.Spec.Sec7.PocketSideInCensusHeight

/-!
# One rational-time event for all fixed candidate pairs and exact heights

PROVE-POCKET-SIDEIN. R73's order of quantifiers: fix a countable incoming
candidate family, choose one mean for each candidate and original time,
then intersect the rational-time comparisons and height transports. Every
realized nested witness is selected only after this common event.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open QuantumZipper (H)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketStopWalls Sec7.PocketStopWallsFin
  Sec7.PocketWordPerQ Sec7.PocketStop LocalSets WholeField WangWu

/-- Coherent actual means, their rational-time harmonicity, every pair's
R.5 germ and every candidate's exact height transport, on one common event.
Geometry and the exact initial height remain inside the pathwise conclusions. -/
theorem exists_coherent_rational_reference_family {Ω : Type} [mΩ : MeasurableSpace Ω]
    {ι : Type*} [Countable ι] {J : ι → SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    [IsProbabilityMeasure d.measure] (hReady : ∀ j, (J j).Ready d)
    (hTransport : ∀ ω, IsChartTransport infinitySourceChart (-1) d.scale d.chartConstant
      (d.field ω) (d.chartField ω))
    (hTranslate : ∀ ω, IsTranslateAddConst 0 d.translateConstant (d.chartField ω) (d.translatedField ω))
    (hu : InnerProductSpace.HarmonicOnNhd d.originalMean H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField d.field d.originalMean) d.measure)
    (hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure d.filtration
      d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hu' : IsBoundedHarmonicExtension (forceBoundaryData i.kappa d.rhoL d.rhoR d.xL d.xR)
      (forceJumpSet d.xL d.xR) d.coupledMean)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (hLife : ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤)
    (hCont : ∀ j j' k ω, Continuous (pairWallFamily (J j) (J j') d k ω))
    (hStart : ∀ j j' k ω, pairWallFamily (J j) (J j') d k ω 0 = 0)
    (hMeas : ∀ j j' k t, Measurable fun ω => pairWallFamily (J j) (J j') d k ω t)
    (hDetermined : ∀ j j' k t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => pairWallFamily (J j) (J j') d k ω t) =ᵐ[d.measure]
        fun ω => f (centredField d.field d.originalMean ω))
    (hLocal : ∀ j j' k, Sec6.IsEntranceHistoryLocal (pairWallFamily (J j) (J j') d k)
      (centredField d.field d.originalMean) d.measure) :
    ∃ G : ι → ℝ≥0 → Ω → DistOn upperHalfPlaneOpens,
      (∀ j q, IsLocalSetMean (eventFilled (J j).event ((J j).target i d).domain
        (fun ω => regHull d.driver d.lifetime q ω))
        (centredField d.translatedField d.coupledMean) d.measure (G j q)) ∧
      ∀ᵐ ω ∂d.measure,
        (∀ (j : ι) (r : ℚ),
          IsHarmonicDistOn (G j (r : ℝ).toNNReal ω)
            (H \ eventFilled (J j).event ((J j).target i d).domain
              (fun ω => regHull d.driver d.lifetime (r : ℝ).toNNReal ω) ω)) ∧
        (∀ (j k : ι) (r : ℚ),
          let q := (r : ℝ).toNNReal
          let F := fun ω => regHull d.driver d.lifetime q ω
          let C := ((J j).target i d).domain
          let U := ((J k).target i d).domain
          let EC := eventFilled (J j).event C F
          let EU := eventFilled (J k).event U F
          ω ∈ (J j).event → ω ∈ (J k).event → ∀ vC vU : ℂ → ℝ,
            InnerProductSpace.HarmonicOnNhd vC (H \ EC ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ EC ω →
              G j q ω φ = ∫ z, vC z * φ z) →
            InnerProductSpace.HarmonicOnNhd vU (H \ EU ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ EU ω →
              G k q ω φ = ∫ z, vU z * φ z) → U ω ⊆ C ω → d.curve ω q ∈ U ω →
            let O := relChart ((J j).target i d).baseChart ((J j).target i d).curve
              ((J j).visitCapacity d ω q).toNNReal ω
            let I := relChart ((J k).target i d).baseChart ((J k).target i d).curve
              ((J k).visitCapacity d ω q).toNNReal ω
            ∀ (W : ℝ → ℝ), Continuous W → W 0 = 0 →
              O = (((J j).target i d).baseChart ω).loewner W ((J j).visitCapacity d ω q).toNNReal →
              ∀ (x : ℝ) (a : ℝ → ℂ),
              QuantumZipper.IsForwardSol W x ((J j).visitCapacity d ω q).toNNReal a →
              ∀ r : ℝ, 0 < r →
              H ∩ ball ((a ((J j).visitCapacity d ω q).toNNReal).re : ℂ) r ⊆
                ((pocketTransitionChart O I).dom : Set ℂ) →
              Tendsto (fun z => vU (O.2.1 z) - vC (O.2.1 z))
                (𝓝[H] ((a ((J j).visitCapacity d ω q).toNNReal).re : ℂ)) (𝓝 0)) ∧
        (∀ (j : ι) (r : ℚ),
          let q := (r : ℝ).toNNReal
          let C := ((J j).target i d).domain
          let F := fun ω => regHull d.driver d.lifetime q ω
          let E0 := eventFilled (J j).event C (fun _ => ∅)
          let Eq := eventFilled (J j).event C F
          ω ∈ (J j).event → ∀ v0 vq : ℂ → ℝ,
            InnerProductSpace.HarmonicOnNhd v0 (H \ E0 ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ E0 ω →
              G j 0 ω φ = ∫ z, v0 z * φ z) →
            InnerProductSpace.HarmonicOnNhd vq (H \ Eq ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ Eq ω →
              G j q ω φ = ∫ z, vq z * φ z) → d.curve ω q ∈ C ω →
            let O := relChart ((J j).target i d).baseChart ((J j).target i d).curve
              ((J j).visitCapacity d ω q).toNNReal ω
            ∀ (W : ℝ → ℝ), Continuous W → W 0 = 0 →
              O = (((J j).target i d).baseChart ω).loewner W ((J j).visitCapacity d ω q).toNNReal →
              ∀ (x : ℝ) (a : ℝ → ℂ),
              QuantumZipper.IsForwardSol W x ((J j).visitCapacity d ω q).toNNReal a →
              ∀ b : ℝ,
              Tendsto (sideMean i.kappa (((J j).target i d).baseChart ω) d.coupledMean v0)
                (𝓝[H] (x : ℂ)) (𝓝 b) →
              Tendsto (sideMean i.kappa O d.coupledMean vq)
                (𝓝[H] ((a ((J j).visitCapacity d ω q).toNNReal).re : ℂ)) (𝓝 b)) := by
  obtain ⟨G, hG, hHarmonic⟩ := exists_original_mean_family hReady
    hTransport hTranslate hu hh hCoupling hu' hKilled hLife
    (fun j => hCont j j) (fun j => hStart j j) (fun j => hMeas j j)
    (fun j => hDetermined j j) (fun j => hLocal j j)
  have hCompare (j k : ι) (r : ℚ) := ae_germ_comparison_at_surviving_visit
    (hReady j) (hReady k) hTransport hTranslate hu hh hCoupling hu' hKilled hLife
    (hCont j k) (hStart j k) (hMeas j k) (hDetermined j k) (hLocal j k)
    (r : ℝ).toNNReal (hG j _) (hG k _)
  have hHeight (j : ι) (r : ℚ) := by
    have hInitial := hG j 0
    rw [original_filling_zero] at hInitial
    exact ae_exact_height_transport_at_surviving_visit (hReady j)
      hTransport hTranslate hu hh hCoupling hu' hKilled hLife
      (hCont j j) (hStart j j) (hMeas j j) (hDetermined j j) (hLocal j j)
      (r : ℝ).toNNReal hInitial (hG j _)
  refine ⟨G, hG, ?_⟩
  filter_upwards [hHarmonic,
    ae_all_iff.2 fun j => ae_all_iff.2 fun k => ae_all_iff.2 (hCompare j k),
    ae_all_iff.2 fun j => ae_all_iff.2 (hHeight j)] with ω hH hC hT
  exact ⟨hH, hC, hT⟩

end InteractingSLE.Wire.Current.SideTest
