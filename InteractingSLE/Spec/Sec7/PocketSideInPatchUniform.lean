/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInPatchGerm

/-!
# One rational-time event for the actual driver-neighborhood germs

PROVE-POCKET-SIDEIN. Choose coherent means before pair selection. On one
event all fixed candidate pairs and rational original times have the actual
current collars and corrected mean comparisons around the centered driver.
The pathwise interval is fixed by geometry before choosing representatives.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketStopWalls Sec7.PocketStopWallsFin
  Sec7.PocketWordPerQ Sec7.PocketStop LocalSets WholeField WangWu

/-- Coherent actual means and one rational-time event for every nested
common visit's driver interval. No survival or collar law is an input. -/
theorem exists_rational_driver_germ_family {Ω : Type} [mΩ : MeasurableSpace Ω]
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
          ω ∈ (J j).event → ω ∈ (J k).event → U ω ⊆ C ω → d.curve ω q ∈ U ω →
          let O := relChart ((J j).target i d).baseChart ((J j).target i d).curve
            ((J j).visitCapacity d ω q).toNNReal ω
          let I := relChart ((J k).target i d).baseChart ((J k).target i d).curve
            ((J k).visitCapacity d ω q).toNNReal ω
          ∃ ε > 0, ∀ ξ : ℝ, |ξ| < ε →
            (J j).currentVisitLanding i d ω q ξ ∈ U ω ∧
            (∃ a > 0, H ∩ ball (ξ : ℂ) a ⊆ ((pocketTransitionChart O I).dom : Set ℂ)) ∧
            ∀ vC vU : ℂ → ℝ,
            InnerProductSpace.HarmonicOnNhd vC (H \ EC ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ EC ω →
              G j q ω φ = ∫ z, vC z * φ z) →
            InnerProductSpace.HarmonicOnNhd vU (H \ EU ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ EU ω →
              G k q ω φ = ∫ z, vU z * φ z) →
            Tendsto (fun z => vU (O.2.1 z) - vC (O.2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 0) ∧
            Tendsto (fun z => sideMean i.kappa I d.coupledMean vU ((pocketTransitionChart O I).1 z) -
              sideMean i.kappa O d.coupledMean vC z - chiC i.kappa * (pocketTransitionChart O I).2.2 z)
              (𝓝[H] (ξ : ℂ)) (𝓝 0)) := by
  obtain ⟨G, hG, hHarmonic⟩ := exists_original_mean_family hReady
    hTransport hTranslate hu hh hCoupling hu' hKilled hLife
    (fun j => hCont j j) (fun j => hStart j j) (fun j => hMeas j j)
    (fun j => hDetermined j j) (fun j => hLocal j j)
  have hCompare (j k : ι) (r : ℚ) := ae_germ_comparison_at_inner_landing
    (hReady j) (hReady k) hTransport hTranslate hu hh hCoupling hu' hKilled hLife
    (hCont j k) (hStart j k) (hMeas j k) (hDetermined j k) (hLocal j k)
    (r : ℝ).toNNReal (hG j _) (hG k _)
  refine ⟨G, hG, ?_⟩
  filter_upwards [hHarmonic,
    ae_all_iff.2 fun j => ae_all_iff.2 fun k => ae_all_iff.2 (hCompare j k)] with ω hH hC
  refine ⟨hH, ?_⟩
  intro j k r _q _F _C _U _EC _EU hωC hωU hUC hvisit _O _I
  have hEventO : ω ∈ ((J j).target i d).event := by rwa [target_event]
  have hEventI : ω ∈ ((J k).target i d).event := by rwa [target_event]
  obtain ⟨ε, hε, hGeometry⟩ := exists_driver_interval_collars (hReady j) (hReady k)
    (hCont j k 0) (hCont j k 1) (hCont j k 2) hEventO hEventI hUC
    (r : ℝ).toNNReal.coe_nonneg hvisit
  refine ⟨ε, hε, ?_⟩
  intro ξ hξ
  obtain ⟨hp, hCollar⟩ := hGeometry ξ hξ
  refine ⟨hp, hCollar, ?_⟩
  intro vC vU hvC hRepC hvU hRepU
  exact hC j k r hωC hωU vC vU hvC hRepC hvU hRepU hUC hvisit ξ hp

end InteractingSLE.Wire.Current.SideTest
