/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInSurviveActual

/-!
# The actual two-pocket R.5 germ at a surviving incoming access

PROVE-POCKET-SIDEIN. The initial shared neighborhood is now derived from
survival and the shared current collar. The current conformal charts, cuts,
inclusion and finite physical landing also come from the actual visit.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Bornology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketStopWalls Sec7.PocketStopWallsFin
  Sec7.PocketWordPerQ Sec7.PocketStop Sec7.PocketTraversal LocalSets WholeField WangWu

/-- Fixed original-time R.5 comparison with no separate shared initial
neighborhood, chart-domain, chart-inclusion or physical-landing premise. -/
theorem exists_germ_comparison_at_surviving_visit {Ω : Type} [mΩ : MeasurableSpace Ω]
    {outer inner : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    [IsProbabilityMeasure d.measure] (hOuter : outer.Ready d) (hInner : inner.Ready d)
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
    (hCont : ∀ j ω, Continuous (pairWallFamily outer inner d j ω))
    (hStart : ∀ j ω, pairWallFamily outer inner d j ω 0 = 0)
    (hMeas : ∀ j t, Measurable fun ω => pairWallFamily outer inner d j ω t)
    (hDetermined : ∀ j t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => pairWallFamily outer inner d j ω t) =ᵐ[d.measure]
        fun ω => f (centredField d.field d.originalMean ω))
    (hLocal : ∀ j, Sec6.IsEntranceHistoryLocal (pairWallFamily outer inner d j)
      (centredField d.field d.originalMean) d.measure) (q : ℝ≥0) :
    let F := fun ω => regHull d.driver d.lifetime q ω
    let C := (outer.target i d).domain
    let U := (inner.target i d).domain
    let EC := eventFilled outer.event C F
    let EU := eventFilled inner.event U F
    ∃ gC gU : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean EC (centredField d.translatedField d.coupledMean) d.measure gC ∧
      IsLocalSetMean EU (centredField d.translatedField d.coupledMean) d.measure gU ∧
      ∀ᵐ ω ∂d.measure, ω ∈ outer.event → ω ∈ inner.event → ∀ vC vU : ℂ → ℝ,
        InnerProductSpace.HarmonicOnNhd vC (H \ EC ω) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ EC ω →
          gC ω φ = ∫ z, vC z * φ z) →
        InnerProductSpace.HarmonicOnNhd vU (H \ EU ω) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ EU ω →
          gU ω φ = ∫ z, vU z * φ z) → U ω ⊆ C ω → d.curve ω q ∈ U ω →
        let O := relChart (outer.target i d).baseChart (outer.target i d).curve
          (outer.visitCapacity d ω q).toNNReal ω
        let I := relChart (inner.target i d).baseChart (inner.target i d).curve
          (inner.visitCapacity d ω q).toNNReal ω
        ∀ (W : ℝ → ℝ), Continuous W → W 0 = 0 →
          O = ((outer.target i d).baseChart ω).loewner W (outer.visitCapacity d ω q).toNNReal →
          ∀ (x : ℝ) (a : ℝ → ℂ),
          QuantumZipper.IsForwardSol W x (outer.visitCapacity d ω q).toNNReal a →
          ∀ r : ℝ, 0 < r →
          H ∩ ball ((a (outer.visitCapacity d ω q).toNNReal).re : ℂ) r ⊆
            ((pocketTransitionChart O I).dom : Set ℂ) →
          Tendsto (fun z => vU (O.2.1 z) - vC (O.2.1 z))
            (𝓝[H] ((a (outer.visitCapacity d ω q).toNNReal).re : ℂ)) (𝓝 0) := by
  obtain ⟨gC, gU, hgC, hgU, hGood⟩ := exists_original_time_germ_comparison hOuter hInner
    hTransport hTranslate hu hh hCoupling hu' hKilled hLife hCont hStart hMeas hDetermined hLocal q
  refine ⟨gC, gU, hgC, hgU, ?_⟩
  filter_upwards [hGood, ae_regHull_eq hCoupling hLife] with ω hGerm hHull hωO hωI
    vC vU hvC hRepC hvU hRepU hUC hvisit _O _I W hW hW0 hCurrent x a hSurvives r hr hCollar
  have hEventO : ω ∈ (outer.target i d).event := by rwa [target_event]
  have hEventI : ω ∈ (inner.target i d).event := by rwa [target_event]
  have hO := (isDomainChart_relChart_visitCapacity hOuter (hCont 0) (hCont 1)
    hEventO q.coe_nonneg (hUC hvisit)).1
  have hI := (isDomainChart_relChart_visitCapacity hInner (hCont 0) (hCont 2)
    hEventI q.coe_nonneg hvisit).1
  have hIncl := current_domain_inclusion_at_visit hOuter hInner (hCont 0) (hCont 1) (hCont 2)
    hEventO hEventI hUC q.coe_nonneg hvisit
  have hDomO := relChart_dom_visitCapacity hOuter (hCont 0) (hCont 1) hEventO q.coe_nonneg (hUC hvisit)
  have hDomI := relChart_dom_visitCapacity hInner (hCont 0) (hCont 2) hEventI q.coe_nonneg hvisit
  rw [← hHull q] at hDomO hDomI
  have hNeighborhood := initial_neighborhood_at_surviving_visit hOuter hInner
    (hCont 0) (hCont 1) (hCont 2) hEventO hEventI hUC q.coe_nonneg hvisit
    hW hW0 hCurrent hSurvives hr hCollar
  exact hGerm hωO hωI vC vU hvC hRepC hvU hRepU _ _ hO hI hIncl hDomO hDomI
    _ _ r hNeighborhood hr hCollar
    (tendsto_currentVisitLanding hOuter (hCont 0) (hCont 1) hEventO q.coe_nonneg (hUC hvisit) _)

end InteractingSLE.Wire.Current.SideTest
