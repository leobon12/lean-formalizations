/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInSurviveIncrementGerm

/-!
# The actual old-to-current mean increment at a surviving incoming access

PROVE-POCKET-SIDEIN. Both labeled laws and both mean versions are constructed
at fixed original time. Actual current charts, landings and local activity
are supplied internally; only survival in the actual own driver remains.
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

/-- The old-to-current physical mean increment is zero at every surviving
original real own coordinate, uniformly after fixing the original time. -/
theorem exists_initial_current_germ_at_surviving_visit {Ω : Type} [mΩ : MeasurableSpace Ω]
    {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    [IsProbabilityMeasure d.measure] (hj : j.Ready d)
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
    (hCont : ∀ k ω, Continuous (pairWallFamily j j d k ω))
    (hStart : ∀ k ω, pairWallFamily j j d k ω 0 = 0)
    (hMeas : ∀ k t, Measurable fun ω => pairWallFamily j j d k ω t)
    (hDetermined : ∀ k t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => pairWallFamily j j d k ω t) =ᵐ[d.measure]
        fun ω => f (centredField d.field d.originalMean ω))
    (hLocal : ∀ k, Sec6.IsEntranceHistoryLocal (pairWallFamily j j d k)
      (centredField d.field d.originalMean) d.measure) (q : ℝ≥0) :
    let C := (j.target i d).domain
    let F := fun ω => regHull d.driver d.lifetime q ω
    let E0 := eventFilled j.event C (fun _ => ∅)
    let Eq := eventFilled j.event C F
    ∃ g0 gq : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean E0 (centredField d.translatedField d.coupledMean) d.measure g0 ∧
      IsLocalSetMean Eq (centredField d.translatedField d.coupledMean) d.measure gq ∧
      ∀ᵐ ω ∂d.measure, ω ∈ j.event → ∀ v0 vq : ℂ → ℝ,
        InnerProductSpace.HarmonicOnNhd v0 (H \ E0 ω) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ E0 ω →
          g0 ω φ = ∫ z, v0 z * φ z) →
        InnerProductSpace.HarmonicOnNhd vq (H \ Eq ω) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ Eq ω →
          gq ω φ = ∫ z, vq z * φ z) → d.curve ω q ∈ C ω →
        let O := relChart (j.target i d).baseChart (j.target i d).curve
          (j.visitCapacity d ω q).toNNReal ω
        ∀ (W : ℝ → ℝ), Continuous W → W 0 = 0 →
          O = ((j.target i d).baseChart ω).loewner W (j.visitCapacity d ω q).toNNReal →
          ∀ (x : ℝ) (a : ℝ → ℂ),
          QuantumZipper.IsForwardSol W x (j.visitCapacity d ω q).toNNReal a →
          Tendsto (fun z => vq (O.2.1 z) - v0 (O.2.1 z))
            (𝓝[H] ((a (j.visitCapacity d ω q).toNNReal).re : ℂ)) (𝓝 0) := by
  obtain ⟨g0, gq, hg0, hgq, hm0, hmq, hl0, hlq, hPair, hu0, huq⟩ :=
    initial_current_reference_facts hj hTransport hTranslate hu hh hCoupling hu'
      hKilled hLife hCont hStart hMeas hDetermined hLocal q
  have hh' : IsZeroBoundaryGFF upperHalfPlaneOpens
      (centredField d.translatedField d.coupledMean) d.measure :=
    Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData
      ⟨hCoupling.2.1, hCoupling.2.2.1⟩ hu'
  have hGood := ae_initial_current_germ_of_local_activity hh' hm0 hmq hl0 hlq hPair hu0 huq hg0 hgq
  refine ⟨g0, gq, hg0, hgq, ?_⟩
  filter_upwards [hGood, ae_regHull_eq hCoupling hLife] with ω hGerm hHull hω
    v0 vq hv0 hRep0 hvq hRepq hvisit _O W hW hW0 hCurrent x a hSurvives
  have hEvent : ω ∈ (j.target i d).event := by rwa [target_event]
  have hc := (isDomainChart_relChart_visitCapacity hj (hCont 0) (hCont 1) hEvent q.coe_nonneg hvisit).1
  have hDomain := relChart_dom_visitCapacity hj (hCont 0) (hCont 1) hEvent q.coe_nonneg hvisit
  rw [← hHull q] at hDomain
  have hActive := (active_near_surviving_visit hj (hCont 0) (hCont 1) hEvent q.coe_nonneg hvisit
    hW hW0 hCurrent hSurvives).1
  exact hGerm hω v0 vq hv0 hRep0 hvq hRepq _ hc hDomain _ _ hActive
    (tendsto_currentVisitLanding hj (hCont 0) (hCont 1) hEvent q.coe_nonneg hvisit _)

end InteractingSLE.Wire.Current.SideTest
