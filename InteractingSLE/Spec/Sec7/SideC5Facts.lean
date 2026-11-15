/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC5Data

/-!
# Raw-reference obligations for the compatible visit reference family

PROVE-SIDE-COLLAR2 continuation. The raw-reference producer depends on the
reference hulls, level and records. Installing their actual visit-chart
lifts preserves all three fields, so the already proved raw law and native
prefix and open-complement facts apply to this same compatible family.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire

open Current Sec7 Sec7.PocketStopSide Sec7.PocketStopWalls Sec7.PocketStopWallsFin
  Sec7.PocketWordPerQ Sec7.PocketCoupling Sec7.PocketStop LocalSets WholeField WangWu

/-- The installed actual visit lifts share the same original hulls and
records as the proved raw-reference family, hence all three native raw
reference obligations hold for this same choice of side data. -/
theorem visit_references_facts {Ω : Type} [mΩ : MeasurableSpace Ω]
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
    (hCont : ∀ k ω, Continuous (j.pairWallFamily j d k ω))
    (hStart : ∀ k ω, j.pairWallFamily j d k ω 0 = 0)
    (hMeas : ∀ k t, Measurable fun ω => j.pairWallFamily j d k ω t)
    (hDetermined : ∀ k t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => j.pairWallFamily j d k ω t) =ᵐ[d.measure]
        fun ω => f (centredField d.field d.originalMean ω))
    (hLocal : ∀ k, Sec6.IsEntranceHistoryLocal (j.pairWallFamily j d k)
      (centredField d.field d.originalMean) d.measure)
    (e : Late.SideData Ω) (s : ℕ → ℝ≥0) :
    let refs := e.withVisitReferences i j d hKilled s
    ∀ r, locPrefixSigma (refs.info r) (j.target i d).event (j.target i d).curve refs.level ≤ mΩ ∧
      (∀ ω ∈ (j.target i d).event, IsOpen (H \ refs.sets r ω)) ∧
      PocketStopUnionLaw (refs.info r) (j.target i d).measure (j.target i d).event
        (j.target i d).curve (j.target i d).domain (refs.sets r) (j.target i d).zeroField refs.level := by
  exact original_references_facts hj hTransport hTranslate hu hh hCoupling hu'
    hKilled hLife hCont hStart hMeas hDetermined hLocal e s

end InteractingSLE.Wire
