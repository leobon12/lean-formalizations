/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInSurviveIncrement
import InteractingSLE.Spec.Sec7.PocketSideInRealLanding

/-!
# Exact incoming height transport with the mean increment proved

PROVE-POCKET-SIDEIN. The actual initial/current reference laws produce the
physical mean germ. The frozen own hydrodynamic lift has zero argument at
surviving real points, so the exact initial height remains unchanged.
The Aux. 119/Aux. 120 initial height is still an explicit geometric input.
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

/-- Exact incoming heights in the actual common field frame, with no
separate initial-to-current physical mean-germ assumption. -/
theorem exists_exact_height_transport_at_surviving_visit {Ω : Type} [mΩ : MeasurableSpace Ω]
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
          ∀ b : ℝ,
          Tendsto (sideMean i.kappa ((j.target i d).baseChart ω) d.coupledMean v0)
            (𝓝[H] (x : ℂ)) (𝓝 b) →
          Tendsto (sideMean i.kappa O d.coupledMean vq)
            (𝓝[H] ((a (j.visitCapacity d ω q).toNNReal).re : ℂ)) (𝓝 b) := by
  obtain ⟨g0, gq, hg0, hgq, hGood⟩ := exists_initial_current_germ_at_surviving_visit hj
    hTransport hTranslate hu hh hCoupling hu' hKilled hLife hCont hStart hMeas hDetermined hLocal q
  refine ⟨g0, gq, hg0, hgq, ?_⟩
  filter_upwards [hGood] with ω hGerm hω v0 vq hv0 hRep0 hvq hRepq hvisit
    _O W hW hW0 hCurrent x a hSurvives b hInitialHeight
  have hEvent : ω ∈ (j.target i d).event := by rwa [target_event]
  have hBase := (isDomainChart_baseChart hj (hCont 0) (hCont 1) hEvent).1
  have hPhysical := hGerm hω v0 vq hv0 hRep0 hvq hRepq hvisit W hW hW0 hCurrent x a hSurvives
  change Tendsto (fun z => vq (_O.2.1 z) - v0 (_O.2.1 z))
    (𝓝[H] ((a (j.visitCapacity d ω q).toNNReal).re : ℂ)) (𝓝 0) at hPhysical
  rw [hCurrent] at hPhysical ⊢
  exact tendsto_exact_height_at_surviving_real hBase hW hW0
    (j.visitCapacity d ω q).toNNReal.coe_nonneg hSurvives hInitialHeight hPhysical

end InteractingSLE.Wire.Current.SideTest
