/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInCensusVersions

/-!
# Exact height transport for mean versions chosen per candidate

PROVE-POCKET-SIDEIN. Initial and current mean versions can be fixed once
for each candidate before any realized pair is selected. Agreement on all
active tests transfers the landed exact-height transport to those versions.
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

/-- Exact height transport for prescribed initial and current local means.
The actual initial height and surviving own coordinate remain explicit. -/
theorem ae_exact_height_transport_at_surviving_visit {Ω : Type} [mΩ : MeasurableSpace Ω]
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
      (centredField d.field d.originalMean) d.measure) (q : ℝ≥0)
    {g0 gq : Ω → DistOn upperHalfPlaneOpens}
    (hg0 : IsLocalSetMean (eventFilled j.event (j.target i d).domain (fun _ => ∅))
      (centredField d.translatedField d.coupledMean) d.measure g0)
    (hgq : IsLocalSetMean (eventFilled j.event (j.target i d).domain
      (fun ω => regHull d.driver d.lifetime q ω))
      (centredField d.translatedField d.coupledMean) d.measure gq) :
    let C := (j.target i d).domain
    let F := fun ω => regHull d.driver d.lifetime q ω
    let E0 := eventFilled j.event C (fun _ => ∅)
    let Eq := eventFilled j.event C F
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
  obtain ⟨g0', gq', hg0', hgq', hGood⟩ := exists_exact_height_transport_at_surviving_visit hj
    hTransport hTranslate hu hh hCoupling hu' hKilled hLife hCont hStart hMeas hDetermined hLocal q
  have hh' := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData
    ⟨hCoupling.2.1, hCoupling.2.2.1⟩ hu'
  have hm0 := measurable_original_filling hj (i := i)
    (hCont 0) (hCont 1) (hMeas 0) (hMeas 1) hKilled 0
  have hreg0 := original_filling_regular hj (i := i) 0
  rw [original_filling_zero] at hm0 hreg0
  have hEq0 := ae_mean_apply_eq_on_compl hm0 hh'.measurable (fun ω => (hreg0 ω).2) hg0 hg0'
  have hEqq := ae_mean_apply_eq_on_compl
    (measurable_original_filling hj (hCont 0) (hCont 1) (hMeas 0) (hMeas 1) hKilled q)
    hh'.measurable (fun ω => (original_filling_regular hj q ω).2) hgq hgq'
  filter_upwards [hGood, hEq0, hEqq] with ω hGood hEq0 hEqq
    hω v0 vq hv0 hRep0 hvq hRepq
  exact hGood hω v0 vq hv0
    (fun φ hφ => (hEq0 φ hφ).symm.trans (hRep0 φ hφ)) hvq
    (fun φ hφ => (hEqq φ hφ).symm.trans (hRepq φ hφ))

end InteractingSLE.Wire.Current.SideTest
