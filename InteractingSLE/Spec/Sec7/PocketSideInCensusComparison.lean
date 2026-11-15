/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInCensusVersions

/-!
# Pair comparisons for mean versions fixed before selecting pairs

PROVE-POCKET-SIDEIN. The actual R.5 germ comparison holds for prescribed
local mean versions. Harmonic pairing uniqueness reconciles the versions
constructed by the pair theorem with those already chosen per candidate.
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

/-- The actual two-pocket germ for prescribed versions, with the same
surviving-access and shared-current-collar geometry as the landed result. -/
theorem ae_germ_comparison_at_surviving_visit {Ω : Type} [mΩ : MeasurableSpace Ω]
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
      (centredField d.field d.originalMean) d.measure) (q : ℝ≥0)
    {gC gU : Ω → DistOn upperHalfPlaneOpens}
    (hgC : IsLocalSetMean (eventFilled outer.event (outer.target i d).domain
      (fun ω => regHull d.driver d.lifetime q ω))
      (centredField d.translatedField d.coupledMean) d.measure gC)
    (hgU : IsLocalSetMean (eventFilled inner.event (inner.target i d).domain
      (fun ω => regHull d.driver d.lifetime q ω))
      (centredField d.translatedField d.coupledMean) d.measure gU) :
    let F := fun ω => regHull d.driver d.lifetime q ω
    let C := (outer.target i d).domain
    let U := (inner.target i d).domain
    let EC := eventFilled outer.event C F
    let EU := eventFilled inner.event U F
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
  obtain ⟨gC', gU', hgC', hgU', hGood⟩ := exists_germ_comparison_at_surviving_visit hOuter hInner
    hTransport hTranslate hu hh hCoupling hu' hKilled hLife hCont hStart hMeas hDetermined hLocal q
  have hh' := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData
    ⟨hCoupling.2.1, hCoupling.2.2.1⟩ hu'
  have hEqC := ae_mean_apply_eq_on_compl
    (measurable_original_filling hOuter (hCont 0) (hCont 1) (hMeas 0) (hMeas 1) hKilled q)
    hh'.measurable (fun ω => (original_filling_regular hOuter q ω).2) hgC hgC'
  have hEqU := ae_mean_apply_eq_on_compl
    (measurable_original_filling hInner (hCont 0) (hCont 2) (hMeas 0) (hMeas 2) hKilled q)
    hh'.measurable (fun ω => (original_filling_regular hInner q ω).2) hgU hgU'
  filter_upwards [hGood, hEqC, hEqU] with ω hGood hEqC hEqU
    hωC hωU vC vU hvC hRepC hvU hRepU
  exact hGood hωC hωU vC vU hvC
    (fun φ hφ => (hEqC φ hφ).symm.trans (hRepC φ hφ)) hvU
    (fun φ hφ => (hEqU φ hφ).symm.trans (hRepU φ hφ))

end InteractingSLE.Wire.Current.SideTest
