/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInCensusVersions

/-!
# Mean versions fixed for a countable family of incoming candidates

PROVE-POCKET-SIDEIN. Choose a mean for every candidate and deterministic
original time before taking the countable rational-time harmonicity event.
There is no claim of joint time measurability or of an all-real-times event.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketStopWalls Sec7.PocketStopWallsFin
  Sec7.PocketWordPerQ LocalSets WholeField WangWu

/-- One assignment of actual local means to fixed candidates and original
times. Rational-time harmonicity holds simultaneously before selection. -/
theorem exists_original_mean_family {Ω : Type} [mΩ : MeasurableSpace Ω]
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
    (hCont : ∀ j k ω, Continuous (pairWallFamily (J j) (J j) d k ω))
    (hStart : ∀ j k ω, pairWallFamily (J j) (J j) d k ω 0 = 0)
    (hMeas : ∀ j k t, Measurable fun ω => pairWallFamily (J j) (J j) d k ω t)
    (hDetermined : ∀ j k t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => pairWallFamily (J j) (J j) d k ω t) =ᵐ[d.measure]
        fun ω => f (centredField d.field d.originalMean ω))
    (hLocal : ∀ j k, Sec6.IsEntranceHistoryLocal (pairWallFamily (J j) (J j) d k)
      (centredField d.field d.originalMean) d.measure) :
    ∃ G : ι → ℝ≥0 → Ω → DistOn upperHalfPlaneOpens,
      (∀ j q, IsLocalSetMean (eventFilled (J j).event ((J j).target i d).domain
        (fun ω => regHull d.driver d.lifetime q ω))
        (centredField d.translatedField d.coupledMean) d.measure (G j q)) ∧
      ∀ᵐ ω ∂d.measure, ∀ (j : ι) (r : ℚ),
        IsHarmonicDistOn (G j (r : ℝ).toNNReal ω)
          (H \ eventFilled (J j).event ((J j).target i d).domain
            (fun ω => regHull d.driver d.lifetime (r : ℝ).toNNReal ω) ω) := by
  have hExists : ∀ (j : ι) (q : ℝ≥0), ∃ g : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (eventFilled (J j).event ((J j).target i d).domain
        (fun ω => regHull d.driver d.lifetime q ω))
        (centredField d.translatedField d.coupledMean) d.measure g := by
    intro j q
    exact (local_facts_at_original_time (hReady j) hTransport hTranslate hu hh hCoupling hu'
      hKilled hLife (hCont j) (hStart j) (hMeas j) (hDetermined j) (hLocal j) q).2.2
  choose G hG using hExists
  exact ⟨G, hG, ae_all_iff.2 fun j => ae_all_iff.2 fun r : ℚ =>
    (hG j (r : ℝ).toNNReal).2.1⟩

end InteractingSLE.Wire.Current.SideTest
