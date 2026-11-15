/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC7Mean
import InteractingSLE.Spec.Sec7.SideC7Phase

/-!
# Native collar with the initial mean formula separated from R.5

PROVE-SIDE-COLLAR2. The initial collar and every initial boundary limit
follow from one initial interior mean formula. The actual residual law
and positive-capacity own-height cover remain explicit inputs.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire

open Current

/-- The native collar, using the initial interior mean formula instead
of an assumed initial boundary-height or initial-collar predicate. -/
theorem lateSideCollarExc_visitReferences_of_initialMeanFormula
    {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    [IsProbabilityMeasure d.measure] (side : SideTest Ω → Late.SideData Ω)
    (G : SideTest Ω → Ω → DistOn upperHalfPlaneOpens)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (s : SideTest Ω → ℕ → ℝ≥0) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ)
    (hZero : ∀ j, ∃ r, s j r = 0)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ seed ω, Continuous (d.leftWall seed ω))
    (hRm : ∀ t, Measurable fun ω => d.rightWall ω t)
    (hLm : ∀ seed t, Measurable fun ω => d.leftWall seed ω t)
    (hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure
      d.filtration d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hLife : ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤)
    (hLaw : LateSideIncrementLaws i d
      (fun j => (side j).withVisitReferences i j d hKilled (s j))
      (fun j r ω => j.referenceVisitChart i d ω (s j r))
      (fun j q r => j.referenceVisitEvent i d (s j r) q))
    (hCover : VisitReferenceHeightCoverPosExc i d side s X)
    (hFormula : InitialPocketMeanFormula i d side G) :
    LateSideCollarExc i d
      (fun j => (side j).withVisitReferences i j d hKilled (s j)) X := by
  exact lateSideCollarExc_visitReferences_of_initialHeights i d side hKilled s X hZero
    hRc hLc hRm hLm hCoupling hLife hLaw hCover
    (initialReferenceHeightsExc_of_meanFormula i d side G hKilled hRc hLc hRm hLm hCoupling
      hFormula X)

end InteractingSLE.Wire
