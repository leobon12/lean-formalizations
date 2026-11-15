/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC6Initial
import InteractingSLE.Spec.Sec7.SideC5Collar

/-!
# Native collar assembly with an explicit initial-height input

PROVE-SIDE-COLLAR2. The zero reference supplies the initial comparison
and lift clauses. Positive capacities use the landed own-chain theorem.
The remaining inputs are the residual old-chart law, the positive own-height
cover, and the initial pocket's own heights. None is asserted proved here.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

/-- The fixed rational original-time family includes original zero at
the index of the rational number zero. -/
theorem rationalOriginalTime_zero : rationalOriginalTime (Denumerable.eqv ℚ 0) = 0 := by
  rw [rationalOriginalTime_eqv, Rat.cast_zero]
  exact Real.toNNReal_zero

end InteractingSLE.Wire.Current.SideTest

namespace InteractingSLE.Wire

open Current Sec7 Sec7.PocketStop Sec7.PocketStopSide

/-- Full native collar off exceptional fibres. The initial clause is
derived from the initial own heights; it is no longer a collar hypothesis. -/
theorem lateSideCollarExc_visitReferences_of_initialHeights
    {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    [IsProbabilityMeasure d.measure] (side : SideTest Ω → Late.SideData Ω)
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
    (hHeight : InitialReferenceHeightsExc i d side X) :
    LateSideCollarExc i d
      (fun j => (side j).withVisitReferences i j d hKilled (s j)) X := by
  exact lateSideCollarExc_visitReferences_of_initial i d side hKilled s X hRc hLc hCoupling
    hLife hLaw hCover (lateSideCollarAtZeroExc_of_initialReferenceHeights i d side hKilled
      s X hZero hRc hLc hRm hLm hCoupling hHeight)

end InteractingSLE.Wire
