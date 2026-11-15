/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC5Cover
import InteractingSLE.Spec.Sec7.SideC5Facts
import InteractingSLE.Spec.Sec7.PocketSideInZeroRefTimes

/-!
# The native collar off exceptional fibres with compatible visit references

PROVE-SIDE-COLLAR2 continuation. Reference charts and actual inherited lift
limits are proved for this concrete family. The raw-reference facts use
the same hulls, records and lifts. The remaining positive-time inputs are
R.5's old-chart increment laws and the source-shaped own-height cover off
exceptional physical fibres. The initial slice is supplied separately.
Aux29CorLate consumes this restricted collar to obtain the full side-limit
conclusion without asserting collars at exceptional fibres.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire

open Current Sec7 Sec7.PocketStopSide Sec7.PocketStop Sec7.PocketTraversal
  Sec7.Lemma71C Sec7.PocketCoupling

/-- The native collar at positive capacities for the installed original
visit references. Charts and ZERO inherited lift difference are proved;
R.5's increment laws and the own-height/word cover are named inputs. -/
theorem lateSideCollarPosExc_visitReferences
    {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    [IsProbabilityMeasure d.measure] (side : SideTest Ω → Late.SideData Ω)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (s : SideTest Ω → ℕ → ℝ≥0) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ seed ω, Continuous (d.leftWall seed ω))
    (hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure
      d.filtration d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hLife : ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤)
    (hLaw : LateSideIncrementLaws i d
      (fun j => (side j).withVisitReferences i j d hKilled (s j))
      (fun j r ω => j.referenceVisitChart i d ω (s j r))
      (fun j q r => j.referenceVisitEvent i d (s j r) q))
    (hCover : VisitReferenceHeightCoverPosExc i d side s X) :
    ∀ q : ℝ≥0, 0 < q → LateSideCollarAtExc i d
      (fun j => (side j).withVisitReferences i j d hKilled (s j)) X q := by
  intro q hq
  exact lateSideCollarAtExc_of_incrementLaws i d
    (fun j => (side j).withVisitReferences i j d hKilled (s j))
    (fun j r ω => j.referenceVisitChart i d ω (s j r))
    (fun j q r => j.referenceVisitEvent i d (s j r) q) X
    (visit_reference_charts i d side hKilled s hRc hLc) hLaw q
    (lateSideCoverAtExc_visitReferences i d side hKilled s X hRc hLc hCoupling hLife
      hCover q hq)

/-- The full restricted native collar follows after its initial clause
is supplied separately. An old interior visit cannot serve at capacity zero. -/
theorem lateSideCollarExc_visitReferences_of_initial
    {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    [IsProbabilityMeasure d.measure] (side : SideTest Ω → Late.SideData Ω)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (s : SideTest Ω → ℕ → ℝ≥0) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ seed ω, Continuous (d.leftWall seed ω))
    (hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure
      d.filtration d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hLife : ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤)
    (hLaw : LateSideIncrementLaws i d
      (fun j => (side j).withVisitReferences i j d hKilled (s j))
      (fun j r ω => j.referenceVisitChart i d ω (s j r))
      (fun j q r => j.referenceVisitEvent i d (s j r) q))
    (hCover : VisitReferenceHeightCoverPosExc i d side s X)
    (hInitial : LateSideCollarAtExc i d
      (fun j => (side j).withVisitReferences i j d hKilled (s j)) X 0) :
    LateSideCollarExc i d
      (fun j => (side j).withVisitReferences i j d hKilled (s j)) X := by
  exact lateSideCollarExc_of_pos_and_zero i d
    (fun j => (side j).withVisitReferences i j d hKilled (s j)) X
    (lateSideCollarPosExc_visitReferences i d side hKilled s X hRc hLc hCoupling hLife
      hLaw hCover) hInitial

end InteractingSLE.Wire
