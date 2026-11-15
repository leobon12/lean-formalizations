/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC5Relative
import InteractingSLE.Spec.Sec7.PocketSideInZeroRefData

/-!
# Original references with their actual visit-chart lifts

PROVE-SIDE-COLLAR2 continuation. Install the original-time hulls and their
retained records using the existing constructor, and use their actual
visit-chart derivative lifts. Reference-chart compatibility is proved on
the explicit live visit event. Other side fields retain their supplied data.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire

open Current Sec7 Sec7.PocketStopSide Sec7.PocketStopWallsFin Sec7.PocketStop
  Sec7.PocketTraversal Sec7.Lemma71C Sec7.PocketCoupling

/-- Actual original hulls and records, with the derivative lifts of their
own visit charts. The phase, offset and all nonreference fields are inherited. -/
def Late.SideData.withVisitReferences {Ω : Type} [MeasurableSpace Ω]
    (e : Late.SideData Ω) (i : BothLow) (j : SideTest Ω) (d : WordObjects Ω)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (s : ℕ → ℝ≥0) : Late.SideData Ω :=
  { e.withOriginalReferences j d hKilled s with
    lift := fun r ω => (j.referenceVisitChart i d ω (s r)).2.2 }

/-- The installed data uses the literal original reference fields and
actual visit lifts, while retaining the supplied phase and common offset. -/
theorem Late.SideData.withVisitReferences_fields {Ω : Type} [MeasurableSpace Ω]
    (e : Late.SideData Ω) (i : BothLow) (j : SideTest Ω) (d : WordObjects Ω)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (s : ℕ → ℝ≥0) :
    let refs := e.withVisitReferences i j d hKilled s
    refs.level = 0 ∧
      refs.sets = (fun r ω => regHull d.driver d.lifetime (s r) ω) ∧
      refs.info = (fun r => j.originalReferenceInfo d hKilled (s r)) ∧
      refs.lift = (fun r ω => (j.referenceVisitChart i d ω (s r)).2.2) ∧
      refs.phase = e.phase ∧ refs.offset = e.offset := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The normalized native reference is the earlier capacity-reference
record on all samples, including off the initial event. -/
theorem visit_references_liveExt {Ω : Type} [MeasurableSpace Ω]
    {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω} (hj : j.Ready d)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (e : Late.SideData Ω) (s : ℕ → ℝ≥0) (r : ℕ) :
    let refs := e.withVisitReferences i j d hKilled s
    liveExt (j.target i d).event (j.target i d).curve (j.target i d).domain
      (refs.sets r) refs.level = j.capacityReference i d (s r) := by
  have h := original_references_liveExt (i := i) hj hKilled e s r
  simpa only [Late.SideData.withVisitReferences, Late.SideData.withOriginalReferences,
    Current.SideTest.capacityReference, Current.SideTest.target_event] using h

end InteractingSLE.Wire

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketStopWallsFin Sec7.PocketStop
  Sec7.PocketTraversal Sec7.Lemma71C

/-- The live event on which an original reference is an actual earlier
visit and its regularized hull agrees with the original hull. The last
identity is supplied simultaneously by `ae_regHull_eq` in the cover proof. -/
def referenceVisitEvent {Ω : Type} [MeasurableSpace Ω]
    (j : SideTest Ω) (i : BothLow) (d : WordObjects Ω) (s q : ℝ≥0) : Set Ω :=
  {ω | ω ∈ (j.target i d).event ∧
    (q : ℝ≥0∞) < capLife ((j.target i d).curve ω) ∧
    d.curve ω s ∈ (j.target i d).domain ω ∧ (j.visitCapacity d ω s).toNNReal ≤ q ∧
    regHull d.driver d.lifetime s ω =
      QuantumZipper.fwdHull (fun t : ℝ => d.driver t.toNNReal ω) s}

end InteractingSLE.Wire.Current.SideTest

namespace InteractingSLE.Wire

open Current Sec7 Sec7.PocketStopSide Sec7.PocketStopWallsFin Sec7.PocketStop
  Sec7.PocketTraversal Sec7.Lemma71C

/-- The native reference-chart obligation holds for the actual installed
visit references. Neither reference conformality nor domain nesting nor
reference-domain identification is a new hypothesis. -/
theorem visit_reference_charts {Ω : Type} [MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω) (side : SideTest Ω → Late.SideData Ω)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (s : SideTest Ω → ℕ → ℝ≥0)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ seed ω, Continuous (d.leftWall seed ω)) :
    LateSideReferenceCharts i d
      (fun j => (side j).withVisitReferences i j d hKilled (s j))
      (fun j r ω => j.referenceVisitChart i d ω (s j r))
      (fun j q r => j.referenceVisitEvent i d (s j r) q) := by
  intro j hj _ _ q r ω hω
  obtain ⟨hA, hq, hVisit, hOrder, hHull⟩ := hω
  have hOld := Current.SideTest.isDomainChart_capacityReference_at_visit
    hj hRc (hLc j.seed) hA (s j r) hVisit hHull
  have hIncl := relChart_dom_antitone (Current.SideTest.isDomainChart_baseChart
    hj hRc (hLc j.seed) hA).1 (Current.SideTest.isDrivenCurve_target hj ω hA) hq hOrder
  refine ⟨hA, hq, hOld.1, hIncl, ?_⟩
  rw [visit_references_liveExt hj hKilled (side j) (s j) r]
  exact hOld.coe_dom

end InteractingSLE.Wire
