/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWABBoundary

/-! # A Borel seed-clearance event on the actual initial records

Both the old boundary and the bounded inverse are read from the retained
records. The physical geometry field guarantees this event almost surely;
its measurability and pointwise clearance are proved here.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitWAB
open Aux61SlitW Aux61R1C Aux61Asm2 Aux61Restart Aux61FibData Aux61GInst Aux61ULoc LawUnique
universe u
variable {S : SourceSetting.{u}} (C : RestartChoices S)

/-- Distance to the compact old boundary is measurable from certified
initial records at every fixed model point. -/
theorem measurable_infDist_recordBoundary (i : C.Idx) (z : ℂ) :
    Measurable (fun y : certifiedSelection C i =>
      infDist z (recordBoundary (rationalTime S.s) y.1.1)) :=
  measurable_infDist_oldModelBoundary
    (fun y => continuousOn_recordTrace (rationalTime_s_pos S) y.2.2)
    (fun t => (measurable_recTrace t).comp (measurable_fst.comp measurable_subtype_coe)) z

/-- The bounded inverse at a fixed closed-half-plane point is measurable
on the actual certified record event. -/
theorem measurable_inverse_on_certifiedSelection (hsel : ∀ i, MeasurableSet (C.selected i))
    (i : C.Idx) {z : ℂ} (hz : z ∈ Hbar) :
    Measurable (fun y : certifiedSelection C i =>
      boundedInverse (C.toR1Restart.chart C.hasChart i y.1) z) := by
  have hm := Aux61SlitWAA.measurable_boundedInverse_Hbar
    (measurableSet_certifiedSelection C hsel i) (C.toR1Restart.chart_spec C.hasChart i).1
    (fun y _ => (C.toR1Restart.chart_spec C.hasChart i).2.1 y)
    (fun _ hy => record_extension C i hy.1 hy.2) hz
  have hp : ∀ y : certifiedSelection C i,
      ((certifiedSelection C i).indicator fun x =>
        boundedInverse (C.toR1Restart.chart C.hasChart i x) z) y.1 =
      boundedInverse (C.toR1Restart.chart C.hasChart i y.1) z :=
    fun y => indicator_of_mem y.2 _
  simpa only [Function.comp_def, hp] using hm.comp
    (measurable_subtype_coe : Measurable (Subtype.val : certifiedSelection C i → SourceRecord S.nL S.nR))

/-- The seed's model distance from the old boundary is a measurable
function of the initial record. -/
theorem measurable_seedDistance (hsel : ∀ i, MeasurableSet (C.selected i)) (i : C.Idx) :
    Measurable (fun y : certifiedSelection C i =>
      infDist (boundedInverse (C.toR1Restart.chart C.hasChart i y.1) 0)
        (recordBoundary (rationalTime S.s) y.1.1)) :=
  Aux61R1C.measurable_comp_of_continuous_of_measurable
    (u := fun z (y : certifiedSelection C i) => infDist z (recordBoundary (rationalTime S.s) y.1.1))
    (fun _ => continuous_infDist_pt _) (measurable_infDist_recordBoundary C i)
    (measurable_inverse_on_certifiedSelection C hsel i (z := (0 : ℂ)) zero_mem_Hbar)

/-- Certified initial records whose selected seed avoids the old boundary. -/
def seedRecords (i : C.Idx) : Set (SourceRecord S.nL S.nR) :=
  {y | y ∈ certifiedSelection C i ∧
    0 < infDist (boundedInverse (C.toR1Restart.chart C.hasChart i y) 0)
      (recordBoundary (rationalTime S.s) y.1)}

theorem measurableSet_seedRecords (hsel : ∀ i, MeasurableSet (C.selected i)) (i : C.Idx) :
    MeasurableSet (seedRecords C i) := by
  have hm := (measurableSet_certifiedSelection C hsel i).subtype_image
    (measurableSet_lt (measurable_const (a := (0 : ℝ))) (measurable_seedDistance C hsel i))
  convert hm using 1
  ext y
  constructor
  · intro hy
    exact ⟨⟨y, hy.1⟩, hy.2, rfl⟩
  · rintro ⟨⟨y, hy⟩, hpos, rfl⟩
    exact ⟨hy, hpos⟩

/-- Every record in the Borel seed event has a positive free real collar.
This assertion is pointwise on records and does not use a continuation. -/
theorem seed_gap_of_mem_seedRecords (i : C.Idx) {y : SourceRecord S.nL S.nR}
    (hy : y ∈ seedRecords C i) : ∃ δ > 0, ∀ a : ℝ, |a| < δ →
      boundedInverse (C.toR1Restart.chart C.hasChart i y) (a : ℂ) ∉
        recordBoundary (rationalTime S.s) y.1 := by
  apply exists_real_seed_gap (record_extension C i hy.1.1 hy.1.2).2
    (isCompact_recordBoundary (rationalTime_s_pos S) hy.1.2).isClosed
  intro hm
  exact hy.2.ne' (infDist_zero_of_mem hm)

end InteractingSLE.Sec5.Aux61SlitWAB
