/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow17Canonical
import InteractingSLE.Spec.Sec5.Aux61SlitWXGeometry

/-! # Physical normalization for the time-indexed chart family

The fully certified chart is chosen once per retained time, then reused
with the requested windows and record selections. Every physical chart
geometry field is proved, with no normalization hypothesis.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWindow17
open Aux61SlitW Aux61R1C Aux61Asm2 Aux61FibData LawUnique
universe u
variable {S : SourceSetting.{u}} (C : RestartChoices S)

/-- The requested source family with the canonical, fully certified
time-indexed chart. Its records, physical contact and data are retained. -/
def canonicalFamily : SourceRestartData S.Ω S.nL S.nR :=
  { C.fam with chart := fun i => recordChart S ⟨C.q i.1, i.2⟩ }

/-- The canonical family reads exactly the same initial record. -/
theorem canonicalFamily_record (i : C.Idx) :
    sourceRecord (canonicalFamily C) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i =
      C.record i.1 := rfl

/-- Its chart is measurable on the retained record space. -/
theorem canonicalFamily_chart_measurable (i : C.Idx) :
    IsMeasChart ((canonicalFamily C).chart i) :=
  (recordChart_spec S ⟨C.q i.1, i.2⟩).measurable

/-- Its chart is conformal at every retained record. -/
theorem canonicalFamily_chart_conformal (i : C.Idx) (y : SourceRecord S.nL S.nR) :
    ((canonicalFamily C).chart i y).IsConformal :=
  (recordChart_spec S ⟨C.q i.1, i.2⟩).conformal y

/-- All physical chart-geometry clauses for the constructed family,
including the current access, original target, infinity and physical lift.
No selected-set measurability or chart-normalization premise is needed. -/
theorem canonicalFamily_geometry : ∀ i, ∀ᵐ p ∂S.μ, p ∈ (canonicalFamily C).event i →
    SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
      (GlueCond.cfHullQ (rationalTime S.s) p.2) ((canonicalFamily C).start i)
      (sourceChart (canonicalFamily C) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p) := by
  intro i
  let t : GoodTime S := ⟨C.q i.1, i.2⟩
  let B := baseChoices S t.1
  have R := Aux61SlitWZ.readers B (fun _ => MeasurableSet.univ)
  filter_upwards [R.ae_geometry B.hasChart (baseIndex S t)] with p hp he
  change C.record i.1 p ∈ C.selected i.1 ∩ C.good i.1 at he
  have hb : p ∈ B.toR1Restart.event (baseIndex S t) := ⟨mem_univ _, he.2⟩
  exact hp hb

/-- The canonical chart stays fixed when a window or selected-record
restriction is refined at the same retained rational time. -/
theorem canonicalFamily_chart_eq {D : RestartChoices S} (i : C.Idx) (j : D.Idx)
    (hq : C.q i.1 = D.q j.1) :
    (canonicalFamily C).chart i = (canonicalFamily D).chart j :=
  recordChart_eq_of_time_eq S _ _ hq

end InteractingSLE.Sec5.Aux61GWindow17
