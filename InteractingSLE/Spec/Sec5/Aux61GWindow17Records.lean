/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow17Capture

/-! # Record and window fields of the constructed canonical source

The canonical family has its actual retained component and inherited
lift. The explicit countable capture choices supply the deterministic
window/reference fields and selected history cover.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWindow17
open Aux61SlitW Aux61R1C Aux61Asm2 Aux61FibData Aux61GR1F Aux61GWord LawUnique
universe u
variable {S : SourceSetting.{u}} (C : RestartChoices S)

/-- The canonical chart reads the component from the same initial record. -/
theorem canonicalFamily_record_domain : RecordDomainComponent S (canonicalFamily C) := by
  intro i
  let t : GoodTime S := ⟨C.q i.1, i.2⟩
  let B := baseChoices S t.1
  have R := Aux61SlitWZ.readers B (fun _ => MeasurableSet.univ)
  obtain ⟨b, hb⟩ := R.record_domain B.hasChart (baseIndex S t)
  exact ⟨b, fun y hy => hb y ⟨mem_univ _, hy.2⟩⟩

/-- Its physical component identity holds on the actual selected event. -/
theorem canonicalFamily_ae_domain : ∀ i, ∀ᵐ p ∂S.μ, p ∈ (canonicalFamily C).event i → ∃ b : ℂ,
    ((sourceChart (canonicalFamily C) (rationalTime S.s)
      S.own.W S.own.VL S.own.VR S.life i p).dom : Set ℂ) =
      Aux61Restart.restartComponent (GlueCond.cfHullQ (rationalTime S.s) p.2)
        (fun t : ℝ => S.path p.1 t.toNNReal) ((canonicalFamily C).start i) b :=
  dom_component_of_record S (canonicalFamily C) (canonicalFamily_record_domain C)
    (fun _ => Eventually.of_forall fun _ => rfl)

/-- The chosen lift is the physical inherited branch at every record,
rather than an arbitrary continuous lift. -/
theorem canonicalFamily_physical_lift (i : C.Idx) (y : SourceRecord S.nL S.nR) :
    ∀ z ∈ ((canonicalFamily C).chart i y).dom,
      ((canonicalFamily C).chart i y).2.2 z =
        (Aux61Restart.physicalRestartLog
          (Aux61Restart.stripTargetHull ((canonicalFamily C).chart i y).dom) z).im :=
  (recordChart_spec S ⟨C.q i.1, i.2⟩).lift y

/-- All five deterministic window/reference fields are proved for the
explicit countable family; no words or windows are supplied by the caller. -/
theorem captureChoices_window_fields (S : SourceSetting.{u}) :
    WindowFields (captureChoices S).toR1Restart where
  open_window i := (windowGeometry i.1.2).open_window
  zero_window i := (windowGeometry i.1.2).zero_window
  clearance _ := rfl
  kappa _ := rfl
  reference i := (intervalWord S i.1.1).reference

/-- The original source window event has an actual selected initial
record in the canonical family, without a supplied selection cover. -/
theorem captureChoices_history_cover (S : SourceSetting.{u}) : ∀ᵐ p ∂S.μ,
    S.windowEvent p → ∃ i,
      sourceRecord (canonicalFamily (captureChoices S)) (rationalTime S.s)
        S.own.W S.own.VL S.own.VR S.life i p ∈ (canonicalFamily (captureChoices S)).selected i := by
  filter_upwards [captureChoices_completed_cover S] with p hp hw
  obtain ⟨i, hi, -⟩ := hp hw
  exact ⟨i, hi.1⟩

end InteractingSLE.Sec5.Aux61GWindow17
