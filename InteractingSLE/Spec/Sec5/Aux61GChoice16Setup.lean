/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GChoice16Compare
import InteractingSLE.Spec.Sec5.Aux61SlitWZChoices
import InteractingSLE.Spec.Sec5.Aux61SlitWZTopology

/-! # Construct the literal choice family's comparison prerequisites

The existing slit results give the restart and physical stopping clauses.
The cut restart facts and its initial marked-set measurability therefore
need no comparison or completed-window premise.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GChoice16
open Aux61SlitW Aux61R1C Aux61Asm2 Aux61FibData Aux61GInst Aux61ULoc Aux61GR1F
open Aux61Marks
open LawUnique GlueCond
universe u

variable {S : SourceSetting.{u}} (C : RestartChoices S)
  (hsel : ∀ i, MeasurableSet (C.selected i)) (w : WindowFields C.toR1Restart)
  (hg : ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i →
    SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
      (cfHullQ (rationalTime S.s) p.2) (rationalTime (C.toR1Restart.q i))
      (sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p))
  (V : Aux61SlitWZ.SeedWindows C)
  (hfinite : ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i →
    ∀ z ∈ closure (C.toR1Restart.data i).buffer ∩ Hbar,
      boundedInverse (sourceChart C.fam (rationalTime S.s)
        S.own.W S.own.VL S.own.VR S.life i p) z ≠ 1)
include hsel w hg V hfinite

/-- The literal chosen source has the canonical record restart facts,
before a comparison or any future capture is supplied. -/
theorem choice_record_restart : RecordRestartFacts S C.fam where
  selected_measurable := C.selected_measurable hsel
  chart_measurable := fun i => (C.toR1Restart.chart_spec C.hasChart i).1
  event_measurable := (eventFacts_of_eq_preimage S C.fam (C.selected_measurable hsel)
    (fun _ => rfl)).1
  contact_measurable := C.toR1Restart.measurable_contact
  open_window := w.open_window
  zero_window := w.zero_window
  clearance := w.clearance
  kappa := w.kappa
  reference := w.reference
  event_version := fun _ => Eventually.of_forall fun _ => rfl
  physical_stop := Aux61SlitWZ.physical_stop_of_finite_buffer C hsel hg hfinite
  geometric := fun i => by
    filter_upwards [Aux61SlitWZ.geometric_of_chart_geometry C hsel hg V i] with p hp he
    obtain ⟨hm, hl, hin, hland, hh⟩ := hp he
    exact ⟨(C.toR1Restart.chart_spec C.hasChart i).2.1 _, hm, hl, hin, hland,
      (C.toR1Restart.chart_spec C.hasChart i).2.2.2 _, hh⟩

/-- All restart facts of the exact cut family consumed by `ChoiceInputs`.
No comparison or completion field is used to establish them. -/
theorem choice_cut_restart :
    SourceRestartFacts (cutSource S (withRecordPath S C.fam)) (rationalTime S.s)
      S.own.W S.own.VL S.own.VR S.life (μ := S.μ) S.κ := by
  have hR := choice_record_restart C hsel w hg V hfinite
  exact restart_cut_of hR.raw (path_version_withRecordPath S C.fam)
    (Aux61SlitWZ.ae_domain C)

omit w hg V hfinite in
/-- The same literal source uses the canonical physical contact rule. -/
theorem choice_contact_rule : ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i →
    contactRule (retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR))
      (rationalTime (C.toR1Restart.q i))
      (stopRec (rationalTime S.s) p.2, killedHistory S.own.W S.own.VL S.own.VR S.life p.1) =
      (C.fam.start i : ℝ≥0∞) + C.fam.contact i p :=
  contact_rule_of_hit S C.fam
    (fun _ => retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR))
    (fun _ => isClosed_retObs _) (fun _ => retObs_nonempty _)
    (Aux61SlitW.r1_contact_hit_of_tipOff C.toR1Restart C.hasChart
      (Aux61SlitWZ.readers C hsel).tipOff)

/-- The initial actual marked set is recorded by its existing marks.
This is proved for the precise cut family, rather than assumed by the
comparison constructor. -/
theorem choice_cut_sets_recorded (i : C.Idx) :
    Measurable[(S.marksData (cutSource S (withRecordPath S C.fam))).baseMarks i 0, hittingSigma]
      ((S.marksData (cutSource S (withRecordPath S C.fam))).baseSets i 0) := by
  exact sets_marks_cut_of (choice_cut_restart C hsel w hg V hfinite)
    (fun _ => measurable_contactRule
      (measurable_infDist_retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR)) _)
    (fun _ => isGalmarinoRule_contactRule _ _) (choice_contact_rule C hsel) i 0

end InteractingSLE.Sec5.Aux61GChoice16
