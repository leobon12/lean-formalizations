/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow17Landing

/-! # Unconditional restart facts of the uniformly refined source

All window, stopping, geometric and normalization inputs are constructed.
Neither comparison means nor future completion is used in these facts.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWindow17
open Aux61SlitW Aux61R1C Aux61Asm2 Aux61FibData LawUnique
universe u

/-- The actual record restart facts, with all window and physical fields
proved for the refined family. -/
theorem refinedFamily_record_restart (S : SourceSetting.{u}) :
    RecordRestartFacts S (refinedFamily S) where
  selected_measurable := (refinedChoices S).selected_measurable (refinedChoices_selected_measurable S)
  chart_measurable := canonicalFamily_chart_measurable (refinedChoices S)
  event_measurable := (eventFacts_of_eq_preimage S (refinedFamily S)
    ((refinedChoices S).selected_measurable (refinedChoices_selected_measurable S)) (fun _ => rfl)).1
  contact_measurable := (refinedChoices S).toR1Restart.measurable_contact
  open_window := (refinedChoices_window_fields S).open_window
  zero_window := (refinedChoices_window_fields S).zero_window
  clearance := (refinedChoices_window_fields S).clearance
  kappa := (refinedChoices_window_fields S).kappa
  reference := (refinedChoices_window_fields S).reference
  event_version := fun _ => Eventually.of_forall fun _ => rfl
  physical_stop := refinedFamily_physical_stop S
  geometric := fun i => by
    filter_upwards [refinedFamily_geometric S i] with p hp he
    obtain ⟨hm, hl, hin, hland, hh⟩ := hp he
    exact ⟨canonicalFamily_chart_conformal (refinedChoices S) i _, hm, hl, hin, hland,
      (recordChart_spec S i.1.1).continuous_lift _, hh⟩

/-- The global regularity cut loses no actual samples. This is proved
before comparisons or any completed-capture argument is supplied. -/
theorem refinedFamily_ae_good (S : SourceSetting.{u}) :
    ∀ᵐ p ∂S.μ, p ∈ Aux61Asm2.goodSet S (withRecordPath S (refinedFamily S)) :=
  ae_mem_goodSet S (withRecordPath S (refinedFamily S))
    (ae_goodPt S (withRecordPath S (refinedFamily S))
      (path_version_withRecordPath S (refinedFamily S))
      (canonicalFamily_ae_domain (refinedChoices S)) (refinedFamily_record_restart S).raw.regular)

/-- The exact source restart interface on the full-measure regular cut.
No normalization, seed-window, finite-buffer or geometric premise remains. -/
theorem refinedFamily_cut_restart (S : SourceSetting.{u}) :
    SourceRestartFacts (cutSource S (withRecordPath S (refinedFamily S))) (rationalTime S.s)
      S.own.W S.own.VL S.own.VR S.life (μ := S.μ) S.κ :=
  restart_cut_of (refinedFamily_record_restart S).raw
    (path_version_withRecordPath S (refinedFamily S))
    (canonicalFamily_ae_domain (refinedChoices S))

end InteractingSLE.Sec5.Aux61GWindow17
