/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWXAssembly

/-! # Normalized R1 restart facts before any comparison or capture input

The full chart certificate and the selected record readers give the basic
restart geometry. The supplied seed window and physical exit give the
remaining landing and stopping clauses. Neither initial comparisons nor
history/future capture is needed to construct the cut source restart.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GCaptureNext
open Aux61SlitW Aux61Asm2 Aux61SlitWX Aux61FibData Aux61Marks Aux61ULoc LawUnique
open Restart.FlowStopIdentG
universe u
variable {S : SourceSetting.{u}} (D : R1Restart S) (h : D.HasChart) (R : ReaderFacts D)
include R

/-- All restart facts of the actual normalized record source, independent
of comparisons and capture. Every geometric field is constructed. -/
theorem normalized_recordRestartFacts (hTip : OwnTipForwardLimit S)
    (V : WindowData D h) (hExit : PhysicalExit D h) :
    RecordRestartFacts S (source D h) where
  selected_measurable := R.selected_measurable
  chart_measurable := fun i => (chart_spec D h i).measurable
  event_measurable := (eventFacts_of_eq_preimage S (source D h)
    R.selected_measurable fun _ => rfl).1
  contact_measurable := D.measurable_contact
  open_window := V.open_window
  zero_window := V.zero_window
  clearance := V.clearance
  kappa := V.kappa
  reference := V.reference
  event_version := (eventFacts_of_eq_preimage S (source D h)
    R.selected_measurable fun _ => rfl).2
  physical_stop := fun i => by
    filter_upwards [hExit i, r1_contact_fields_of_tipOff D h R.tipOff i] with p hx ht he
    exact ⟨he, (ht he).2.1, hx he⟩
  geometric := fun i => by
    filter_upwards [R.ae_restartPoint h hTip i, R.ae_geometry h i,
      R.ae_landing h hTip V.buffer V.gap V.bounded V.window_subset V.seed i]
      with p hB hg hl he
    exact ⟨(hB he).conformal, (hB he).start_mem, (hB he).start_lim,
      (hB he).inside, fun _ => hl he, (chart_spec D h i).continuous_lift _,
      (hg he).harmonic_lift⟩

/-- The actual normalized cut family has all pointwise restart facts,
with no history-cover or future-completion hypothesis. -/
theorem normalized_cut_restart (hTip : OwnTipForwardLimit S)
    (V : WindowData D h) (hExit : PhysicalExit D h) :
    SourceRestartFacts (cutSource S (source D h)) (rationalTime S.s)
      S.own.W S.own.VL S.own.VR S.life (μ := S.μ) S.κ := by
  have hR := normalized_recordRestartFacts D h R hTip V hExit
  exact restart_cut_of hR.raw (path_version_withRecordPath S (source D h))
    (dom_component_of_record S (source D h) (R.record_domain h) hR.event_version)

/-- The normalized chart choice leaves the actual contact rule unchanged.
The absolute contact identity comes from the selected past record alone. -/
theorem normalized_contact_rule : ∀ i, ∀ᵐ p ∂S.μ, p ∈ (source D h).event i →
    contactRule (retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR))
      (rationalTime (D.q i))
      (stopRec (rationalTime S.s) p.2,
        killedHistory S.own.W S.own.VL S.own.VR S.life p.1) =
      ((source D h).start i : ℝ≥0∞) + (source D h).contact i p :=
  contact_rule_of_hit S (source D h)
    (fun _ => retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR))
    (fun _ => isClosed_retObs _) (fun _ => retObs_nonempty _)
    (r1_contact_hit_of_tipOff D h R.tipOff)

end InteractingSLE.Sec5.Aux61GCaptureNext
