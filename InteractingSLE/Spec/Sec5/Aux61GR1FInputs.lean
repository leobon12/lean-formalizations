/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GR1FStop
import InteractingSLE.Spec.Sec5.Aux61GR1FWindows

/-! # Fill the assembler's exact R1RestartInputs structure

The window fields come from a proved construction, and physical_stop is
proved from the actual proper path and bounded physical inverse windows.
The remaining chart/comparison/capture inputs retain their exact landed
field types. In particular the full-ball comparison and all-selected
completed-window premises are explicit conditional inputs here.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open scoped NNReal ENNReal
namespace InteractingSLE.Sec5.Aux61GR1F
open Aux61Asm2 Aux61SlitW Aux61FibData Aux61Fib LawUnique GlueCond
open Aux61Marks Aux61ULoc Restart.FlowStopIdentG
universe u

/-- An adapter with the exact landed result type. No geometric,
comparison or future-capture field is silently inferred from a chart. -/
theorem r1RestartInputs_of_window_fields {S : SourceSetting.{u}}
    (D : R1Restart S) (h : D.HasChart) (w : WindowFields D)
    (selected_measurable : ∀ i, MeasurableSet (D.selected i))
    (record_Y : ∀ i, ∀ y ∈ D.selected i, D.Y i y = y.1)
    (record_η : ∀ i, ∀ y ∈ D.selected i, D.η i y = fun t : ℝ => histTrace 0 y.2 t.toNNReal)
    (q_nonneg : ∀ i, 0 ≤ D.q i)
    (start_off : ∀ i, ∀ᵐ p ∂S.μ, p ∈ D.event i →
    recordPath S (rationalTime (D.q i)) p 0 ∉ retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR)
      (sourceRecord (D.src h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p))
    (geometric : ∀ i, ∀ᵐ p ∂S.μ, p ∈ (D.src h).event i → RestartGeoRest S (withRecordPath S (D.src h)) i p)
    (chart_geometry : ∀ i, ∀ᵐ p ∂S.μ, p ∈ (D.src h).event i →
    SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
      (cfHullQ (rationalTime S.s) p.2) (rationalTime (D.q i))
      (sourceChart (D.src h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p))
    (comparisons : ∀ i, Nonempty (Aux61GAlign.ZeroComparisons (S.marksData (cutSource S (withRecordPath S (D.src h)))) i))
    (history_cover : ∀ᵐ p ∂S.μ, S.windowEvent p → ∃ i,
    sourceRecord (D.src h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈ D.selected i)
    (completed_window : ∀ i, ∀ᵐ p ∂S.μ,
    sourceRecord (D.src h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈ D.selected i →
    S.windowEvent p → (D.src h).contact i p < ⊤ ∧
    (∀ v : ℝ≥0, (v : ℝ≥0∞) < (D.src h).contact i p →
      inPath ((D.src h).event i) (sourceChart (D.src h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
        ((withRecordPath S (D.src h)).path i) ((D.src h).contact i) p v ∈ (D.data i).V) ∧
    ∃ y ∈ Ioo (D.left i) (D.right i),
      Tendsto (inPath ((D.src h).event i)
        (sourceChart (D.src h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
        ((withRecordPath S (D.src h)).path i) ((D.src h).contact i) p)
        (𝓝[<] ((D.src h).contact i p).toNNReal) (𝓝 (y : ℂ)))
    (hbounded : ∀ i, ∀ᵐ p ∂S.μ, p ∈ D.event i → Bornology.IsBounded
      ((sourceChart (D.src h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).2.1 ''
        ((D.data i).V ∩ H))) :
    R1RestartInputs D h where
  selected_measurable := selected_measurable
  record_Y := record_Y
  record_η := record_η
  q_nonneg := q_nonneg
  start_off := start_off
  open_window := w.open_window
  zero_window := w.zero_window
  clearance := w.clearance
  kappa := w.kappa
  reference := w.reference
  physical_stop := physical_stop_of_bounded_inverse D h start_off (fun i => by
    filter_upwards [geometric i] with p hp he
    exact (hp he).2.2.1) hbounded
  geometric := geometric
  chart_geometry := chart_geometry
  comparisons := comparisons
  history_cover := history_cover
  completed_window := completed_window

end InteractingSLE.Sec5.Aux61GR1F
