/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GR1FInputs
import InteractingSLE.Spec.Sec5.Aux61GPrimeCutoffs

/-! # R1's record interface using the marked component comparison

The landed R1RestartInputs comparison field still asks for full-ball
separation. This fresh adapter instead fills its downstream RecordInputs
with the proved component comparison theorem. The old structure is left
unchanged, and every remaining geometric and capture input is explicit.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open scoped NNReal ENNReal
namespace InteractingSLE.Sec5.Aux61GR1F
open Aux61Asm2 Aux61SlitW Aux61FibData Aux61Fib Aux61Marks Aux61ULoc
open LawUnique GlueCond Restart.FlowStopIdentG
universe u

/-- The record-domain component follows from the recorded chart readers,
without any comparison mean or future-capture premise. -/
theorem recordDomainComponent_of_prefix_readers {S : SourceSetting.{u}}
    (D : R1Restart S) (h : D.HasChart)
    (record_Y : ∀ i, ∀ y ∈ D.selected i, D.Y i y = y.1)
    (record_η : ∀ i, ∀ y ∈ D.selected i,
      EqOn (D.η i y) (fun t : ℝ => histTrace 0 y.2 t.toNNReal) (Icc 0 (D.q i : ℝ)))
    (q_nonneg : ∀ i, 0 ≤ D.q i) : RecordDomainComponent S (D.src h) := by
  intro i

  obtain ⟨b, hb⟩ := (D.chart_spec h i).2.2.1
  refine ⟨b, fun y hy => ?_⟩
  have hq : ((rationalTime (D.q i) : ℝ≥0) : ℝ) = (D.q i : ℝ) :=
    Real.coe_toNNReal _ (by exact_mod_cast q_nonneg i)
  have hK : Aux61Restart.historyHull (rationalTime S.s) (D.Y i) y =
    Aux61Restart.historyHull (rationalTime S.s) (fun p : HistorySpace 0 0 × HistorySpace S.nL S.nR => p.1) y := by
    simp only [Aux61Restart.historyHull, record_Y i y hy]
  change ((D.chart h i y).dom : Set ℂ) = connectedComponentIn (Aux61Restart.retainedDomain
    (Aux61Restart.historyHull (rationalTime S.s) (fun p : HistorySpace 0 0 × HistorySpace S.nL S.nR => p.1) y)
    (fun t : ℝ => histTrace 0 y.2 t.toNNReal) ((rationalTime (D.q i) : ℝ≥0) : ℝ)) (b y)
  rw [hb y, hK, hq, Aux61Restart.retainedDomain, Aux61Restart.retainedDomain,
    (record_η i y hy).image_eq]

/-- Compatibility with the older exact global-reader premise. The
component domain itself only needs the prefix identity above. -/
theorem recordDomainComponent_of_readers {S : SourceSetting.{u}}
    (D : R1Restart S) (h : D.HasChart)
    (record_Y : ∀ i, ∀ y ∈ D.selected i, D.Y i y = y.1)
    (record_η : ∀ i, ∀ y ∈ D.selected i, D.η i y = fun t : ℝ => histTrace 0 y.2 t.toNNReal)
    (q_nonneg : ∀ i, 0 ≤ D.q i) : RecordDomainComponent S (D.src h) :=
  recordDomainComponent_of_prefix_readers D h record_Y
    (fun i y hy t _ => congrFun (record_η i y hy) t) q_nonneg

/-- The canonical record restart facts, including a proved physical_stop,
are independent of comparison and completed-window hypotheses. -/
theorem recordRestartFacts_of_window_fields {S : SourceSetting.{u}}
    (D : R1Restart S) (h : D.HasChart) (w : WindowFields D)
    (selected_measurable : ∀ i, MeasurableSet (D.selected i))
    (start_off : ∀ i, ∀ᵐ p ∂S.μ, p ∈ D.event i →
    recordPath S (rationalTime (D.q i)) p 0 ∉ retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR)
      (sourceRecord (D.src h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p))
    (geometric : ∀ i, ∀ᵐ p ∂S.μ, p ∈ (D.src h).event i → RestartGeoRest S (withRecordPath S (D.src h)) i p)
    (hbounded : ∀ i, ∀ᵐ p ∂S.μ, p ∈ D.event i → Bornology.IsBounded
      ((sourceChart (D.src h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).2.1 ''
        ((D.data i).V ∩ H))) :
    RecordRestartFacts S (D.src h) where
  selected_measurable := selected_measurable
  chart_measurable := fun i => (D.chart_spec h i).1
  event_measurable := (eventFacts_of_eq_preimage S (D.src h) selected_measurable fun _ => rfl).1
  contact_measurable := D.measurable_contact
  open_window := w.open_window
  zero_window := w.zero_window
  clearance := w.clearance
  kappa := w.kappa
  reference := w.reference
  event_version := (eventFacts_of_eq_preimage S (D.src h) selected_measurable fun _ => rfl).2
  physical_stop := physical_stop_of_bounded_inverse D h start_off (fun i => by
    filter_upwards [geometric i] with p hp he
    exact (hp he).2.2.1) hbounded
  geometric := fun i => by
    filter_upwards [geometric i] with p hp he
    obtain ⟨hm, hlim, hin, hland, hh⟩ := hp he
    exact ⟨(D.chart_spec h i).2.1 _, hm, hlim, hin, hland, (D.chart_spec h i).2.2.2 _, hh⟩

/-- The exact downstream record interface, with the stronger full-ball
comparison replaced by the proved marked component comparison. This is
a distinct theorem and does not alter R1RestartInputs. -/
theorem recordInputs_of_component_comparisons {S : SourceSetting.{u}}
    (D : R1Restart S) (h : D.HasChart) (w : WindowFields D)
    (selected_measurable : ∀ i, MeasurableSet (D.selected i))
    (record_Y : ∀ i, ∀ y ∈ D.selected i, D.Y i y = y.1)
    (record_η : ∀ i, ∀ y ∈ D.selected i,
      EqOn (D.η i y) (fun t : ℝ => histTrace 0 y.2 t.toNNReal) (Icc 0 (D.q i : ℝ)))
    (q_nonneg : ∀ i, 0 ≤ D.q i)
    (start_off : ∀ i, ∀ᵐ p ∂S.μ, p ∈ D.event i →
    recordPath S (rationalTime (D.q i)) p 0 ∉ retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR)
      (sourceRecord (D.src h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p))
    (geometric : ∀ i, ∀ᵐ p ∂S.μ, p ∈ (D.src h).event i → RestartGeoRest S (withRecordPath S (D.src h)) i p)
    (chart_geometry : ∀ i, ∀ᵐ p ∂S.μ, p ∈ (D.src h).event i →
    SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
      (cfHullQ (rationalTime S.s) p.2) (rationalTime (D.q i))
      (sourceChart (D.src h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p))
    (comparisons : ∀ i, Nonempty (Aux61GPrime.ZeroComparisons (S.marksData (cutSource S (withRecordPath S (D.src h)))) i))
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
    RecordInputs S (D.src h) (fun i => contactRule
      (retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR)) (rationalTime (D.q i))) := by
  have hR := recordRestartFacts_of_window_fields D h w selected_measurable start_off geometric hbounded
  have hD := recordDomainComponent_of_prefix_readers D h record_Y record_η q_nonneg
  have hcontact := ae_contact_eq_hitTime D h start_off
  have hhit : ∀ i, ∀ᵐ p ∂S.μ, p ∈ (D.src h).event i →
      (D.src h).contact i p = hitTime (recordPath S ((D.src h).start i))
        (fun p => retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR)
          (sourceRecord (D.src h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)) p ∧
      recordPath S ((D.src h).start i) p 0 ∉
        retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR)
          (sourceRecord (D.src h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p) := fun i => by
    filter_upwards [hcontact i, start_off i] with p hc hs he
    exact ⟨hc he, hs he⟩
  refine {
    restart := hR
    contact_measurable := fun i => measurable_contactRule
      (measurable_infDist_retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR)) (rationalTime (D.q i))
    contact_galmarino := fun i => isGalmarinoRule_contactRule _ _
    contact_rule := contact_rule_of_hit S (D.src h)
      (fun _ => retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR))
      (fun _ => isClosed_retObs _) (fun _ => retObs_nonempty _) hhit
    dom_component := dom_component_of_record S (D.src h) hD hR.event_version
    chart_geometry := chart_geometry
    initial_data := fun i => ?_
    history_cover := history_cover
    completed_window := completed_window }
  have hR' := restart_cut_of hR.raw (path_version_withRecordPath S (D.src h))
    (dom_component_of_record S (D.src h) hD hR.event_version)
  have hsets := sets_marks_cut_of hR'
    (fun i => measurable_contactRule
      (measurable_infDist_retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR)) (rationalTime (D.q i)))
    (fun i => isGalmarinoRule_contactRule _ _)
    (contact_rule_of_hit S (D.src h)
      (fun _ => retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR))
      (fun _ => isClosed_retObs _) (fun _ => retObs_nonempty _) hhit) i 0
  have hret : ∀ᵐ p ∂S.μ, p ∈ (cutSource S (withRecordPath S (D.src h))).event i →
      (((S.marksData (cutSource S (withRecordPath S (D.src h)))).chart i p).dom : Set ℂ) ⊆
        H \ (cfHullQ (rationalTime S.s) p.2 ∪
          (fun t : ℝ => S.path p.1 t.toNNReal) '' Icc 0 (rationalTime (D.q i) : ℝ)) := by
    filter_upwards [chart_geometry i] with p hp he
    exact (hp he.1).retained
  obtain ⟨C⟩ := comparisons i
  obtain ⟨g, hg, -, hinit⟩ := Aux61GPrime.exists_source_initial_data_comp S
    (cutSource S (withRecordPath S (D.src h))) hR' i hsets hret C
  exact ⟨g, hg, hinit⟩

end InteractingSLE.Sec5.Aux61GR1F
