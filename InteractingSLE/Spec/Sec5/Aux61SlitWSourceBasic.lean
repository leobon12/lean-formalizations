/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWSource

/-! # Recording, geometry and nesting of the concrete source objects -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW
open Aux61Marks Aux61FibData Aux61GInst Aux61ChLoc Aux61ULoc LawUnique Aux61UnionK
universe u

variable {Ω : Type u} [MeasurableSpace Ω] {nL nR : ℕ}
  (F : SourceRestartData Ω nL nR) (s : ℝ≥0) (W : ℝ≥0 → Ω → ℝ)
  (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
  {μ : Measure (Ω × HistorySpace 0 0)}

/-- The physical hypotheses reserved for the restart/window/history worker.
Neither marked locality nor any comparison or Gaussian conclusion is a field. -/
structure SourceRestartFacts (κ : ℝ) : Prop where
  selected_measurable : ∀ i, MeasurableSet (F.selected i)
  chart_measurable : ∀ i, IsMeasChart (F.chart i)
  spec : ∀ i, IsRestartSpec (F.event i) (sourceChart F s W VL VR ζ i) (F.path i) (F.contact i)
  open_window : ∀ i, IsOpen (F.data i).V
  zero_window : ∀ i, (0 : ℂ) ∈ (F.data i).V
  landing : ∀ i, HasAccessLanding (F.event i) (sourceChart F s W VL VR ζ i)
    (F.path i) (F.contact i) (F.data i).V
  injective_path : ∀ i, ∀ x ∈ F.event i, InjOn (F.path i x) {v | (v : ℝ≥0∞) < F.contact i x}
  continuous_lift : ∀ i, ∀ x ∈ F.event i,
    ContinuousOn (sourceChart F s W VL VR ζ i x).2.2 (sourceChart F s W VL VR ζ i x).dom
  harmonic_lift : ∀ i, ∀ x ∈ F.event i,
    InnerProductSpace.HarmonicOnNhd (sourceChart F s W VL VR ζ i x).2.2
      (sourceChart F s W VL VR ζ i x).dom
  clearance : ∀ i, (F.data i).ℓ = clr (F.data i).V
  kappa : ∀ i, (F.data i).κ = κ
  reference : ∀ i, Aux61Cov.RefWin (F.data i).κ (F.data i).bR (F.data i).JR (Ioo (F.left i) (F.right i))
  event_version : ∀ i, F.event i =ᵐ[μ] sourceRecord F s W VL VR ζ i ⁻¹' F.selected i
  physical_stop : ∀ i, ∀ᵐ p ∂μ, sourceRecord F s W VL VR ζ i p ∈ F.selected i →
    p ∈ F.event i ∧ 0 < F.contact i p ∧ (F.contact i p < ⊤ ∨ ∃ v : ℝ≥0,
      (v : ℝ≥0∞) < F.contact i p ∧
      inPath (F.event i) (sourceChart F s W VL VR ζ i) (F.path i) (F.contact i) p v ∉ (F.data i).V)

/-- Initial histories are measurable on the actual coupling space. -/
theorem measurable_sourceRecord (hX : IsMeasurableKilledDriving W VL VR ζ) (i : F.ι) :
    Measurable (sourceRecord F s W VL VR ζ i) := by
  exact (isRecordStop_stopRec.measurable.comp (measurable_const.prodMk measurable_snd)).prodMk
    (isRecordStop_stopRec.measurable.comp
      (measurable_const.prodMk ((measurable_killedHistory hX).comp measurable_fst)))

omit [MeasurableSpace Ω] in
/-- The initial history is recorded by the raw marks at every capacity stop. -/
theorem sourceRecord_ruleMarks (i : F.ι) (q : ℝ≥0) :
    Measurable[ruleMarks stopRec (capacityRule (F.chart i) (F.start i) q)
      (fun p : Ω × HistorySpace 0 0 => stopRec s p.2) (fun p => killedHistory W VL VR ζ p.1)]
      (sourceRecord F s W VL VR ζ i) :=
  measurable_ruleMarks_of_time0 measurable_id isRecordStop_stopRec
    (start_le_capacityRule (F.chart i) (F.start i) q)

/-- The initial history algebra lies in the completed physical marks. -/
theorem sourceHistory_marks {κ : ℝ} (hF : SourceRestartFacts F s W VL VR ζ (μ := μ) κ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (i : F.ι) (q : ℝ≥0) :
    Measurable[nullMarks (ruleMarks stopRec (capacityRule (F.chart i) (F.start i) q)
      (fun p => stopRec s p.2) (fun p => killedHistory W VL VR ζ p.1)) μ]
      (sourceHistory F s W VL VR ζ i) := by
  exact ((measurable_up.comp (sourceRecord_ruleMarks F s W VL VR ζ i q))).mono
    (le_nullMarks (ruleMarks_le isRecordStop_stopRec
      (measurable_capacityRule (hF.chart_measurable i) (F.start i) q)
      (isRecordStop_stopRec.measurable.comp (measurable_const.prodMk measurable_snd))
      ((measurable_killedHistory hX).comp measurable_fst))) le_rfl

/-- The selected restart event is recorded up to null sets, as required for
the regular physical restart versions. -/
theorem sourceEvent_marks {κ : ℝ} (hF : SourceRestartFacts F s W VL VR ζ (μ := μ) κ)
    (i : F.ι) (q : ℝ≥0) :
    MeasurableSet[nullMarks (ruleMarks stopRec (capacityRule (F.chart i) (F.start i) q)
      (fun p => stopRec s p.2) (fun p => killedHistory W VL VR ζ p.1)) μ] (F.event i) :=
  measurableSet_nullMarks_of_ae_eq (hF.spec i).measurableSet
    ((sourceRecord_ruleMarks F s W VL VR ζ i q) (hF.selected_measurable i)) (hF.event_version i)

/-- The initially selected chart is recorded by the completed marks. -/
theorem sourceChart_marks {κ : ℝ} (hF : SourceRestartFacts F s W VL VR ζ (μ := μ) κ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (i : F.ι) (q : ℝ≥0) :
    @IsMeasChart (Ω × HistorySpace 0 0)
      (nullMarks (ruleMarks stopRec (capacityRule (F.chart i) (F.start i) q)
        (fun p => stopRec s p.2) (fun p => killedHistory W VL VR ζ p.1)) μ)
      (sourceChart F s W VL VR ζ i) := by
  have hrec := sourceHistory_marks F s W VL VR ζ hF hX i q
  have hm := measurable_down.comp hrec
  exact @IsMeasChart.mk (Ω × HistorySpace 0 0)
    (nullMarks (ruleMarks stopRec (capacityRule (F.chart i) (F.start i) q)
      (fun p => stopRec s p.2) (fun p => killedHistory W VL VR ζ p.1)) μ)
    (sourceChart F s W VL VR ζ i)
    (fun z => hm ((hF.chart_measurable i).dom z))
    (fun z => ((hF.chart_measurable i).fwd z).comp hm)
    (fun z => ((hF.chart_measurable i).lift z).comp hm)

variable (κ : ℝ) (h : Ω → DistOn upperHalfPlaneOpens)

/-- The constructed set is relatively closed at every sample, including
samples with a dead code. -/
theorem sourceSets_closed (hs : ∀ i,
    IsRestartSpec (F.event i) (sourceChart F s W VL VR ζ i) (F.path i) (F.contact i))
    (i : F.ι) (q : ℝ≥0) (p : Ω × HistorySpace 0 0) :
    sourceSets F s W VL VR ζ κ h i q p ⊆ H ∧ IsOpen (H \ sourceSets F s W VL VR ζ κ h i q p) := by
  by_cases hp : p ∈ liveEv (sourceHistory F s W VL VR ζ i) (sourceHistoryEvent F i)
      (sourceCode F s W VL VR ζ κ h i) q
  · rw [sourceSets, liveSet_of_mem hp]
    exact ⟨chartSet_subset_H _ _, isOpen_H_diff_chartSet
      ((hs i).conf p (mem_exitEv_of_lt_accessLife hp.2).1.1) (isOpen_H_diff_chartHull _ hp.2)⟩
  · rw [sourceSets, liveSet_of_notMem hp, sdiff_self]
    exact ⟨subset_rfl, isOpen_empty⟩

omit [MeasurableSpace Ω] in
/-- The current live sets contain the initial live set at every sample. -/
theorem sourceSets_mono (i : F.ι) (q : ℝ≥0) (p : Ω × HistorySpace 0 0) :
    sourceSets F s W VL VR ζ κ h i 0 p ⊆ sourceSets F s W VL VR ζ κ h i q p := by
  apply Aux61Nest.liveSet_subset Aux61OldB.liveEv_subset_zero (fun _ => chartSet_subset_H _ _)
  intro x
  exact chartSet_mono _ (QuantumZipper.fwdHull_mono.1 (NNReal.coe_nonneg q))

/-- The complement of the concrete live set is the chart pullback on the
live event; this is exactly MARKS' geometry field. -/
theorem sourceSets_geometry (hs : ∀ i,
    IsRestartSpec (F.event i) (sourceChart F s W VL VR ζ i) (F.path i) (F.contact i))
    (i : F.ι) (q : ℝ≥0) (p : Ω × HistorySpace 0 0)
    (hp : p ∈ liveEv (sourceHistory F s W VL VR ζ i) (sourceHistoryEvent F i)
      (sourceCode F s W VL VR ζ κ h i) q) :
    H \ sourceSets F s W VL VR ζ κ h i q p =
      (sourceChart F s W VL VR ζ i p).2.1 ''
        (H \ chartHull (sourceCode F s W VL VR ζ κ h i) q p) := by
  rw [sourceSets, liveSet_of_mem hp]
  exact H_diff_chartSet ((hs i).conf p (mem_exitEv_of_lt_accessLife hp.2).1.1) _

end InteractingSLE.Sec5.Aux61SlitW
