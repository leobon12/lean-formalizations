/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWABPieces
import InteractingSLE.Spec.Sec5.Aux61SlitWAASeed

/-! # The compact old boundary read from the retained counterflow record -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitWAB
open Aux61R1C Aux61SlitW Aux61GInst Aux61ULoc LawUnique Restart.FlowStopIdentG CfRegQ

/-- The finite counterflow trace read solely from its retained record. -/
def recordBoundary (s : ℝ≥0) (y : HistorySpace 0 0) : Set ℂ :=
  oldModelBoundary (counterflowRecord (recTrace y) s)

/-- The recorded compact trace is continuous on its retained interval. -/
theorem continuousOn_recordTrace {s : ℝ≥0} (hs : 0 < s) {y : HistorySpace 0 0}
    (hy : y ∈ counterflowCertified s) : ContinuousOn (recTrace y) (Icc 0 (s : ℝ)) :=
  (hy.1.isLoewnerTraceLT_recTrace hy.2 hs).2

theorem isCompact_recordBoundary {s : ℝ≥0} (hs : 0 < s) {y : HistorySpace 0 0}
    (hy : y ∈ counterflowCertified s) : IsCompact (recordBoundary s y) :=
  isCompact_oldModelBoundary (isCompact_Icc.image_of_continuousOn
    (continuous_clipH.comp_continuousOn (continuousOn_recordTrace hs hy)))
    (by rintro _ ⟨t, -, rfl⟩; exact clipH_mem_Hbar _)

theorem recordBoundary_nonempty (s : ℝ≥0) (y : HistorySpace 0 0) : (recordBoundary s y).Nonempty :=
  ⟨1, Or.inl (by simp)⟩

/-- Up to the retained time, the trace read from the stopped record
equals the physical counterflow trace read from the original history. -/
theorem recTrace_stopRec_eq_histLine {y : HistorySpace 0 0} (hy : DyCert y)
    {s : ℝ≥0} {t : ℝ} (ht : t ≤ s) : recTrace (stopRec s y) t = WangWu.histLine y t := by
  rw [recTrace_eq_traceAt ht]
  apply LP.traceAt_congr
  intro r hr
  rw [frozenDrv_stopRec_of_dyCert hy, min_eq_left (hr.trans (Real.toNNReal_le_iff_le_coe.2 ht))]
  rfl

/-- The recorded old boundary is exactly the physical old boundary.
Only the original counterflow's dyadic certificate is required. -/
theorem recordBoundary_stopRec_eq {y : HistorySpace 0 0} (hy : DyCert y) (s : ℝ≥0) :
    recordBoundary s (stopRec s y) =
      oldModelBoundary (counterflowRecord (WangWu.histLine y) s) := by
  unfold recordBoundary counterflowRecord
  congr 1
  apply image_congr
  intro t ht
  rw [recTrace_stopRec_eq_histLine hy ht.2]

end InteractingSLE.Sec5.Aux61SlitWAB
