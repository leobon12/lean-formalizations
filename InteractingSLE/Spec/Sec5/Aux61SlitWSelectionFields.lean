/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61Asm2R1
import InteractingSLE.Spec.Sec5.Aux61RestartPrepCover

/-!
# Selection of a restart tip off the recorded obstacle

The initial record alone decides whether the restart tip is outside R1's
contact obstacle. R1's separated interior prefix event implies this test.
For the source record the test is exactly the canonical restart's initial
point being off that obstacle, with no exceptional set needed.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW
open Aux61Marks Aux61FibData Aux61Restart Aux61ULoc LawUnique Restart.FlowStopIdentG
open Aux61Asm2 (recordPath)

/-- The retained record's restart tip is off the contact obstacle. -/
def tipOffRecords {nL nR : ℕ} (s r : ℝ≥0) : Set (SourceRecord nL nR) :=
  {y | histTrace 0 y.2 r ∉ retObs s y}

/-- Clearance of the recorded tip from the full contact obstacle is measurable. -/
theorem measurable_tipObstacleDistance {nL nR : ℕ} (s r : ℝ≥0) :
    Measurable fun y : SourceRecord nL nR => infDist (histTrace 0 y.2 r) (retObs s y) := by
  have hm : ∀ z : ℂ, Measurable fun y : SourceRecord nL nR => infDist z (retObs s y) :=
    fun z => measurable_infDist_retObs (β := HistorySpace nL nR) s z
  have hd : Measurable fun p : ℂ × SourceRecord nL nR => infDist p.1 (retObs s p.2) :=
    measurable_uncurry_of_continuous_of_measurable
      (u := fun (z : ℂ) (y : SourceRecord nL nR) => infDist z (retObs s y))
      (fun _ => continuous_infDist_pt _) hm
  have hz : Measurable fun y : SourceRecord nL nR => histTrace 0 y.2 r :=
    (measurable_histTrace (nL := nL) (nR := nR) 0 r).comp
      (measurable_snd : Measurable (Prod.snd : SourceRecord nL nR → HistorySpace nL nR))
  have hpair : Measurable fun y : SourceRecord nL nR => (histTrace 0 y.2 r, y) :=
    hz.prodMk (measurable_id : Measurable (id : SourceRecord nL nR → SourceRecord nL nR))
  exact Measurable.comp
    (g := fun p : ℂ × SourceRecord nL nR => infDist p.1 (retObs s p.2))
    (f := fun y : SourceRecord nL nR => (histTrace 0 y.2 r, y)) hd hpair

/-- Selection by a tip outside the obstacle is measurable on the initial records. -/
theorem measurableSet_tipOffRecords {nL nR : ℕ} (s r : ℝ≥0) :
    MeasurableSet (tipOffRecords (nL := nL) (nR := nR) s r) := by
  have he : tipOffRecords (nL := nL) (nR := nR) s r =
      {y | 0 < infDist (histTrace 0 y.2 r) (retObs s y)} := by
    ext y
    exact (isClosed_retObs s y).notMem_iff_infDist_pos (retObs_nonempty s y)
  rw [he]
  exact measurableSet_lt measurable_const (measurable_tipObstacleDistance s r)

/-- R1's separated interior prefix already puts the recorded tip off the obstacle. -/
theorem mem_tipOffRecords_of_restartPrefixEvent {nL nR : ℕ} {s : ℝ≥0} {q : ℚ}
    (hq : 0 < (q : ℝ)) {y : SourceRecord nL nR}
    (hy : y ∈ restartPrefixEvent s q Prod.fst
      (fun y : SourceRecord nL nR => fun t : ℝ => histTrace 0 y.2 t.toNNReal)) :
    y ∈ tipOffRecords s (rationalTime q) := by
  change ¬ ¬ (histTrace 0 y.2 (rationalTime q) ∈ H ∧
    histTrace 0 y.2 (rationalTime q) ∉ historyHull s Prod.fst y)
  refine not_not.2 ⟨hy.2.1 ⟨hq, le_rfl⟩, ?_⟩
  intro hmem
  have hzero := infDist_zero_of_mem hmem
  exact (ne_of_gt hy.2.2) hzero

namespace SourceSetting
universe u
variable (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR)

/-- The canonical restart's initial point is read exactly from the stopped
own record, including for records outside the physical full-measure set. -/
theorem recordPath_zero_eq_sourceRecord_tip (i : F.ι) (p : S.Ω × HistorySpace 0 0) :
    recordPath S (F.start i) p 0 = histTrace 0
      (sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).2 (F.start i) := by
  simp only [recordPath, sourceRecord, add_zero, histTrace_stopRec_of_le le_rfl]

/-- An initial selection contained in R1's off-obstacle test supplies the
pointwise start-off clause; neither a restart specification nor a contact
rule identity is assumed. -/
theorem start_off_of_selected_tipOff
    (hsel : ∀ i, F.selected i ⊆ tipOffRecords (rationalTime S.s) (F.start i))
    (i : F.ι) (p : S.Ω × HistorySpace 0 0)
    (hp : sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈ F.selected i) :
    recordPath S (F.start i) p 0 ∉
      retObs (rationalTime S.s) (sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p) := by
  rw [S.recordPath_zero_eq_sourceRecord_tip F i p]
  exact hsel i hp

end SourceSetting
end InteractingSLE.Sec5.Aux61SlitW
