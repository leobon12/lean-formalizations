/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWXChart
import InteractingSLE.Spec.Sec5.Aux61SlitWR1Contact
import InteractingSLE.Spec.Sec5.Aux61SlitWSettingFields
import QuantumZipper.Proofs.Zipper.RegContRandom

/-! # Selected-record readers for the fully normalized R1 chart -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H fwdMapInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitWX
open Aux61SlitW Aux61Asm2 Aux61Restart Aux61FibData Aux61Marks Aux61ULoc LawUnique
open Restart.FlowStopIdentG
universe u
variable {S : SourceSetting.{u}} (D : R1Restart S)

/-- The R1 model reads the selected retained records. These are identities
and configuration membership of the model, not future-contact assumptions. -/
structure ReaderFacts : Prop where
  selected_measurable : ∀ i, MeasurableSet (D.selected i)
  q_pos : ∀ i, 0 < (D.q i : ℝ)
  time_eq : ∀ i, D.r i = rationalTime (D.q i)
  counterflow : ∀ i, ∀ y ∈ D.selected i, D.Y i y = y.1
  path : ∀ i, ∀ y ∈ D.selected i,
    EqOn (D.η i y) (fun t : ℝ => histTrace 0 y.2 t.toNNReal) (Icc (0 : ℝ) (D.q i))
  driver_continuous : ∀ i, ∀ y ∈ D.selected i, Continuous fun t => D.U i t y
  driver : ∀ i, ∀ y ∈ D.selected i, ∀ t ≤ D.r i, D.U i t y = (histState y.2 t).1
  configuration : ∀ i, D.selected i ⊆
    restartConfigurationEvent (rationalTime S.s) (D.r i) (D.q i) (D.Y i) (D.η i) (D.U i)

variable {D} (R : ReaderFacts D) (h : D.HasChart)
include R

theorem ReaderFacts.tipOff : ∀ i, D.selected i ⊆
    tipOffRecords (rationalTime S.s) (rationalTime (D.q i)) := by
  intro i y hy
  have hp := (R.configuration i hy).1
  have ht := R.path i y hy ⟨(R.q_pos i).le, le_rfl⟩
  have hK : historyHull (rationalTime S.s) (D.Y i) y =
      historyHull (rationalTime S.s) Prod.fst y := by
    simp only [historyHull, R.counterflow i y hy]
  have hclear := hp.2.2
  rw [ht, hK] at hclear
  have hheight := hp.2.1 ⟨R.q_pos i, le_rfl⟩
  rw [ht] at hheight
  change ¬ ¬ (histTrace 0 y.2 (rationalTime (D.q i)) ∈ H ∧
    histTrace 0 y.2 (rationalTime (D.q i)) ∉ historyHull (rationalTime S.s) Prod.fst y)
  refine not_not.2 ⟨hheight, ?_⟩
  intro hmem
  exact (ne_of_gt hclear) (infDist_zero_of_mem hmem)

/-- The exact selected-record component identity for the new source. -/
theorem ReaderFacts.record_domain : RecordDomainComponent S (source D h) := by
  intro i
  refine ⟨base D h i, fun y hy => ?_⟩
  have hq : (rationalTime (D.q i) : ℝ) = (D.q i : ℝ) := Real.coe_toNNReal _ (R.q_pos i).le
  change ((chart D h i y).dom : Set ℂ) = connectedComponentIn
    (retainedDomain (historyHull (rationalTime S.s) Prod.fst y)
      (fun t : ℝ => histTrace 0 y.2 t.toNNReal) (rationalTime (D.q i))) (base D h i y)
  rw [(chart_spec D h i).domain y]
  have hK : historyHull (rationalTime S.s) (D.Y i) y =
      historyHull (rationalTime S.s) Prod.fst y := by
    simp only [historyHull, R.counterflow i y hy]
  rw [hK, restartComponent, retainedDomain, retainedDomain, (R.path i y hy).image_eq, hq]

/-- The R1 own inverse chart is the actual own inverse map. Only driver
values through the original restart time are read. -/
theorem ReaderFacts.ae_inverse_eq : ∀ᵐ p ∂S.μ, ∀ i, p ∈ D.event i →
    EqOn (ownHistoryChart (D.U i) (D.r i)
      (sourceRecord (source D h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)).2.1
      (fwdMapInv (fun t : ℝ => S.own.W t.toNNReal p.1) (rationalTime (D.q i))) H := by
  have hstate := ae_histState_killedHistory S.own.coupling.1
    (WangWu.glueMeasure_fst S.kernel S.measCounterField)
  filter_upwards [S.physical_path, hstate] with p hp hst i he
  let y := sourceRecord (source D h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p
  have hy : y ∈ D.selected i := he
  have hread : ∀ t : ℝ≥0, t ≤ D.r i → D.U i t y = S.own.W t p.1 := by
    intro t ht
    rw [R.driver i y hy t ht]
    change (histState (stopRec (rationalTime (D.q i))
      (killedHistory S.own.W S.own.VL S.own.VR S.life p.1)) t).1 = _
    rw [histState_stopRec_of_le (R.time_eq i ▸ ht),
      hst t (by rw [hp.1.1]; exact ENNReal.coe_lt_top)]
  have hU0 : D.U i 0 y = 0 := by
    rw [hread 0 (zero_le : (0 : ℝ≥0) ≤ D.r i)]
    exact hp.1.2.1
  have hEq : EqOn (Ito.rpath fun t => D.U i t y)
      (fun t : ℝ => S.own.W t.toNNReal p.1) (Icc (0 : ℝ) (rationalTime (D.q i))) := by
    intro t ht
    exact hread t.toNNReal (by rw [R.time_eq i]; exact Real.toNNReal_le_iff_le_coe.2 ht.2)
  change EqOn (fwdMapInv (Ito.rpath fun t => D.U i t y) (D.r i)) _ H
  rw [R.time_eq i]
  exact QuantumZipper.RegCont.fwdMapInv_congr
    (Chart.continuous_rpath_of_continuous (R.driver_continuous i y hy))
    (Chart.rpath_zero_of hU0) hp.1.continuous_rpath
    (by simpa only [Ito.rpath, Real.toNNReal_zero] using hp.1.2.1) hEq
    ⟨(rationalTime (D.q i)).coe_nonneg, le_rfl⟩

/-- The physical component identity follows from the selected record identity. -/
theorem ReaderFacts.ae_domain : ∀ i, ∀ᵐ p ∂S.μ, p ∈ D.event i → ∃ b : ℂ,
    ((sourceChart (source D h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom : Set ℂ) =
      restartComponent (GlueCond.cfHullQ (rationalTime S.s) p.2)
        (fun t : ℝ => S.path p.1 t.toNNReal) (rationalTime (D.q i)) b :=
  dom_component_of_record S (source D h) (R.record_domain h) fun _ => Filter.Eventually.of_forall fun _ => rfl

end InteractingSLE.Sec5.Aux61SlitWX
