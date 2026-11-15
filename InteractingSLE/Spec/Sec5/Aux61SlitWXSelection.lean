/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWXRead

/-!
# A concrete measurable choice of selected initial records

The selected set is the complete R1 configuration event, rather than an
arbitrary subset of a measurable record event. Its measurability follows
from the landed R1 constructor. Model/record agreement is stated separately.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal

namespace InteractingSLE.Sec5.Aux61SlitWX
open Aux61SlitW Aux61Asm2 Aux61Restart Aux61Marks Aux61ULoc LawUnique Restart.FlowStopIdentG
universe u
variable {S : SourceSetting.{u}} (D : R1Restart S)

/-- Select the complete R1 configuration, read solely from the initial record. -/
def configurationRestart : R1Restart S :=
  { D with selected := fun i =>
    restartConfigurationEvent (rationalTime S.s) (D.r i) (D.q i) (D.Y i) (D.η i) (D.U i) }

/-- The measurable continuous model inputs of the existing R1 constructor. -/
structure ModelFacts : Prop where
  q_pos : ∀ i, 0 < (D.q i : ℝ)
  time : ∀ i, (D.r i : ℝ) = (D.q i : ℝ)
  counterflow_measurable : ∀ i, Measurable fun y => GlueCond.cfStop (rationalTime S.s) (D.Y i y)
  driver_continuous : ∀ i y, Continuous fun t => D.U i t y
  driver_zero : ∀ i y, D.U i 0 y = 0
  driver_measurable : ∀ i t, t ≤ D.r i → Measurable (D.U i t)
  loewner : ∀ i y, IsLoewnerTrace (Ito.rpath fun t => D.U i t y) (D.η i y)
  path_measurable : ∀ i t, t ∈ Icc (0 : ℝ) (D.q i) → Measurable fun y => D.η i y t
  dense : DenseRange D.e

/-- Exact agreement of the continuous model with the original retained
records on the constructed configuration event. Producing this model is
the remaining record-instantiation input; it contains no future decision. -/
structure ModelRecordReadings : Prop where
  counterflow : ∀ i, ∀ y ∈ (configurationRestart D).selected i, D.Y i y = y.1
  path : ∀ i, ∀ y ∈ (configurationRestart D).selected i,
    EqOn (D.η i y) (fun t : ℝ => histTrace 0 y.2 t.toNNReal) (Icc (0 : ℝ) (D.q i))
  driver : ∀ i, ∀ y ∈ (configurationRestart D).selected i, ∀ t ≤ D.r i,
    D.U i t y = (histState y.2 t).1

variable {D} (M : ModelFacts D)
include M

/-- Measurability is proved for the actual selected set of this constructor. -/
theorem ModelFacts.selected_measurable (i : D.ι) :
    MeasurableSet ((configurationRestart D).selected i) :=
  (has_original_target_restart_chart_on_configuration (M.time i) (M.q_pos i)
    (M.counterflow_measurable i) (M.driver_continuous i) (M.driver_zero i)
    (M.driver_measurable i) (M.loewner i) (M.path_measurable i) M.dense).1

/-- The constructed selection supplies the previous reader interface,
including its measurability and exact configuration membership. -/
theorem ModelFacts.readers (A : ModelRecordReadings D) : ReaderFacts (configurationRestart D) where
  selected_measurable := M.selected_measurable
  q_pos := M.q_pos
  time_eq := fun i => NNReal.coe_injective (by
    change (D.r i : ℝ) = (rationalTime (D.q i) : ℝ)
    exact (M.time i).trans (Real.coe_toNNReal _ (M.q_pos i).le).symm)
  counterflow := A.counterflow
  path := A.path
  driver_continuous := fun i y _ => M.driver_continuous i y
  driver := A.driver
  configuration := fun _ => Subset.rfl

end InteractingSLE.Sec5.Aux61SlitWX
