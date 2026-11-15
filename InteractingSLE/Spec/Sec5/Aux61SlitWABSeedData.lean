/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWABSeed

/-! # The measurable continuous data for uniform seed localization -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (Hbar)

namespace InteractingSLE.Sec5.Aux61SlitWAB
open Aux61SlitW Aux61R1C Aux61Asm2 Aux61FibData Aux61GInst LawUnique
universe u
variable {S : SourceSetting.{u}} (C : RestartChoices S)

theorem measurable_seed_inverse (hsel : ∀ i, MeasurableSet (C.selected i)) (i : C.Idx) (a : ℝ) :
    Measurable ((seedRecords C i).indicator fun y =>
      boundedInverse (C.toR1Restart.chart C.hasChart i y) (a : ℂ)) :=
  measurable_boundedInverse_real (measurableSet_seedRecords C hsel i)
    (C.toR1Restart.chart_spec C.hasChart i).1
    (fun y _ => (C.toR1Restart.chart_spec C.hasChart i).2.1 y)
    (fun _ hy => record_extension C i hy.1.1 hy.1.2) a

theorem continuous_seed_inverse (i : C.Idx) {y : SourceRecord S.nL S.nR}
    (hy : y ∈ seedRecords C i) :
    Continuous (fun a : ℝ => boundedInverse (C.toR1Restart.chart C.hasChart i y) (a : ℂ)) :=
  (record_extension C i hy.1.1 hy.1.2).2.comp_continuous Complex.continuous_ofReal
    (fun a => by change 0 ≤ (a : ℂ).im; simp only [Complex.ofReal_im, le_refl])

theorem measurable_seed_boundary (hsel : ∀ i, MeasurableSet (C.selected i)) (i : C.Idx) (z : ℂ) :
    Measurable ((seedRecords C i).indicator fun y => infDist z (recordBoundary (rationalTime S.s) y.1)) := by
  classical
  have hd : Measurable (fun y : seedRecords C i =>
      infDist z (recordBoundary (rationalTime S.s) y.1.1)) :=
    measurable_infDist_oldModelBoundary
      (fun y => continuousOn_recordTrace (rationalTime_s_pos S) y.2.1.2)
      (fun t => (measurable_recTrace t).comp (measurable_fst.comp measurable_subtype_coe)) z
  apply measurable_of_restrict_of_restrict_compl (measurableSet_seedRecords C hsel i)
  · have heq : (seedRecords C i).domRestrict ((seedRecords C i).indicator
        fun y => infDist z (recordBoundary (rationalTime S.s) y.1)) =
        (fun y : seedRecords C i => infDist z (recordBoundary (rationalTime S.s) y.1.1)) :=
      funext fun y => indicator_of_mem y.2 _
    rw [heq]
    exact hd
  · have heq : (seedRecords C i)ᶜ.domRestrict ((seedRecords C i).indicator
        fun y => infDist z (recordBoundary (rationalTime S.s) y.1)) =
        (fun _ : ((seedRecords C i)ᶜ : Set (SourceRecord S.nL S.nR)) => (0 : ℝ)) :=
      funext fun y => indicator_of_notMem y.2 _
    rw [heq]
    exact measurable_const

end InteractingSLE.Sec5.Aux61SlitWAB
