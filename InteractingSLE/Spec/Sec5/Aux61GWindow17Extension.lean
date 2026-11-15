/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow17Records
import InteractingSLE.Spec.Sec5.Aux61SlitWABSeed

/-! # Certified-record inverse extension for the canonical chart

Reuse SLITW's stopped counterflow certificates with the full canonical
chart certificate. This supplies the analytic input of initial-record
window selection without identifying independent chart choices.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull)
open QuantumZipper.CA (cayley)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWindow17
open Aux61SlitW Aux61R1C Aux61Asm2 Aux61Restart Aux61FibData Aux61GInst Aux61ULoc LawUnique
open WangWu (negInv)
universe u

/-- SLITW's fixed Borel certified-record set for the canonical time model. -/
abbrev certifiedRecords (S : SourceSetting.{u}) (t : GoodTime S) :=
  Aux61SlitWAB.certifiedSelection (baseChoices S t.1) (baseIndex S t)

theorem measurableSet_certifiedRecords (S : SourceSetting.{u}) (t : GoodTime S) :
    MeasurableSet (certifiedRecords S t) :=
  Aux61SlitWAB.measurableSet_certifiedSelection _ (fun _ => MeasurableSet.univ) _

/-- The actual canonical inverse extension on every certified record.
Only the already constructed retained-record certificates are required. -/
theorem recordChart_extension (S : SourceSetting.{u}) (t : GoodTime S)
    {y : SourceRecord S.nL S.nR} (hy : y ∈ certifiedRecords S t) :
    EqOn (boundedInverse (recordChart S t y)) (cayley ∘ (recordChart S t y).2.1) H ∧
      ContinuousOn (boundedInverse (recordChart S t y)) Hbar := by
  have hg : y ∈ goodSet (rationalTime S.s) t.1 := hy.1.2
  obtain ⟨-, -, -, -, -, hH, hηc, hη0, -⟩ := hg.1.facts
  have hd := (recordChart_spec S t).domain y
  change ((recordChart S t y).dom : Set ℂ) = restartComponent
    (historyHull (rationalTime S.s) (finY (rationalTime S.s) t.1) y)
    (finη (rationalTime S.s) t.1 y) t.1 _ at hd
  rw [historyHull, finY_of_mem hg, finη_of_mem hg,
    Aux61SlitWAB.cfDrv0_eq_frozenDrv hy.2.1] at hd
  have hc := (recordChart_spec S t).conformal y
  have hb : Aux61SlitWX.base (baseChoices S t.1).toR1Restart
      (baseChoices S t.1).hasChart (baseIndex S t) y ∈ retainedDomain
      (negInv '' fwdHull (Ito.rpath (frozenDrv (rationalTime S.s) y.1)) (rationalTime S.s))
      (recη t.1 y) t.1 := by
    apply connectedComponentIn_nonempty_iff.1
    change (restartComponent _ _ _ _).Nonempty
    rw [← hd]
    exact ⟨_, hc.inv_mem_dom (by change 0 < Complex.I.im; norm_num)⟩
  have hηH : MapsTo (recη t.1 y) (Icc 0 (t.1 : ℝ)) Hbar := by
    intro r hr
    rcases hr.1.eq_or_lt with hr0 | hr0
    · rw [← hr0, hη0]
      exact zero_mem_Hbar
    · exact QuantumZipper.H_subset_Hbar (hH ⟨hr0, hr.2⟩)
  have hF := boundedInverse_spec_of_traces
    (hy.2.1.isLoewnerTrace_fullTrace hy.2.2 (rationalTime_s_pos S))
    (rationalTime S.s).coe_nonneg hηc hηH hb hc hd
  exact ⟨hF.1, hF.2.1⟩

/-- The canonical inverse at each real coordinate is measurable on the
fixed certified-record set. -/
theorem measurable_recordChart_inverse (S : SourceSetting.{u}) (t : GoodTime S) (a : ℝ) :
    Measurable ((certifiedRecords S t).indicator fun y =>
      boundedInverse (recordChart S t y) (a : ℂ)) :=
  measurable_boundedInverse_real (measurableSet_certifiedRecords S t)
    (recordChart_spec S t).measurable (fun y _ => (recordChart_spec S t).conformal y)
    (fun _ hy => recordChart_extension S t hy) a

end InteractingSLE.Sec5.Aux61GWindow17
