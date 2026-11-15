/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWZRead
import InteractingSLE.Spec.Sec5.Aux61SlitWXSelection

/-! # All global model facts for the actual restart choices

The good-record retraction already defines the continuous Loewner model
on every raw record. This adapter exposes all its `ModelFacts` directly.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology

namespace InteractingSLE.Sec5.Aux61SlitWZ
open Aux61SlitW Aux61SlitWX Aux61R1C Aux61Asm2 Aux61ULoc LawUnique
universe u
variable {S : SourceSetting.{u}} (C : RestartChoices S)

/-- The actual choices' total model satisfies every global analytic and
measurability clause; no model hypothesis or selected-set premise remains. -/
theorem modelFacts : ModelFacts C.toR1Restart := by
  have hgood : ∀ (i : C.Idx) (y : SourceRecord S.nL S.nR),
      retr (C.good i.1) y ∈ C.good i.1 := fun i => retr_mem i.2
  have hm := fun i : C.Idx => measurable_retr
    (measurableSet_goodSet (nL := S.nL) (nR := S.nR) (rationalTime S.s) (C.q i.1))
  refine
    { q_pos := fun i => (hgood i (pickIn (C.good i.1))).1.facts.1
      time := fun i => coe_rationalTime (C.q_nonneg i)
      counterflow_measurable := fun i =>
        (GlueCond.measurable_cfStop _).comp (measurable_fst.comp (hm i))
      driver_continuous := fun i y => (hgood i y).1.facts.2.1
      driver_zero := fun i y => (hgood i y).1.facts.2.2.1
      driver_measurable := fun i t _ => (measurable_recU (C.q i.1) t).comp (hm i)
      loewner := fun i y => (hgood i y).1.facts.2.2.2.1
      path_measurable := fun i t ht => (measurable_recη (C.q_nonneg i) ht.2).comp (hm i)
      dense := TopologicalSpace.denseRange_denseSeq ℂ }

end InteractingSLE.Sec5.Aux61SlitWZ
