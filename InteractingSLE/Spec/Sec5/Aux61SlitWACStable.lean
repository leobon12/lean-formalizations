/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWZRead

/-! # The complete normalized selector is stable at a fixed retained time

Although `ChartFacts` is indexed by a whole restart model, its fields
depend only on the retained time and the R1 readers. Extensionality of
its predicate preserves the chosen normalized witness across changes
of windows, reference words, indices and selected-record restrictions.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set

namespace InteractingSLE.Sec5.Aux61SlitWAC
open Aux61SlitW Aux61SlitWX Aux61R1C Aux61Asm2 LawUnique
universe u
variable {S : SourceSetting.{u}} (C D : RestartChoices S)

/-- The full chart certificate transports at an equal retained time;
the selected sets and the continuation windows do not enter its fields. -/
theorem chartFacts_of_time_eq (i : C.Idx) (j : D.Idx) (hq : C.q i.1 = D.q j.1)
    {b : SourceRecord S.nL S.nR → ℂ} {c : SourceRecord S.nL S.nR → Chart}
    (h : ChartFacts C.toR1Restart i b c) : ChartFacts D.toR1Restart j b c := by
  refine ⟨h.base_measurable, ?_, h.measurable, h.conformal, ?_, h.target,
    h.continuous_lift, h.lift, ?_, h.infty⟩
  · simpa only [RestartChoices.toR1Restart, hq] using h.base_mem
  · simpa only [RestartChoices.toR1Restart, hq] using h.domain
  · simpa only [RestartChoices.toR1Restart, hq] using h.current

/-- Predicate equality, rather than equality of existence proofs,
identifies the two complete normalized chart choices. -/
theorem normalized_witness_eq_of_time_eq (i : C.Idx) (j : D.Idx)
    (hq : C.q i.1 = D.q j.1) :
    chartWitness C.toR1Restart C.hasChart i = chartWitness D.toR1Restart D.hasChart j := by
  unfold chartWitness
  congr 1
  funext p
  exact propext ⟨chartFacts_of_time_eq C D i j hq, chartFacts_of_time_eq D C j i hq.symm⟩

/-- The normalized chart itself is unchanged by any refinement at the
same retained time. This does not identify it with the weak selector. -/
theorem normalized_chart_eq_of_time_eq (i : C.Idx) (j : D.Idx) (hq : C.q i.1 = D.q j.1) :
    Aux61SlitWX.chart C.toR1Restart C.hasChart i =
      Aux61SlitWX.chart D.toR1Restart D.hasChart j :=
  congrArg Prod.snd (normalized_witness_eq_of_time_eq C D i j hq)

/-- The accompanying measurable base is preserved as well. -/
theorem normalized_base_eq_of_time_eq (i : C.Idx) (j : D.Idx) (hq : C.q i.1 = D.q j.1) :
    Aux61SlitWX.base C.toR1Restart C.hasChart i =
      Aux61SlitWX.base D.toR1Restart D.hasChart j :=
  congrArg Prod.fst (normalized_witness_eq_of_time_eq C D i j hq)

end InteractingSLE.Sec5.Aux61SlitWAC
