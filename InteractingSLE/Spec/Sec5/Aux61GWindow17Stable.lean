/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GChoice15Windows
import InteractingSLE.Spec.Sec5.Aux61SlitWXChart

/-! # Window refinement preserves the retained chart

The chart model depends on the rational restart time, rather than on the
word, window, or selected set. Thus an initial-record restriction can
reuse the same weak chart exactly. The canonical normalized chart is
constructed with the same time-indexed design in the successor module.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set

namespace InteractingSLE.Sec5.Aux61GWindow17
open Aux61SlitW Aux61R1C Aux61Asm2 Aux61Marks LawUnique
universe u

/-- Retained times admitting the existing regular record model. -/
abbrev GoodTime (S : SourceSetting.{u}) :=
  {q : ℚ // (goodSet (nL := S.nL) (nR := S.nR) (rationalTime S.s) q).Nonempty}

/-- The old weak chart choice, written with its actual time parameter. -/
def weakRecordChart (S : SourceSetting.{u}) (t : GoodTime S) :
    SourceRecord S.nL S.nR → Chart :=
  Classical.choose (Classical.choose_spec (exists_isMeasChart_of_hasOriginalTargetRestartChart
    (Aux61R1C.hasChart (rationalTime_s_pos S) t.2))).2.2

/-- Equal restart times give the same literal retained-record chart,
even when the choice indices, windows and selections differ. -/
theorem chart_eq_of_time_eq {S : SourceSetting.{u}} (C D : RestartChoices S)
    (i : C.Idx) (j : D.Idx) (hq : C.q i.1 = D.q j.1) :
    C.toR1Restart.chart C.hasChart i = D.toR1Restart.chart D.hasChart j := by
  change weakRecordChart S ⟨C.q i.1, i.2⟩ = weakRecordChart S ⟨D.q j.1, j.2⟩
  exact congrArg (weakRecordChart S) (Subtype.ext hq)

end InteractingSLE.Sec5.Aux61GWindow17
