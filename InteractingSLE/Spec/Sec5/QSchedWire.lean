/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.QSchedMain
import InteractingSLE.Spec.Sec5.QSchedBase

/-!
# `FrameQ.QScheduleFirstHitStatement` from the chart leaves in their (4.4) form

Packet PROVE-QSCHED. Composition of `qScheduleFirstHitStatement_of_input` (the induction on the number of
switches) with `counterflowGivenPrefix44Statement_of_leaves` (the restart law at a switch from the positive-time
chart base, PROVED from Part A and the §4.2 reference, and the four CfChart leaves in their (4.4)-height form, plus
the mirror-image chart form).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

universe u

namespace InteractingSLE.Sec5.QSched

/-- **Lemma 5.7 for the finite extreme-angle schedules in the Q frame from Lemma 4.7, `h44`, Part A, the §4.2
reference and the chart leaves in their (4.4) form.** -/
theorem qScheduleFirstHitStatement_of_leaves (h44 : Sec7.AdmCode.Theorem12ParamCond44Statement.{u})
    (h47 : Prop411Q.Lemma47QHitStatement.{u}) (hA : PartAInputsSixteenDivOfClearance)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hInt : Converted44IntegrableOn.{u})
    (hRed : Converted44ReductionOn (positiveChartBase44Statement hA href))
    (hLoc : Converted44LocalOn (positiveChartBase44Statement hA href)) (hZero : ZeroChart44Statement.{u})
    (hDn : CfGivenChart44DownStatement.{u}) : FrameQ.QScheduleFirstHitStatement.{u} :=
  qScheduleFirstHitStatement_of_input h44 h47 href
    (counterflowGivenPrefix44Statement_of_leaves hA href hInt hRed hLoc hZero hDn)

end InteractingSLE.Sec5.QSched
