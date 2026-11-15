/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.RetMatchLiftRules
import InteractingSLE.Spec.Wire.Thm1415LateRetain

/-!
# Retained determination from the lifetime-rule representation

The named hypothesis is the exact remaining lifetime-rule mathematics. The
conclusions are the existing retained model determination statement and the
source-faithful Lemma 7.6 determination statement, with no change to either.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace InteractingSLE.Wire.RetMatchLift

/-- The R79 model consumer discharges the retained determination target from
the explicitly named general lifetime-rule representation. -/
theorem retStoppedTypeDeterminationStatement_of_historyRules
    (h13 : Exist.Theorem13Statement.{0}) (hRules : StoppedTypeHistoryRuleStatement) :
    RetStoppedTypeDeterminationStatement := by
  intro κ hκ hκ4 θ M Fc hFc
  exact ae_codeMatch_of_historyRule M h13 hκ (hRules κ hκ hκ4 θ M) hFc

universe v

/-- The same rule hypothesis, together with Lemma 7.5 and Theorem 1.3, gives
the unchanged retained determination of Lemma 7.6 in any outer universe. -/
theorem lemma76DetRStatement_of_historyRules
    (h13 : Exist.Theorem13Statement.{0}) (hRules : StoppedTypeHistoryRuleStatement)
    (h75 : Theorem15.Lemma75Statement.{v}) : Sec7.Lemma76DetRStatement.{v} :=
  lemma76DetRStatement_of_modelMatch_late
    (retStoppedTypeDeterminationStatement_of_historyRules h13 hRules) h75

end InteractingSLE.Wire.RetMatchLift
