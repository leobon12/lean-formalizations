/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.RetMatchPredictLocal
import InteractingSLE.Spec.Wire.RetMatchLiftWire

/-!
# Retained determination from positive bounded pre-lifetime rules

The representation input is localized to bounded stops strictly before the
lifetime. All approximation, limiting, stopped-coupling and transport steps
are supplied by proved lemmas; the target statements remain unchanged.
-/

set_option autoImplicit false
noncomputable section

namespace InteractingSLE.Wire.RetMatchPredict

/-- The unchanged model determination target from the local pre-lifetime
representation theorem and the permitted Theorem 1.3. -/
theorem retStoppedTypeDeterminationStatement_of_positiveBoundedPrelifeRules
    (h13 : Exist.Theorem13Statement.{0}) (hLocal : PositiveBoundedPrelifeRuleStatement) :
    RetStoppedTypeDeterminationStatement :=
  RetMatchLift.retStoppedTypeDeterminationStatement_of_historyRules h13
    (stoppedTypeHistoryRuleStatement_of_positiveBoundedPrelifeRules hLocal)

universe v

/-- The unchanged retained determination of Lemma 7.6, in any outer universe,
from the local representation input and the permitted source results. -/
theorem lemma76DetRStatement_of_positiveBoundedPrelifeRules
    (h13 : Exist.Theorem13Statement.{0}) (hLocal : PositiveBoundedPrelifeRuleStatement)
    (h75 : Theorem15.Lemma75Statement.{v}) : Sec7.Lemma76DetRStatement.{v} :=
  RetMatchLift.lemma76DetRStatement_of_historyRules h13
    (stoppedTypeHistoryRuleStatement_of_positiveBoundedPrelifeRules hLocal) h75

end InteractingSLE.Wire.RetMatchPredict
