/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.RetMatchMeyerPredict
import InteractingSLE.Spec.Wire.RetMatchLiftWire

/-!
# Retained determination with one standard predictable-lifting input

The model already announces its lifetime. The new proof uses that announcement
directly, so the sole unresolved input here is the generic standard theorem
`PredictableAnnouncingLiftingStatement` (Dellacherie--Meyer IV.78). Neither the
canonical regularization statement nor an SLE predictability statement is an
assumption of these endpoints. The original target statements are unchanged.
-/

set_option autoImplicit false
noncomputable section

namespace InteractingSLE.Wire.RetMatchMeyer

/-- Every model's lifetime-rule representation follows from the one generic
standard predictable-time lifting theorem. -/
theorem stoppedTypeHistoryRuleStatement_of_predictableLifting
    (hMeyer : PredictableAnnouncingLiftingStatement) :
    RetMatchLift.StoppedTypeHistoryRuleStatement := by
  intro κ _ _ θ M
  exact hasStoppedTypeHistoryRule_of_predictableLifting hMeyer M

/-- The exact packet target, using the permitted Theorem 1.3 and the one
standard augmentation-removal input. -/
theorem retStoppedTypeDeterminationStatement_of_predictableLifting
    (h13 : Exist.Theorem13Statement.{0}) (hMeyer : PredictableAnnouncingLiftingStatement) :
    RetStoppedTypeDeterminationStatement :=
  RetMatchLift.retStoppedTypeDeterminationStatement_of_historyRules h13
    (stoppedTypeHistoryRuleStatement_of_predictableLifting hMeyer)

universe v

/-- The unchanged Lemma 7.6 determination statement in every outer universe,
with the same single standard lifting input and the permitted source inputs. -/
theorem lemma76DetRStatement_of_predictableLifting
    (h13 : Exist.Theorem13Statement.{0}) (hMeyer : PredictableAnnouncingLiftingStatement)
    (h75 : Theorem15.Lemma75Statement.{v}) : Sec7.Lemma76DetRStatement.{v} :=
  RetMatchLift.lemma76DetRStatement_of_historyRules h13
    (stoppedTypeHistoryRuleStatement_of_predictableLifting hMeyer) h75

end InteractingSLE.Wire.RetMatchMeyer
