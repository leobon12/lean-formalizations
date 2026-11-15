/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.RetMatchExplicitApprox
import InteractingSLE.Spec.Wire.RetMatchExplicitAnnounce

/-!
# Predictable-time lifting proved, and retained determination without that input

The exact generic statement isolated in the preceding handoff follows from raw
dyadic approximations, a summable-error diagonal, and attained tail minima.
The retained endpoints therefore no longer assume any lifting or history-rule
statement. Their remaining hypotheses are the permitted source inputs.
-/

set_option autoImplicit false
noncomputable section

namespace InteractingSLE.Wire.RetMatchExplicit

/-- The exact formerly named predictable-time lifting statement, proved from
an explicit announcing sequence with no additional stochastic input. -/
theorem predictableAnnouncingLiftingStatement :
    RetMatchMeyer.PredictableAnnouncingLiftingStatement := by
  intro Ω mΩ P hP 𝓕 V A hVm hA
  obtain ⟨R, hR, hgood⟩ := exists_raw_approximation_of_announcingSeq hVm hA
  exact exists_raw_announcingSeq_of_approximation hR hgood

/-- Every stopped model has a measurable global Galmarino lifetime rule. -/
theorem hasStoppedTypeHistoryRule {κ θ : ℝ} (M : Restart.RetAux79.StoppedTypeModel κ θ) :
    RetMatchLift.HasStoppedTypeHistoryRule M :=
  RetMatchMeyer.hasStoppedTypeHistoryRule_of_predictableLifting
    predictableAnnouncingLiftingStatement M

/-- The exact packet endpoint, using only the permitted Theorem 1.3 input. -/
theorem retStoppedTypeDeterminationStatement (h13 : Exist.Theorem13Statement.{0}) :
    RetStoppedTypeDeterminationStatement :=
  RetMatchMeyer.retStoppedTypeDeterminationStatement_of_predictableLifting h13
    predictableAnnouncingLiftingStatement

universe v

/-- The unchanged retained Lemma 7.6 determination statement with no additional
standard-theorem hypothesis, in every outer universe. -/
theorem lemma76DetRStatement (h13 : Exist.Theorem13Statement.{0})
    (h75 : Theorem15.Lemma75Statement.{v}) : Sec7.Lemma76DetRStatement.{v} :=
  RetMatchMeyer.lemma76DetRStatement_of_predictableLifting h13
    predictableAnnouncingLiftingStatement h75

end InteractingSLE.Wire.RetMatchExplicit
