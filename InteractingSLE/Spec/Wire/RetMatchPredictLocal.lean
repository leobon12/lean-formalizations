/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.RetMatchPredictStops

/-!
# Reduction to positive bounded pre-lifetime stopping rules

The new mathematical input is local: a positive bounded stopping time strictly
before the model's lifetime has a measurable Galmarino representation. The
proved positive bounded announcing sequence and supremum closure then give
the previously named general lifetime representation.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.RetMatchPredict

open Restart.RetAux79 Restart.StoppedExtendWF LawUnique Sec7.PocketTraversal RetMatchLift

/-- Remaining local probability input. The stopping time is deterministically
bounded, positive almost surely, and strictly before the lifetime. No lifetime
representation or field determination is included in its conclusion. -/
def PositiveBoundedPrelifeRuleStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ : ℝ, ∀ M : StoppedTypeModel κ θ,
    ∀ (σ : M.space → WithTop ℝ≥0) (b : ℝ≥0),
      IsStoppingTime (drivingFiltration M.law M.data.killedMeas) σ →
      (∀ ω, (σ ω : ℝ≥0∞) ≤ (b : ℝ≥0∞)) →
      (∀ᵐ ω ∂M.law, 0 < (σ ω : ℝ≥0∞) ∧ (σ ω : ℝ≥0∞) < M.data.life ω) →
      ∃ Q : HistorySpace M.data.nL M.data.nR → ℝ≥0∞,
        Measurable Q ∧ IsHistGalmarino Q ∧
          ∀ᵐ ω ∂M.law, (σ ω : ℝ≥0∞) = Q (killedHistory M.data.driver
            (geomLW M.data.driver M.data.xL) (geomRW M.data.driver M.data.xR)
            M.data.life ω)

/-- The local representation input suffices for each model: represent the
positive bounded announcing stops, then take their countable supremum. -/
theorem hasStoppedTypeHistoryRule_of_positiveBoundedPrelifeRules
    (hLocal : PositiveBoundedPrelifeRuleStatement)
    {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (M : StoppedTypeModel κ θ) :
    HasStoppedTypeHistoryRule M := by
  have h : ∀ n : ℕ, ∃ Q : HistorySpace M.data.nL M.data.nR → ℝ≥0∞,
      Measurable Q ∧ IsHistGalmarino Q ∧
        ∀ᵐ ω ∂M.law, (boundedDriveStop M n ω : ℝ≥0∞) = Q (killedHistory M.data.driver
          (geomLW M.data.driver M.data.xL) (geomRW M.data.driver M.data.xR)
          M.data.life ω) := by
    intro n
    exact hLocal κ hκ hκ4 θ M (boundedDriveStop M n) ((n : ℝ≥0) + 1)
      (isStoppingTime_boundedDriveStop M n) (boundedDriveStop_le M n)
      ((ae_boundedDriveStop_bounds M).mono fun _ h => h n)
  choose Q hQm hQg hQeq using h
  have hall := ae_all_iff.2 hQeq
  have hmono : ∀ᵐ ω ∂M.law, Monotone fun n => Q n (killedHistory M.data.driver
      (geomLW M.data.driver M.data.xL) (geomRW M.data.driver M.data.xR)
      M.data.life ω) := by
    filter_upwards [hall] with ω he n k hnk
    exact (he n).symm.trans_le
      ((monotone_boundedDriveStop M ω hnk).trans_eq (he k))
  have hlim : ∀ᵐ ω ∂M.law, Tendsto
      (fun n => Q n (killedHistory M.data.driver
        (geomLW M.data.driver M.data.xL) (geomRW M.data.driver M.data.xR)
        M.data.life ω)) atTop (𝓝 (M.data.life ω)) := by
    filter_upwards [hall, ae_tendsto_boundedDriveStop M] with ω he hl
    have heq : (fun n => Q n (killedHistory M.data.driver
        (geomLW M.data.driver M.data.xL) (geomRW M.data.driver M.data.xR)
        M.data.life ω)) = fun n => (boundedDriveStop M n ω : ℝ≥0∞) :=
      funext fun n => (he n).symm
    exact heq.symm ▸ hl
  exact hasStoppedTypeHistoryRule_of_ruleSequence M hQm hQg hmono hlim

/-- The previously open global representation reduces to positive bounded
stopping times strictly before the lifetime. -/
theorem stoppedTypeHistoryRuleStatement_of_positiveBoundedPrelifeRules
    (hLocal : PositiveBoundedPrelifeRuleStatement) : StoppedTypeHistoryRuleStatement := by
  intro κ hκ hκ4 θ M
  exact hasStoppedTypeHistoryRule_of_positiveBoundedPrelifeRules hLocal hκ hκ4 M

end InteractingSLE.Wire.RetMatchPredict
