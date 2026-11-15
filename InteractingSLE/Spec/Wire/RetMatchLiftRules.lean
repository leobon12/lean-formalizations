/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.RetMatchLiftContact
import InteractingSLE.Spec.Wire.RetMatchModel

/-!
# Lifetime history rules for stopped models

The exact general representation obligation is named separately from
determination. For a model stopped at its first positive real contact, the
representation is supplied by the existing uncapped hitting rule.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

namespace InteractingSLE.Wire.RetMatchLift

open Restart Restart.RetAux79 Restart.StoppedExtendWF LawUnique
open Sec2.Assembly Sec7.PocketTraversal

/-- A measurable Galmarino rule on the model's raw typed driving histories
identifies its lifetime almost surely. This property contains no code match. -/
def HasStoppedTypeHistoryRule {κ θ : ℝ} (M : StoppedTypeModel κ θ) : Prop :=
  ∃ R : HistorySpace M.data.nL M.data.nR → ℝ≥0∞,
    Measurable R ∧ IsHistGalmarino R ∧
      ∀ᵐ ω ∂M.law, M.data.life ω = R (killedHistory M.data.driver
        (geomLW M.data.driver M.data.xL) (geomRW M.data.driver M.data.xR)
        M.data.life ω)

/-- The unresolved general lifetime-rule representation, with exactly the
parameter and model range of the retained determination target. This is a
named hypothesis, not an asserted theorem. -/
def StoppedTypeHistoryRuleStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ : ℝ, ∀ M : StoppedTypeModel κ θ,
    HasStoppedTypeHistoryRule M

/-- A first-positive-real-contact model has the required lifetime rule.
The terminal-real premise applies only at finite lifetimes. -/
theorem hasStoppedTypeHistoryRule_of_firstRealContact {κ θ : ℝ}
    (M : StoppedTypeModel κ θ)
    (hH : ∀ᵐ ω ∂M.law, ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < M.data.life ω →
      M.data.trace ω t ∈ QuantumZipper.H)
    (hend : ∀ᵐ ω ∂M.law, ∀ T : ℝ≥0, (T : ℝ≥0∞) = M.data.life ω →
      (M.data.trace ω T).im = 0) :
    HasStoppedTypeHistoryRule M := by
  refine ⟨retPositiveRealRule, measurable_retPositiveRealRule,
    isStrongGalmarino_retPositiveRealRule.isHistGalmarino, ?_⟩
  filter_upwards [M.data.lifePos, M.data.generates, hH, hend]
    with ω hV hg hHω hendω
  have hc : ContinuousOn
      (fun t => (M.data.driver t ω, fun i => geomLW M.data.driver M.data.xL i t ω,
        fun j => geomRW M.data.driver M.data.xR j t ω))
      {t | (t : ℝ≥0∞) < M.data.life ω} :=
    (M.data.driverCont ω).continuousOn.prodMk
      ((continuousOn_pi.2 fun i =>
        (isForcePath_geomLW M.data.driverCont M.data.xL ω i).1.continuousOn).prodMk
        (continuousOn_pi.2 fun j =>
          (isForcePath_geomRW M.data.driverCont M.data.xR ω j).1.continuousOn))
  exact (retPositiveRealRule_eq_life hV hc (M.data.driverZero ω) hg hHω hendω).symm

/-- The named rule property discharges the only additional hypothesis of
the landed R79 model consumer. -/
theorem ae_codeMatch_of_historyRule {κ θ : ℝ} (M : StoppedTypeModel κ θ)
    (h13 : Exist.Theorem13Statement.{0}) (hκ : 0 < κ)
    (hR : HasStoppedTypeHistoryRule M)
    {Fc : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hFc : IsCanonicalFlowCode κ θ Fc) :
    ∀ᵐ ω ∂M.law, M.data.life ω ≤ (Fc ((M.data.word ω, 0), M.data.field ω)).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ M.data.life ω →
        M.data.trace ω t = decPath (Fc ((M.data.word ω, 0), M.data.field ω)) t := by
  obtain ⟨R, hRm, hRg, hRe⟩ := hR
  exact RetMatch.ae_codeMatch_of_model_historyRule M h13 hκ hFc hRm hRg hRe

/-- Stopped determination for the first-positive-real-contact case has no
remaining abstract lifetime-rule hypothesis. -/
theorem ae_codeMatch_of_firstRealContact {κ θ : ℝ} (M : StoppedTypeModel κ θ)
    (h13 : Exist.Theorem13Statement.{0}) (hκ : 0 < κ)
    {Fc : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hFc : IsCanonicalFlowCode κ θ Fc)
    (hH : ∀ᵐ ω ∂M.law, ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < M.data.life ω →
      M.data.trace ω t ∈ QuantumZipper.H)
    (hend : ∀ᵐ ω ∂M.law, ∀ T : ℝ≥0, (T : ℝ≥0∞) = M.data.life ω →
      (M.data.trace ω T).im = 0) :
    ∀ᵐ ω ∂M.law, M.data.life ω ≤ (Fc ((M.data.word ω, 0), M.data.field ω)).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ M.data.life ω →
        M.data.trace ω t = decPath (Fc ((M.data.word ω, 0), M.data.field ω)) t :=
  ae_codeMatch_of_historyRule M h13 hκ
    (hasStoppedTypeHistoryRule_of_firstRealContact M hH hend) hFc

end InteractingSLE.Wire.RetMatchLift
