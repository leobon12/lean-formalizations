/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm13Inputs4
import InteractingSLE.Spec.ZhanGT4.CrosscutA31
import InteractingSLE.WangWu.Prop424Chart

/-!
# Theorem 1.3 with the A.3 reduction plugged in

Theorem 1.3's existing chart-form pocket input and the κ = 4 and κ > 4 inputs remain open. Astra's proved A.3 wiring
reduces its former first-swallow input to the two named A.2 statements.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Wire

/-- **Theorem 1.3 (trace existence and continuity)**, with exactly the conclusion of the frozen anchor, from the six
remaining named inputs. A.3 is supplied by `A35.firstSwallowCrosscutStatement_of_A2`. -/
theorem ae_exists_isGeneratingTrace_of_open6
    (hPC : Sec7.Lemma71C.Lemma71PocketChartStatement.{0})
    (hC4 : WangWu.Chamber4.Chamber4JointStatement.{u})
    (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR →
      rR < κ / 2 - 4 → Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (hA2 : ∀ κ : ℝ, ZhanGT4.A34.FourForceCrosscutG3LifeStatement.{0} κ)
    (hA2' : ∀ κ : ℝ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{u} κ)
    {a : ℝ} (ha : 0 < a := by assumption) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR := by assumption)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ := by assumption) :
    ∀ᵐ ω ∂P, (ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
        (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) :=
  ae_exists_isGeneratingTrace_of_open4 hPC
    (WangWu.Chamber4.twoSeedHittingStatement_four_of_joint hC4) hR7 hPW
    (ZhanGT4.A35.forall_firstSwallowCrosscutStatement_of_A2 hA2 hA2') ha hF hE

/-- **Theorem 1.3 as `Exist.Theorem13Statement`**, the frozen-anchor type, from the same six open inputs. -/
theorem theorem13Statement_of_open6
    (hPC : Sec7.Lemma71C.Lemma71PocketChartStatement.{0})
    (hC4 : WangWu.Chamber4.Chamber4JointStatement.{u})
    (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR →
      rR < κ / 2 - 4 → Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (hA2 : ∀ κ : ℝ, ZhanGT4.A34.FourForceCrosscutG3LifeStatement.{0} κ)
    (hA2' : ∀ κ : ℝ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{u} κ) : Exist.Theorem13Statement.{u} := by
  intro _ ha _ _ _ _ _ _ hF _ _ _ _ _ _ _ _ _ _ hE
  exact ae_exists_isGeneratingTrace_of_open6 hPC hC4 hR7 hPW hA2 hA2' ha hF hE

end Wire

end InteractingSLE
