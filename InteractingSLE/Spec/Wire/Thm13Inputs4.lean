/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm13Inputs3
import InteractingSLE.Spec.Wire.Thm12Inputs4
import InteractingSLE.Spec.Sec7.TrialsHi4Wire
import InteractingSLE.Spec.ZhanGT4.RealTip
import InteractingSLE.Spec.Sec7.Lemma71FLift
import InteractingSLE.Spec.Sec7.Lemma71ETop

/-!
# Theorem 1.3 with the results landed since PROVE-WIRE3 plugged in

Packet PROVE-WIRE4 (no new mathematics). PROVE-WIRE3 left Theorem 1.3
(`Wire.ae_exists_isGeneratingTrace_of_open3`) with eight named inputs. Since then:

* the critical and singleton trial remainders are proved (`Sec7.TrialsHi4.lowCritStatement` for every `κ > 0` and
  `lo ≥ −2`, `Sec7.TrialsHi4.lp8CritStatement`, PROVE-TRIALS-HI4): `hmid`, `hlow`, `h8` are gone;
* Zhan's stopping collar for `κ > 4` follows from Astra's A.3 alone (the first swallowing of a fixed real point is a
  real crosscut; `ZhanGT4.stoppingCollarStatement_of_firstSwallowCrosscut`, with A.4.2 and A.4.3 landed): `hcol`
  becomes `hA3` (A.3 is vacuous for `κ ≤ 4`, so it is quantified over every `κ`).

**Five named inputs remain** (`ae_exists_isGeneratingTrace_of_open4`): `hPC`, `hhit`, `hR7`, `hPW`, `hA3`. `hPC`
(Lemma 7.1's chart-form pocket statement, universe 0) has two landed sources, each recorded as a variant:
Lemma 7.1's joint statement (`ae_exists_isGeneratingTrace_of_open4J`: `hPC` becomes the three `κ < 4` inputs `h411`,
`h51`, `hPCond` of Theorem 1.2 at universe 0) and Lemma 7.1's pinned pocket statement
(`ae_exists_isGeneratingTrace_of_pin4`). Each replaced input is implied by its replacements, so nothing is
strengthened.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Wire

/-- **Zhan's stopping collar for `κ > 4`** (WIRE3's `hcol`) from Astra's A.3 (the first-swallow crosscut). -/
theorem stoppingCollar_of_open4 (hA3 : ∀ κ : ℝ, ZhanGT4.FirstSwallowCrosscutStatement.{u} κ) :
    ∀ κ : ℝ, 4 < κ → ZhanGT4.StoppingCollarStatement.{u} κ :=
  fun κ hκ => ZhanGT4.stoppingCollarStatement_of_firstSwallowCrosscut hκ (hA3 κ)

/-- **Lemma 7.1's chart-form pocket statement** from the three `κ < 4` inputs of Lemma 7.1's joint statement
(PROVE-LEMMA72 `lemma71PocketChartStatement_of_joint`). -/
theorem lemma71PocketChartStatement_of_open4 (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (hPCond : Sec7.Lemma72C.PocketCondStatement.{u}) :
    Sec7.Lemma71C.Lemma71PocketChartStatement.{u} :=
  Sec7.Lemma72.lemma71PocketChartStatement_of_joint (lemma71JointStatement_of_open4 h411 h51 hPCond)

/-- **Lemma 7.1's chart-form pocket statement from the pinned pocket statement** (PROVE-LEMMA71F/E/C). -/
theorem lemma71PocketChartStatement_of_pin4 (hpin : Sec7.Lemma71F.Lemma71PocketPinStatement.{u}) :
    Sec7.Lemma71C.Lemma71PocketChartStatement.{u} :=
  Sec7.Lemma71C.lemma71PocketChartStatement_of_pocketCurve
    (Sec7.Lemma71E.lemma71PocketCurveStatement_of_pocket (Sec7.Lemma71F.lemma71PocketStatement_of_pin hpin))

/-- **Theorem 1.3 with Zhan's stopping collar as the `κ > 4` input** (instead of A.3; for a collar proved by another
route, e.g. A.1/A.2/A.5): five named inputs, `hPC`, `hhit`, `hR7`, `hPW`, `hcol`. -/
theorem ae_exists_isGeneratingTrace_of_collar4
    (hPC : Sec7.Lemma71C.Lemma71PocketChartStatement.{0})
    (hhit : WangWu.Theorem18.TwoSeedHittingStatement.{u} 4)
    (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (hcol : ∀ κ : ℝ, 4 < κ → ZhanGT4.StoppingCollarStatement.{u} κ)
    {a : ℝ} (ha : 0 < a := by assumption) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR := by assumption) {Ω : Type u}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ := by assumption) :
    ∀ᵐ ω ∂P, (ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
        (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) :=
  ae_exists_isGeneratingTrace_of_open3 hPC
    (fun κ hκ _ => Sec7.TrialsHi4.lowCritStatement hκ le_rfl)
    (fun κ hκ => Sec7.TrialsHi4.lowCritStatement (by linarith) (by linarith))
    (fun κ hκ => Sec7.TrialsHi4.lp8CritStatement (by linarith))
    hhit hR7 hPW hcol ha hF hE

/-- **Theorem 1.3 (continuity and endpoint)**, with exactly the conclusion of the frozen
`IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace`, in the provider shape (all of the anchor's arguments implicit,
its hypotheses `ha`, `hF`, `hE` auto-parameters), from the **five open** named inputs (conditional helper; it is not
the provider):

* `hPC` — Lemma 7.1's chart-form pocket statement (`κ < 4`, universe 0);
* `hhit` — the boundary-hitting two-seed words at `κ = 4`;
* `hR7` — Theorem R.7's reference (`κ > 4`);
* `hPW` — the pocket word evolutions of Lemma 7.25 (`κ > 4`, both weights below `κ/2 − 4`);
* `hA3` — Astra's A.3, the first-swallow crosscut of ordinary `SLE_κ` (`κ > 4`; vacuous otherwise). -/
theorem ae_exists_isGeneratingTrace_of_open4
    (hPC : Sec7.Lemma71C.Lemma71PocketChartStatement.{0})
    (hhit : WangWu.Theorem18.TwoSeedHittingStatement.{u} 4)
    (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (hA3 : ∀ κ : ℝ, ZhanGT4.FirstSwallowCrosscutStatement.{u} κ)
    {a : ℝ} (ha : 0 < a := by assumption) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR := by assumption) {Ω : Type u}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ := by assumption) :
    ∀ᵐ ω ∂P, (ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
        (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) :=
  ae_exists_isGeneratingTrace_of_collar4 hPC hhit hR7 hPW (stoppingCollar_of_open4 hA3) ha hF hE

/-- **Theorem 1.3, `hPC` through Lemma 7.1's joint statement**: seven named inputs, `h411`, `h51`, `hPCond` (the
`κ < 4` inputs of Theorem 1.2, here at universe 0), `hhit`, `hR7`, `hPW`, `hA3`. -/
theorem ae_exists_isGeneratingTrace_of_open4J
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{0}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{0})
    (hPCond : Sec7.Lemma72C.PocketCondStatement.{0})
    (hhit : WangWu.Theorem18.TwoSeedHittingStatement.{u} 4)
    (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (hA3 : ∀ κ : ℝ, ZhanGT4.FirstSwallowCrosscutStatement.{u} κ)
    {a : ℝ} (ha : 0 < a := by assumption) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR := by assumption) {Ω : Type u}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ := by assumption) :
    ∀ᵐ ω ∂P, (ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
        (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) :=
  ae_exists_isGeneratingTrace_of_open4 (lemma71PocketChartStatement_of_open4 h411 h51 hPCond) hhit hR7 hPW hA3
    ha hF hE

/-- **Theorem 1.3, `hPC` through Lemma 7.1's pinned pocket statement** (PROVE-LEMMA71M's target): five named inputs,
`hpin`, `hhit`, `hR7`, `hPW`, `hA3`. -/
theorem ae_exists_isGeneratingTrace_of_pin4
    (hpin : Sec7.Lemma71F.Lemma71PocketPinStatement.{0})
    (hhit : WangWu.Theorem18.TwoSeedHittingStatement.{u} 4)
    (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (hA3 : ∀ κ : ℝ, ZhanGT4.FirstSwallowCrosscutStatement.{u} κ)
    {a : ℝ} (ha : 0 < a := by assumption) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR := by assumption) {Ω : Type u}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ := by assumption) :
    ∀ᵐ ω ∂P, (ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
        (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) :=
  ae_exists_isGeneratingTrace_of_open4 (lemma71PocketChartStatement_of_pin4 hpin) hhit hR7 hPW hA3 ha hF hE

/-- **Theorem 1.3 as the named form `Exist.Theorem13Statement`** (the frozen anchor's type), from the same five open
inputs (conditional helper; for the consumers of the frozen type: the flow-line companion, the staged histories). -/
theorem theorem13Statement_of_open4
    (hPC : Sec7.Lemma71C.Lemma71PocketChartStatement.{0})
    (hhit : WangWu.Theorem18.TwoSeedHittingStatement.{u} 4)
    (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (hA3 : ∀ κ : ℝ, ZhanGT4.FirstSwallowCrosscutStatement.{u} κ) :
    Exist.Theorem13Statement.{u} := by
  intro _ ha _ _ _ _ _ _ hF _ _ _ _ _ _ _ _ _ _ hE
  exact ae_exists_isGeneratingTrace_of_open4 hPC hhit hR7 hPW hA3 ha hF hE

end Wire

end InteractingSLE
