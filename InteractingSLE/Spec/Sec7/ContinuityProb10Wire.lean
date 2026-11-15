import InteractingSLE.Spec.Wire.Thm13Inputs2
import InteractingSLE.Spec.Sec7.ContinuityProb9OneMark
import InteractingSLE.Spec.Sec7.ContinuityProb10Seed

/-!
# Theorem 1.3 with the one-sided, LP9 and Aux. 99 inputs discharged

Packet PROVE-TRACECLOSE (wiring; no new mathematics). PROVE-WIRE2 left Theorem 1.3
(`Wire.ae_exists_isGeneratingTrace_of_remaining2`) with twelve named inputs. Since then:

* `h1s` (the prefix of the one-sided step) is `Sec7.oneSidedPrefixStatement` (from the trace-closure fact
  `Sec7.traceClosureStatement`, this packet, and PROVE-SEC7-C10's `oneSidedPrefixStatement_of_closure`);
* `h9` (LP9's prefix) is `Sec7.lp9PrefixStatement` for every `κ > 0` (the trace-closure fact and the two-sided seed
  `Sec7.lp9SeedTraceStatement`, this packet);
* `h99` (Aux. lemma 99 stopped) follows, for every `κ > 0`, from the seed one-force theorem
  (`Sec7.aux99StoppedStatement_of_seed`, PROVE-SEC7-C10). The seed one-force theorem is derived here from inputs that do
  not contain Aux. lemma 99 (`seedOneForce_of_remaining3`): for `κ < 4` from Proposition 7.3's trace, i.e. from Lemma 7.1's
  pocket statement `hP` (`Wire.prop73TraceStatement_of_pocket2`, `Sec7.isCompleteForceWord_seedRight_of_prop73Trace`);
  for `κ = 4` from the boundary-hitting two-seed words `hhit` (`WangWu.Theorem18.twoSeedComplete_of_hitting`); for
  `κ > 4` from LP10's two-seed premise, i.e. from `hR7`, `hPW`, `hcol`, `hRS` (`Wire.twoSeedComplete_of_remainingB`),
  through `LP.seedOneForce_of_twoSeedComplete`. Lean checks that none of these takes an `Aux99StoppedStatement`.

**Nine named inputs remain**: `hP`, `hmid`, `hhit`, `hlow`, `h8T`, `hR7`, `hPW`, `hcol`, `hRS` (meanings as in
`Wire.ae_exists_isGeneratingTrace_of_remaining2`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Wire

/-- **The seed one-force theorem for every `κ > 0`** (one right mark at `0⁺` of weight `> −2` gives a complete word),
from inputs that do not contain Aux. lemma 99 (conditional helper). -/
theorem seedOneForce_of_remaining3 (hP : Sec7.Lemma71E.Lemma71PocketStatement.{0})
    (hhit : WangWu.Theorem18.TwoSeedHittingStatement.{u} 4) (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (hcol : ∀ κ : ℝ, 4 < κ → ZhanGT4.StoppingCollarStatement.{u} κ) (hRS : LP.LP4RightSwallowStatement.{u})
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ (xL ρL : Fin 0 → ℝ) (ρR : Fin 1 → ℝ), -2 < ρR 0 → LP.IsCompleteForceWord.{u} κ xL (fun _ => 0) ρL ρR := by
  rcases lt_trichotomy κ 4 with h4 | rfl | h4
  · intro xL ρL ρR hρ
    exact Sec7.isCompleteForceWord_seedRight_of_prop73Trace (prop73TraceStatement_of_pocket2.{0} hP) hκ h4 xL
      (fun _ => 0) ρL ρR (fun _ => rfl) fun i => by rw [Fin.fin_one_eq_zero i]; exact hρ
  · exact LP.seedOneForce_of_twoSeedComplete hκ
      (WangWu.Theorem18.twoSeedComplete_of_hitting (by norm_num) le_rfl hhit)
  · exact LP.seedOneForce_of_twoSeedComplete hκ (twoSeedComplete_of_remainingB hR7
      (Sec7.Lemma725Ref.lemma725DriverReferenceStatement_of_pocketWordEvolution hPW)
      (lp4AvoidStatement_of_remaining2 hcol hRS) h4)

/-- **Aux. lemma 99 stopped for every `κ > 0`** from the seed one-force theorem (conditional helper). -/
theorem aux99StoppedStatement_of_remaining3 (hP : Sec7.Lemma71E.Lemma71PocketStatement.{0})
    (hhit : WangWu.Theorem18.TwoSeedHittingStatement.{u} 4) (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (hcol : ∀ κ : ℝ, 4 < κ → ZhanGT4.StoppingCollarStatement.{u} κ) (hRS : LP.LP4RightSwallowStatement.{u})
    {κ : ℝ} (hκ : 0 < κ) : Sec7.Aux99StoppedStatement.{u} κ :=
  Sec7.aux99StoppedStatement_of_seed hκ (seedOneForce_of_remaining3 hP hhit hR7 hPW hcol hRS hκ)

/-- **Theorem 1.3 (continuity and endpoint)**, with exactly the conclusion of the frozen
`IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace`, in the provider shape, from the **nine remaining** named inputs
(conditional helper; it is not the provider): `ae_exists_isGeneratingTrace_of_remaining2` with `h1s`, `h9` proved and
`h99` from the seed one-force theorem. -/
theorem ae_exists_isGeneratingTrace_of_remaining3
    (hP : Sec7.Lemma71E.Lemma71PocketStatement.{0})
    (hmid : ∀ κ : ℝ, 0 < κ → κ < 4 → Sec7.TrialsHi2.HighTrialMidStatement.{u} κ)
    (hhit : WangWu.Theorem18.TwoSeedHittingStatement.{u} 4)
    (hlow : ∀ κ : ℝ, 4 ≤ κ → Sec7.TrialsHi.HighTrialLowStatement.{u} κ)
    (h8T : ∀ κ : ℝ, 4 < κ → Sec7.TrialsHi.LP8TrialStatement.{u} κ)
    (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (hcol : ∀ κ : ℝ, 4 < κ → ZhanGT4.StoppingCollarStatement.{u} κ)
    (hRS : LP.LP4RightSwallowStatement.{u})
    {a : ℝ} (ha : 0 < a := by assumption) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR := by assumption) {Ω : Type u}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ := by assumption) :
    ∀ᵐ ω ∂P, (ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
        (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) :=
  ae_exists_isGeneratingTrace_of_remaining2 hP
    (fun κ hκ => aux99StoppedStatement_of_remaining3 hP hhit hR7 hPW hcol hRS hκ) hmid
    Sec7.oneSidedPrefixStatement hhit hlow (fun κ hκ => Sec7.lp9PrefixStatement (by linarith)) h8T hR7 hPW hcol hRS
    ha hF hE

end Wire

end InteractingSLE
