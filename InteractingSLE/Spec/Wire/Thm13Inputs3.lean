/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb10Wire
import InteractingSLE.Spec.Sec7.TrialsHi3Wire
import InteractingSLE.Spec.Supplement.LP4Swallow
import InteractingSLE.Spec.Sec7.Lemma71CTop
import InteractingSLE.Spec.Exist.DetField

/-!
# Theorem 1.3 with the results landed since PROVE-TRACECLOSE plugged in

Packet PROVE-WIRE3 (no new mathematics). PROVE-TRACECLOSE left Theorem 1.3
(`Wire.ae_exists_isGeneratingTrace_of_remaining3`) with nine named inputs. Since then (or not used there):

* LP4's right-swallow statement is a theorem (`LP.lp4RightSwallowStatement`, PROVE-LP18), so LP4's avoid step needs
  only Zhan's stopping collar (`LP.lp4AvoidStatement_of_collar`): the input `hRS` is gone;
* the trial bounds (`hmid`, `hlow`, `h8T`) follow from their critical-case remainders
  (`Sec7.TrialsHi3.highTrialMidStatement_of_crit`, `highTrialLowStatement_of_crit`, `lp8TrialStatement_of_crit`,
  PROVE-TRIALS-HI3): the inputs become `Sec7.TrialsHi3.LowCritStatement κ lo` and `LP8CritStatement κ`;
* Theorem 1.3 uses Lemma 7.1 only through its mapped segment and the trace reference of Proposition 7.3, and both follow
  from the chart-form pocket statement `Sec7.Lemma71C.Lemma71PocketChartStatement`
  (`lemma71MappedSegmentStatement_of_pocketChart`, `lemma71TraceReferenceStatement_of_pocketChart`, PROVE-LEMMA71C).
  The pathwise pocket statement implies it (`Lemma71E` → `Lemma71CTop`), and so does PROVE-LEMMA72's joint statement
  (`Sec7.Lemma72.lemma71PocketChartStatement_of_joint`), so the input `hP` is replaced by the weaker `hPC`.

**Eight named inputs remain** (`ae_exists_isGeneratingTrace_of_open3`): `hPC`, `hmid`, `hlow`, `h8`, `hhit`, `hR7`,
`hPW`, `hcol`. Every replaced input implies its replacement through the landed reductions above, so nothing is
strengthened.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Wire

/-- **Proposition 7.3's trace from the chart-form pocket statement** (PROVE-LEMMA71C). -/
theorem prop73TraceStatement_of_pocketChart3 (hPC : Sec7.Lemma71C.Lemma71PocketChartStatement.{0}) :
    Sec7.Prop73TraceStatement.{u} :=
  Sec7.prop73TraceStatement_of_reference (Sec7.Lemma71C.lemma71TraceReferenceStatement_of_pocketChart hPC)

/-- **The seed one-force theorem for every `κ > 0`** (one right mark at `0⁺` of weight `> −2` gives a complete word),
from inputs that do not contain Aux. lemma 99 (conditional helper): PROVE-TRACECLOSE's `seedOneForce_of_remaining3`
with `hP` weakened to `hPC` and `hRS` proved. -/
theorem seedOneForce_of_open3 (hPC : Sec7.Lemma71C.Lemma71PocketChartStatement.{0})
    (hhit : WangWu.Theorem18.TwoSeedHittingStatement.{u} 4) (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (hcol : ∀ κ : ℝ, 4 < κ → ZhanGT4.StoppingCollarStatement.{u} κ)
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ (xL ρL : Fin 0 → ℝ) (ρR : Fin 1 → ℝ), -2 < ρR 0 → LP.IsCompleteForceWord.{u} κ xL (fun _ => 0) ρL ρR := by
  rcases lt_trichotomy κ 4 with h4 | rfl | h4
  · intro xL ρL ρR hρ
    exact Sec7.isCompleteForceWord_seedRight_of_prop73Trace (prop73TraceStatement_of_pocketChart3.{0} hPC) hκ h4 xL
      (fun _ => 0) ρL ρR (fun _ => rfl) fun i => by rw [Fin.fin_one_eq_zero i]; exact hρ
  · exact LP.seedOneForce_of_twoSeedComplete hκ
      (WangWu.Theorem18.twoSeedComplete_of_hitting (by norm_num) le_rfl hhit)
  · exact LP.seedOneForce_of_twoSeedComplete hκ (twoSeedComplete_of_remainingB hR7
      (Sec7.Lemma725Ref.lemma725DriverReferenceStatement_of_pocketWordEvolution hPW)
      (LP.lp4AvoidStatement_of_collar hcol) h4)

/-- **Aux. lemma 99 stopped for every `κ > 0`** from the seed one-force theorem (conditional helper). -/
theorem aux99StoppedStatement_of_open3 (hPC : Sec7.Lemma71C.Lemma71PocketChartStatement.{0})
    (hhit : WangWu.Theorem18.TwoSeedHittingStatement.{u} 4) (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (hcol : ∀ κ : ℝ, 4 < κ → ZhanGT4.StoppingCollarStatement.{u} κ)
    {κ : ℝ} (hκ : 0 < κ) : Sec7.Aux99StoppedStatement.{u} κ :=
  Sec7.aux99StoppedStatement_of_seed hκ (seedOneForce_of_open3 hPC hhit hR7 hPW hcol hκ)

/-- **Wang–Wu's Theorem 1.8 (`κ = 4`)** from the boundary-hitting two-seed words, Aux. lemma 99 stopped (from the seed
theorem), the low-sector critical remainder at `κ = 4` and LP9's prefix (proved). -/
theorem wwTheorem18DistinctStatement_of_open3 (hPC : Sec7.Lemma71C.Lemma71PocketChartStatement.{0})
    (hhit : WangWu.Theorem18.TwoSeedHittingStatement.{u} 4) (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (hcol : ∀ κ : ℝ, 4 < κ → ZhanGT4.StoppingCollarStatement.{u} κ)
    (hlow4 : Sec7.TrialsHi3.LowCritStatement.{u} 4 (4 / 2 - 4)) :
    LP.WWTheorem18DistinctStatement.{u} :=
  Sec7.TrialsHi2.wwTheorem18DistinctStatement_of_low
    (WangWu.Theorem18.twoSeedComplete_of_hitting (by norm_num) le_rfl hhit)
    (WangWu.Lemma51.oneRightNonAdmissibleStatement_of_stopped
      (aux99StoppedStatement_of_open3 hPC hhit hR7 hPW hcol (by norm_num)))
    (Sec7.TrialsHi3.highTrialLowStatement_of_crit (by norm_num) hlow4) (Sec7.lp9PrefixStatement (by norm_num))

/-- **Theorem 1.3 (continuity and endpoint)**, with exactly the conclusion of the frozen
`IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace`, in the provider shape (all of the anchor's arguments implicit,
its hypotheses `ha`, `hF`, `hE` auto-parameters), from the **eight open** named inputs (conditional helper; it is not
the provider):

* `hPC` — Lemma 7.1's chart-form pocket statement (`κ < 4`);
* `hmid` — the low-sector critical remainder with both totals `> −2`, `0 < κ < 4`;
* `hlow` — the low-sector critical remainder with both totals `> κ/2 − 4`, `κ ≥ 4`;
* `h8` — LP8's critical remainder (left total `≥ κ/2 − 2`), `κ > 4`;
* `hhit` — the boundary-hitting two-seed words at `κ = 4`;
* `hR7` — Theorem R.7's reference (`κ > 4`);
* `hPW` — the pocket word evolutions of Lemma 7.25 (`κ > 4`, both weights below `κ/2 − 4`);
* `hcol` — Zhan's stopping collar, `κ > 4`. -/
theorem ae_exists_isGeneratingTrace_of_open3
    (hPC : Sec7.Lemma71C.Lemma71PocketChartStatement.{0})
    (hmid : ∀ κ : ℝ, 0 < κ → κ < 4 → Sec7.TrialsHi3.LowCritStatement.{u} κ (-2))
    (hlow : ∀ κ : ℝ, 4 ≤ κ → Sec7.TrialsHi3.LowCritStatement.{u} κ (κ / 2 - 4))
    (h8 : ∀ κ : ℝ, 4 < κ → Sec7.TrialsHi3.LP8CritStatement.{u} κ)
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
  ae_exists_isGeneratingTrace_of_remainingB (Sec7.Lemma71C.lemma71MappedSegmentStatement_of_pocketChart hPC)
    (fun κ hκ _ => aux99StoppedStatement_of_open3 hPC hhit hR7 hPW hcol hκ) Sec7.aux102BandStatement
    (Sec7.TrialsHi3.aux113TransienceStatement_of_crit (prop73TraceStatement_of_pocketChart3 hPC) hmid)
    Sec7.oneSidedPrefixStatement
    (wwTheorem18DistinctStatement_of_open3 hPC hhit hR7 hPW hcol (hlow 4 le_rfl))
    (fun κ hκ => aux99StoppedStatement_of_open3 hPC hhit hR7 hPW hcol (by linarith))
    (fun κ hκ => Sec7.TrialsHi3.lpAux113TransienceStatement_of_crit (by linarith) (hlow κ hκ.le))
    (fun κ hκ => Sec7.TrialsHi3.lp8TransienceStatement_of_crit (by linarith) (h8 κ hκ))
    (fun κ hκ => Sec7.lp9PrefixStatement (by linarith)) hR7
    (Sec7.Lemma725Ref.lemma725DriverReferenceStatement_of_pocketWordEvolution hPW)
    (LP.lp4AvoidStatement_of_collar hcol) ha hF hE

/-- **Theorem 1.3 as the named form `Exist.Theorem13Statement`** (the frozen anchor's type), from the same eight open
inputs (conditional helper; for the consumers of the frozen type: the flow-line companion, the staged histories). -/
theorem theorem13Statement_of_open3
    (hPC : Sec7.Lemma71C.Lemma71PocketChartStatement.{0})
    (hmid : ∀ κ : ℝ, 0 < κ → κ < 4 → Sec7.TrialsHi3.LowCritStatement.{u} κ (-2))
    (hlow : ∀ κ : ℝ, 4 ≤ κ → Sec7.TrialsHi3.LowCritStatement.{u} κ (κ / 2 - 4))
    (h8 : ∀ κ : ℝ, 4 < κ → Sec7.TrialsHi3.LP8CritStatement.{u} κ)
    (hhit : WangWu.Theorem18.TwoSeedHittingStatement.{u} 4)
    (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (hcol : ∀ κ : ℝ, 4 < κ → ZhanGT4.StoppingCollarStatement.{u} κ) :
    Exist.Theorem13Statement.{u} := by
  intro _ ha _ _ _ _ _ _ hF _ _ _ _ _ _ _ _ _ _ hE
  exact ae_exists_isGeneratingTrace_of_open3 hPC hmid hlow h8 hhit hR7 hPW hcol ha hF hE

end Wire

end InteractingSLE
