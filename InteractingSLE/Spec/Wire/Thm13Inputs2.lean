/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Theorem13B
import InteractingSLE.Spec.Sec7.ContinuityProb7Aux102
import InteractingSLE.Spec.Sec7.TrialsHi2Assembly
import InteractingSLE.Spec.Sec7.Lemma71ETop
import InteractingSLE.Spec.Sec7.Lemma71BTop
import InteractingSLE.Spec.Sec7.TraceCodingUse
import InteractingSLE.Spec.Sec7.Lemma725Ref
import InteractingSLE.Spec.Supplement.LP4HalfBallStraddle
import InteractingSLE.Spec.Supplement.LP4AvoidHalfBall
import InteractingSLE.WangWu.Theorem18
import InteractingSLE.WangWu.Continuity2OneForce

/-!
# Theorem 1.3 with the results landed since PROVE-FLOWEXIST plugged in

Packet PROVE-WIRE2 (no new mathematics). PROVE-FLOWEXIST left Theorem 1.3
(`Wire.ae_exists_isGeneratingTrace_of_remainingB`) with thirteen named inputs. Since then:

* Aux. lemma 102 is a theorem (`Sec7.aux102BandStatement`, PROVE-SEC7-C7);
* Lemma 7.1's mapped segment and its trace reference follow from the pathwise pocket statement
  `Sec7.Lemma71E.Lemma71PocketStatement` (PROVE-LEMMA71E), and Proposition 7.3's trace from that reference
  (`Sec7.prop73TraceStatement_of_reference`);
* Aux. lemma 113's transience (`κ < 4`) follows from Proposition 7.3's trace and the mid-sector trial bound
  (`Sec7.TrialsHi2.aux113TransienceStatement_of_mid`); its `κ > 4` form from the low-sector trial bound
  (`lpAux113TransienceStatement_of_low`); LP8's transience from LP8's trial bound (`lp8TransienceStatement_of_trial`)
  (PROVE-TRIALS-HI2);
* Wang–Wu's Theorem 1.8 (`κ = 4`) follows from the two-seed premise, the one-right non-admissible statement, the
  low-sector trial bound and LP9's prefix (`wwTheorem18DistinctStatement_of_low`); the two-seed premise at `κ = 4` from
  its boundary-hitting weights (`WangWu.Theorem18.twoSeedComplete_of_hitting`), the non-admissible statement from
  Aux. lemma 99 stopped (`WangWu.Lemma51.oneRightNonAdmissibleStatement_of_stopped`);
* LP4's avoid step follows from Zhan's stopping collar and one right-swallow statement
  (`LP.lp4HalfBallStatement_of_rightSwallow`, PROVE-LP17; `LP.lp4AvoidStatement_of_halfBall`, PROVE-LP16);
* the driving part of Lemma 7.25's reference follows from the pocket word evolutions
  (`Sec7.Lemma725Ref.lemma725DriverReferenceStatement_of_pocketWordEvolution`, PROVE-AUX119-130).

The three copies of Aux. lemma 99 stopped (`κ < 4`, `κ = 4`, `κ > 4`) become one input for every `κ > 0`, and the
low-sector trial bound and LP9's prefix become one input each for `κ ≥ 4`. **Twelve named inputs remain**
(`ae_exists_isGeneratingTrace_of_remaining2`). Every replaced input is implied by its replacements through the landed
reductions above, so nothing is strengthened.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Wire

/-- **Lemma 7.1's mapped segment from the pathwise pocket statement** (PROVE-LEMMA71E with PROVE-LEMMA71B). -/
theorem lemma71MappedSegmentStatement_of_pocket2 (hP : Sec7.Lemma71E.Lemma71PocketStatement.{0}) :
    Sec7.Lemma71.Lemma71MappedSegmentStatement.{0} :=
  Sec7.Lemma71B.lemma71MappedSegmentStatement_of_killed (Sec7.Lemma71E.lemma71KilledSegmentStatement_of_pocket hP)

/-- **Proposition 7.3's trace from the pathwise pocket statement.** -/
theorem prop73TraceStatement_of_pocket2 (hP : Sec7.Lemma71E.Lemma71PocketStatement.{0}) :
    Sec7.Prop73TraceStatement.{u} :=
  Sec7.prop73TraceStatement_of_reference (Sec7.Lemma71E.lemma71TraceReferenceStatement_of_pocket hP)

/-- **Aux. lemma 113's transience (`κ < 4`)** from the pathwise pocket statement and the mid-sector trial bound. -/
theorem aux113TransienceStatement_of_pocket_mid2 (hP : Sec7.Lemma71E.Lemma71PocketStatement.{0})
    (hmid : ∀ κ : ℝ, 0 < κ → κ < 4 → Sec7.TrialsHi2.HighTrialMidStatement.{u} κ) :
    Sec7.Aux113TransienceStatement.{u} :=
  Sec7.TrialsHi2.aux113TransienceStatement_of_mid (prop73TraceStatement_of_pocket2 hP) hmid

/-- **Wang–Wu's Theorem 1.8 (`κ = 4`)** from the boundary-hitting two-seed words, Aux. lemma 99 stopped, the
low-sector trial bound and LP9's prefix, all at `κ = 4`. -/
theorem wwTheorem18DistinctStatement_of_remaining2
    (hhit : WangWu.Theorem18.TwoSeedHittingStatement.{u} 4) (h99 : Sec7.Aux99StoppedStatement.{u} 4)
    (hlow : Sec7.TrialsHi.HighTrialLowStatement.{u} 4) (h9 : Sec7.LP9PrefixStatement.{u} 4) :
    LP.WWTheorem18DistinctStatement.{u} :=
  Sec7.TrialsHi2.wwTheorem18DistinctStatement_of_low
    (WangWu.Theorem18.twoSeedComplete_of_hitting (by norm_num) le_rfl hhit)
    (WangWu.Lemma51.oneRightNonAdmissibleStatement_of_stopped h99) hlow h9

/-- **LP4's avoid step** from Zhan's stopping collar (`κ > 4`) and LP4's right-swallow statement. -/
theorem lp4AvoidStatement_of_remaining2 (hcol : ∀ κ : ℝ, 4 < κ → ZhanGT4.StoppingCollarStatement.{u} κ)
    (hRS : LP.LP4RightSwallowStatement.{u}) : LP.LP4AvoidStatement.{u} :=
  LP.lp4AvoidStatement_of_halfBall (LP.lp4HalfBallStatement_of_rightSwallow hcol hRS)

/-- **Theorem 1.3 (continuity and endpoint)**, with exactly the conclusion of the frozen
`IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace`, in the provider shape (all of the anchor's arguments implicit,
its hypotheses `ha`, `hF`, `hE` auto-parameters), from the **twelve remaining** named inputs (conditional helper; it is
not the provider):

* `hP` — Lemma 7.1's pathwise pocket statement (`κ < 4`);
* `h99` — Aux. lemma 99 stopped, every `κ > 0`;
* `hmid` — the mid-sector trial bound, `0 < κ < 4`;
* `h1s` — the prefix of the one-sided step (`κ < 4`);
* `hhit` — the boundary-hitting two-seed words at `κ = 4`;
* `hlow` — the low-sector trial bound, `κ ≥ 4`;
* `h9` — LP9's prefix, `κ ≥ 4`;
* `h8T` — LP8's trial bound, `κ > 4`;
* `hR7` — Theorem R.7's reference (`κ > 4`);
* `hPW` — the pocket word evolutions of Lemma 7.25 (`κ > 4`, both weights below `κ/2 − 4`);
* `hcol` — Zhan's stopping collar, `κ > 4`;
* `hRS` — LP4's right-swallow statement. -/
theorem ae_exists_isGeneratingTrace_of_remaining2
    (hP : Sec7.Lemma71E.Lemma71PocketStatement.{0})
    (h99 : ∀ κ : ℝ, 0 < κ → Sec7.Aux99StoppedStatement.{u} κ)
    (hmid : ∀ κ : ℝ, 0 < κ → κ < 4 → Sec7.TrialsHi2.HighTrialMidStatement.{u} κ)
    (h1s : Sec7.OneSidedPrefixStatement.{u})
    (hhit : WangWu.Theorem18.TwoSeedHittingStatement.{u} 4)
    (hlow : ∀ κ : ℝ, 4 ≤ κ → Sec7.TrialsHi.HighTrialLowStatement.{u} κ)
    (h9 : ∀ κ : ℝ, 4 ≤ κ → Sec7.LP9PrefixStatement.{u} κ)
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
  ae_exists_isGeneratingTrace_of_remainingB (lemma71MappedSegmentStatement_of_pocket2 hP)
    (fun κ hκ _ => h99 κ hκ) Sec7.aux102BandStatement (aux113TransienceStatement_of_pocket_mid2 hP hmid) h1s
    (wwTheorem18DistinctStatement_of_remaining2 hhit (h99 4 (by norm_num)) (hlow 4 le_rfl) (h9 4 le_rfl))
    (fun κ hκ => h99 κ (by linarith))
    (fun κ hκ => Sec7.TrialsHi2.lpAux113TransienceStatement_of_low (by linarith) (hlow κ hκ.le))
    (fun κ hκ => Sec7.TrialsHi2.lp8TransienceStatement_of_trial (by linarith) (h8T κ hκ))
    (fun κ hκ => h9 κ hκ.le) hR7
    (Sec7.Lemma725Ref.lemma725DriverReferenceStatement_of_pocketWordEvolution hPW)
    (lp4AvoidStatement_of_remaining2 hcol hRS) ha hF hE

end Wire

end InteractingSLE
