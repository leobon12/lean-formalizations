/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.TrialsHi2Clock
import InteractingSLE.Spec.Sec7.TrialsHi2Inner
import InteractingSLE.Spec.Sec7.ContinuityProb7Inputs

/-!
# The trial route with Aux. lemma 101 and the inner-reference positivity discharged

Packet PROVE-TRIALS-HI2. With `aux101BandClockStatement` (Aux. lemma 101 for the bands) and
`innerRefPositivityStatement` (Aux. lemma 111's inner references) proved for every `κ > 0`, PROVE-TRIALS-HI's target
statements need only the remaining trial inputs:

* `WangWu.LowSide.LPAux113HighTransienceStatement κ` (and Aux. lemma 113's transience `Sec7.LPAux113TransienceStatement
  κ`) from `TrialsHi.HighTrialLowStatement κ` alone (`lpAux113HighTransienceStatement_of_low`,
  `lpAux113TransienceStatement_of_low`); at `κ = 4` this is Theorem 1.3's input #4 of PROVE-WW-C2
  (`lpAux113HighTransienceStatement_four`, and `wwTheorem18DistinctStatement_of_low` for Wang–Wu's Theorem 1.8);
* `WangWu.LowSide.Aux113HighTransienceStatement` (the `κ < 4` form) from `HighTrialLowStatement κ` for `0 < κ < 4`
  (`aux113HighTransienceStatement_of_low`);
* `LP.LP8TransienceStatement κ` from `TrialsHi.LP8TrialStatement κ` alone (`lp8TransienceStatement_of_trial`).

For `0 < κ < 4` the remainder is narrowed further (orchestrator scope addition): a side total `≤ −2` is handled by the
landed low-side completeness (`WangWu.LowSide.isCompleteForceWord_of_lowSide`, with the two-seed premise from
`Prop73TraceStatement`), so only words with both totals `> −2` and one total in `(−2, κ/2 − 2]` need a trial bound
(`HighTrialMidStatement`); `aux113HighTransienceStatement_of_mid` and `aux113TransienceStatement_of_mid` (Theorem 1.3's
input #6) follow. The outer references of `TrialsHi.uniformTrialBound_outer` do not cover that range: with an outer
weight `s < κ/2 − 2` the outer mark is swallowed almost surely, so their success event (`RefGood`, infinite lifetime
with the nearest marks never hit) is null (see the handoff).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace TrialsHi2

open TrialsHi

/-- **The third-sector trial bound from the low-total remainder alone** (every `κ > 0`). -/
theorem highTrialStatement_of_low {κ : ℝ} (hκ : 0 < κ) (hlow : HighTrialLowStatement.{u} κ) :
    HighTrialStatement.{u} κ :=
  highTrialStatement_of_ref hκ (innerRefPositivityStatement hκ) hlow

/-- **`WangWu.LowSide.LPAux113HighTransienceStatement κ` from the low-total remainder alone** (every `κ > 0`). -/
theorem lpAux113HighTransienceStatement_of_low {κ : ℝ} (hκ : 0 < κ) (hlow : HighTrialLowStatement.{u} κ) :
    WangWu.LowSide.LPAux113HighTransienceStatement.{u} κ :=
  lpAux113HighTransienceStatement_of_ref hκ (aux101BandClockStatement hκ) (innerRefPositivityStatement hκ) hlow

/-- **Aux. lemma 113's transience `Sec7.LPAux113TransienceStatement κ` from the low-total remainder alone** (every
`κ > 0`; Aux. lemma 102 is PROVE-SEC7-C7's landed `aux102BandStatement`). -/
theorem lpAux113TransienceStatement_of_low {κ : ℝ} (hκ : 0 < κ) (hlow : HighTrialLowStatement.{u} κ) :
    LPAux113TransienceStatement.{u} κ :=
  C7.lpAux113TransienceStatement_of_high hκ (lpAux113HighTransienceStatement_of_low hκ hlow)

/-- **Theorem 1.3's input #4 at `κ = 4`** (PROVE-WW-C2) from the low-total remainder at `κ = 4` (side totals in
`(−2, 0]`). -/
theorem lpAux113HighTransienceStatement_four (hlow : HighTrialLowStatement.{u} 4) :
    WangWu.LowSide.LPAux113HighTransienceStatement.{u} 4 :=
  lpAux113HighTransienceStatement_of_low (by norm_num) hlow

/-- **Wang–Wu's Theorem 1.8 (distinct words) at `κ = 4`** with the third sector reduced to the low-total remainder. -/
theorem wwTheorem18DistinctStatement_of_low (h2 : LP.TwoSeedComplete.{u} 4)
    (hna : WangWu.Lemma51.OneRightNonAdmissibleStatement.{u} 4) (hlow : HighTrialLowStatement.{u} 4)
    (h9 : LP9PrefixStatement.{u} 4) : LP.WWTheorem18DistinctStatement.{u} :=
  C7.wwTheorem18DistinctStatement_of_high h2 hna (lpAux113HighTransienceStatement_four hlow) h9

/-- **`WangWu.LowSide.Aux113HighTransienceStatement` (the `κ < 4` form) from the low-total remainder for
`0 < κ < 4`.** -/
theorem aux113HighTransienceStatement_of_low
    (hlow : ∀ κ : ℝ, 0 < κ → κ < 4 → HighTrialLowStatement.{u} κ) :
    WangWu.LowSide.Aux113HighTransienceStatement.{u} :=
  aux113HighTransienceStatement_of_ref (fun _ hκ _ => aux101BandClockStatement hκ)
    (fun _ hκ _ => innerRefPositivityStatement hκ) hlow

/-- **`LP.LP8TransienceStatement κ` from the trial bound of LP8's strengthened singleton experiment alone** (every
`κ > 0`). -/
theorem lp8TransienceStatement_of_trial {κ : ℝ} (hκ : 0 < κ) (hT : LP8TrialStatement.{u} κ) :
    LP.LP8TransienceStatement.{u} κ :=
  lp8TransienceStatement_of_trials hκ (aux101BandClockStatement hκ) hT

/-! ### `κ < 4`: only side totals in `(−2, κ/2 − 2]` remain -/

/-- **Named input (narrowed, for `κ < 4`): the uniform trial bound when both side totals exceed `−2` and one of them
is at most `κ/2 − 2`** (the part of `HighTrialLowStatement` that Aux. lemma 113's `κ < 4` consumer uses). -/
def HighTrialMidStatement (κ : ℝ) : Prop :=
  ∀ N : ℕ, 3 ≤ N → LP.DistinctCompleteBelow.{u} κ N →
    ∀ {nL nR : ℕ} (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ), nL + 1 + (nR + 1) = N →
      (-2 < ∑ i, ρL i ∧ -2 < ∑ i, ρR i) → ((∑ i, ρL i) ≤ κ / 2 - 2 ∨ (∑ i, ρR i) ≤ κ / 2 - 2) →
      UniformTrialBound κ ρL ρR

/-- For `κ < 4` the narrowed input is a special case of the low-total remainder. -/
theorem highTrialMidStatement_of_low {κ : ℝ} (hκ4 : κ < 4) (h : HighTrialLowStatement.{u} κ) :
    HighTrialMidStatement.{u} κ := fun N hN hD _ _ ρL ρR hc hs hlow =>
  h N hN hD ρL ρR hc ⟨by linarith [hs.1], by linarith [hs.2]⟩ hlow

/-- **The trial bound for one word with both side totals `> −2`**: from the inner-reference positivity if both exceed
`κ/2 − 2`, from the narrowed input otherwise. -/
theorem uniformTrialBound_of_mid {κ : ℝ} (hκ : 0 < κ) (hmid : HighTrialMidStatement.{u} κ) {N : ℕ} (hN : 3 ≤ N)
    (hD : LP.DistinctCompleteBelow.{u} κ N) {nL nR : ℕ} (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ)
    (hc : nL + 1 + (nR + 1) = N) (hs : -2 < ∑ i, ρL i ∧ -2 < ∑ i, ρR i) : UniformTrialBound κ ρL ρR := by
  by_cases hhigh : κ / 2 - 2 < ∑ i, ρL i ∧ κ / 2 - 2 < ∑ i, ρR i
  · have hD3 : LP.DistinctCompleteBelow.{u} κ 3 := fun xL xR ρL ρR hd hlt => hD xL xR ρL ρR hd (by omega)
    exact uniformTrialBound_inner hκ fun M hM => innerRefPositivityStatement hκ hD3 _ _ hhigh.1 hhigh.2 M hM
  · rw [not_and_or, not_lt, not_lt] at hhigh
    exact hmid N hN hD ρL ρR hc hs hhigh

/-- **`WangWu.LowSide.Aux113HighTransienceStatement` (Aux. lemma 113's third sector, `κ < 4`) from Proposition 7.3's
named statement and the narrowed trial input.** Words with a side total `≤ −2` are complete by the landed low-side
argument (Aux. lemma 102 and the two-seed premise); words with both totals `> −2` are transient by the trials. -/
theorem aux113HighTransienceStatement_of_mid (h73 : Prop73TraceStatement.{u})
    (hmid : ∀ κ : ℝ, 0 < κ → κ < 4 → HighTrialMidStatement.{u} κ) :
    WangWu.LowSide.Aux113HighTransienceStatement.{u} := by
  intro κ hκ hκ4 N hN hbelow nL nR xL xR ρL ρR hd hc hL hR _ Ω mΩ P _ 𝓕 W VL VR B ζ hE
  have hD : LP.DistinctCompleteBelow.{u} κ N := distinctCompleteBelow_of_le (by omega) hbelow
  obtain ⟨m, rfl⟩ : ∃ m, nL = m + 1 := ⟨nL - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, nR = k + 1 := ⟨nR - 1, by omega⟩
  by_cases hlow : (∑ i, ρL i) ≤ -2 ∨ (∑ j, ρR j) ≤ -2
  · have hcw : LP.IsCompleteForceWord.{u} κ xL xR ρL ρR :=
      WangWu.LowSide.isCompleteForceWord_of_lowSide hκ aux102BandStatement hD
        (twoSeedComplete_of_prop73 h73 hκ hκ4) hd.1 (by omega) (by omega) hlow
    filter_upwards [hcw P 𝓕 W VL VR B ζ hE, hE.2.2.2.2] with ω ⟨η₀, hη₀, htr₀⟩ hp hζ _ η hη
    rw [hζ] at hη₀ hp
    have hwc : ContinuousOn (fun t => W t ω) {s | (s : ℝ≥0∞) < ⊤} := hp.2.2.2.1
    refine (htr₀ hζ).congr fun t => ?_
    rw [hη₀.eq_of_le hη hwc hp.1 le_top]
  · rw [not_or, not_le, not_le] at hlow
    filter_upwards [ae_tendsto_of_trialBound hκ hD (aux101BandClockStatement hκ) (by omega) (by omega)
      (uniformTrialBound_of_mid hκ (hmid κ hκ hκ4) hN hD ρL ρR hc hlow) hd.1 hE] with ω h hζ _ η hη
    exact h hζ η hη

/-- **Aux. lemma 113's transience for `κ < 4` (`Sec7.Aux113TransienceStatement`, Theorem 1.3's input #6)** from
Proposition 7.3's named statement and the narrowed trial input (Aux. lemmas 101 and 102 and the inner references
discharged). -/
theorem aux113TransienceStatement_of_mid (h73 : Prop73TraceStatement.{u})
    (hmid : ∀ κ : ℝ, 0 < κ → κ < 4 → HighTrialMidStatement.{u} κ) : Aux113TransienceStatement.{u} :=
  C7.aux113TransienceStatement_of_high h73 (aux113HighTransienceStatement_of_mid h73 hmid)

/-! ### Lemma LP8's sector is empty for `κ ≤ 4` -/

/-- For `κ ≤ 4` no weight lies in `(−2, κ/2 − 4]`, so LP8's trial statement holds vacuously. -/
theorem lp8TrialStatement_of_le_four {κ : ℝ} (hκ4 : κ ≤ 4) : LP8TrialStatement.{u} κ :=
  fun _ _ _ _ _ _ _ hr hrd _ => absurd (hr.trans_le hrd) (by linarith)

/-- **`LP.LP8TransienceStatement κ` for `0 < κ ≤ 4`** (the sector is empty). -/
theorem lp8TransienceStatement_of_le_four {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) : LP.LP8TransienceStatement.{u} κ :=
  lp8TransienceStatement_of_trial hκ (lp8TrialStatement_of_le_four hκ4)

end TrialsHi2

end Sec7

end InteractingSLE
