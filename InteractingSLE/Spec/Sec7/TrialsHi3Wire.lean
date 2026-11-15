/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.TrialsHi3Assembly

/-!
# The low-sector trial statements, reduced to the critical and singleton words

Packet PROVE-TRIALS-HI3. With the whole-side swallow (`uniformTrialBound_swallowR`, `uniformTrialBound_swallowL`) the
three trial statements of PROVE-TRIALS-HI2 are reduced to the words of the low sector in which **no side with at
least two marks has its total in `(κ/2 − 4, κ/2 − 2)`**: every such side total is at least `κ/2 − 2`, and a side
total below `κ/2 − 2` belongs to a single mark. On these words no whole side can be swallowed (a side total
`≥ κ/2 − 2` is never swallowed; swallowing a singleton merges nothing), so their trial success must be transience,
the source's "Both totals are at least `c`" (critical total `= c`) and "A sole right mark is allowed to continue"
cases of Aux. lemma 111. They are the named remainders

* `LowCritStatement κ lo` (both totals `> lo`, one `≤ κ/2 − 2`, every side with two marks or more at least
  `κ/2 − 2`);
* `LP8CritStatement κ` (Lemma LP8's sector with the left total at least `κ/2 − 2`).

## Main results

* `highTrialLowStatement_of_crit`, `highTrialMidStatement_of_crit`, `lp8TrialStatement_of_crit`;
* the consumers: `lpAux113HighTransienceStatement_of_crit`, `lpAux113TransienceStatement_of_crit`,
  `lpAux113HighTransienceStatement_four_of_crit` (Theorem 1.3's input #4 at `κ = 4`),
  `aux113TransienceStatement_of_crit` (T13 #6, `κ < 4`), `lp8TransienceStatement_of_crit`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace TrialsHi3

/-! ### The named remainders -/

/-- **Named remainder: the critical and singleton words of the low sector** (Specification p. 364–366, Aux. lemma
111, "Both totals are at least `c`" at the critical total `c = κ/2 − 2`, and "A sole right mark is allowed to
continue"): for `N ≥ 3` under the smaller-count hypothesis, the weights of a word with `N` marks whose side totals
exceed `lo`, one of them at most `κ/2 − 2`, and in which every side with at least two marks has total at least
`κ/2 − 2`, have the uniform trial bound. -/
def LowCritStatement (κ lo : ℝ) : Prop :=
  ∀ N : ℕ, 3 ≤ N → LP.DistinctCompleteBelow.{u} κ N →
    ∀ {nL nR : ℕ} (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ), nL + 1 + (nR + 1) = N →
      (lo < ∑ i, ρL i ∧ lo < ∑ i, ρR i) → ((∑ i, ρL i) ≤ κ / 2 - 2 ∨ (∑ i, ρR i) ≤ κ / 2 - 2) →
      (nL = 0 ∨ κ / 2 - 2 ≤ ∑ i, ρL i) → (nR = 0 ∨ κ / 2 - 2 ≤ ∑ i, ρR i) →
      TrialsHi.UniformTrialBound κ ρL ρR

/-- **Named remainder: Lemma LP8's strengthened singleton experiment with a high left total** (supplement p. 485;
Aux. lemma 111, "If `s_L ≥ c`, use the reference with weights `s_L, s_R` at `−1, 1`"): for `N ≥ 3` under the
smaller-count hypothesis, weights with `N − 1` left marks of total at least `κ/2 − 2` and one right mark of weight
in `(−2, κ/2 − 4]` have the uniform trial bound. -/
def LP8CritStatement (κ : ℝ) : Prop :=
  ∀ N : ℕ, 3 ≤ N → LP.DistinctCompleteBelow.{u} κ N →
    ∀ {nL : ℕ} (ρL : Fin (nL + 1) → ℝ) (ρR : Fin 1 → ℝ), nL + 1 + 1 = N → -2 < ρR 0 → ρR 0 ≤ κ / 2 - 4 →
      κ / 2 - 2 ≤ ∑ i, ρL i → TrialsHi.UniformTrialBound κ ρL ρR

/-! ### The reductions -/

/-- The case split: a side with at least two marks and total in `(d, c)` is swallowed; otherwise the word is in the
remainder. -/
theorem uniformTrialBound_of_crit {κ : ℝ} (hκ : 0 < κ) {lo : ℝ} (hlo : κ / 2 - 4 ≤ lo)
    (h : LowCritStatement.{u} κ lo) {N : ℕ} (hN : 3 ≤ N) (hD : LP.DistinctCompleteBelow.{u} κ N) {nL nR : ℕ}
    (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (hc : nL + 1 + (nR + 1) = N)
    (hs : lo < ∑ i, ρL i ∧ lo < ∑ i, ρR i) (hlow : (∑ i, ρL i) ≤ κ / 2 - 2 ∨ (∑ i, ρR i) ≤ κ / 2 - 2) :
    TrialsHi.UniformTrialBound κ ρL ρR := by
  by_cases hR : 0 < nR ∧ ∑ j, ρR j < κ / 2 - 2
  · exact uniformTrialBound_swallowR hκ hD hc.le hR.1 (by linarith [hs.2]) hR.2
  by_cases hL : 0 < nL ∧ ∑ i, ρL i < κ / 2 - 2
  · exact uniformTrialBound_swallowL hκ hD hc.le hL.1 (by linarith [hs.1]) hL.2
  refine h N hN hD ρL ρR hc hs hlow ?_ ?_
  · rcases Nat.eq_zero_or_pos nL with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (not_lt.1 fun h' => hL ⟨h0, h'⟩)
  · rcases Nat.eq_zero_or_pos nR with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (not_lt.1 fun h' => hR ⟨h0, h'⟩)

/-- **`HighTrialLowStatement κ` from the critical and singleton remainder** (every `κ > 0`). -/
theorem highTrialLowStatement_of_crit {κ : ℝ} (hκ : 0 < κ) (h : LowCritStatement.{u} κ (κ / 2 - 4)) :
    TrialsHi.HighTrialLowStatement.{u} κ := fun _ hN hD _ _ ρL ρR hc hs hlow =>
  uniformTrialBound_of_crit hκ le_rfl h hN hD ρL ρR hc hs hlow

/-- **`HighTrialMidStatement κ` (`0 < κ < 4`) from the remainder with both totals `> −2`.** -/
theorem highTrialMidStatement_of_crit {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (h : LowCritStatement.{u} κ (-2)) :
    TrialsHi2.HighTrialMidStatement.{u} κ := fun _ hN hD _ _ ρL ρR hc hs hlow =>
  uniformTrialBound_of_crit hκ (by linarith) h hN hD ρL ρR hc hs hlow

/-- **`LP8TrialStatement κ` from its high-left remainder** (a left total in `(κ/2 − 4, κ/2 − 2)` is swallowed). -/
theorem lp8TrialStatement_of_crit {κ : ℝ} (hκ : 0 < κ) (h : LP8CritStatement.{u} κ) :
    TrialsHi.LP8TrialStatement.{u} κ := by
  intro N hN hD nL ρL ρR hc h1 h2 hsL
  by_cases hL : ∑ i, ρL i < κ / 2 - 2
  · exact uniformTrialBound_swallowL (nR := 0) hκ hD hc.le (by omega) hsL hL
  · exact h N hN hD ρL ρR hc h1 h2 (not_lt.1 hL)

/-! ### The consumers -/

/-- **`WangWu.LowSide.LPAux113HighTransienceStatement κ` from the remainder** (every `κ > 0`). -/
theorem lpAux113HighTransienceStatement_of_crit {κ : ℝ} (hκ : 0 < κ) (h : LowCritStatement.{u} κ (κ / 2 - 4)) :
    WangWu.LowSide.LPAux113HighTransienceStatement.{u} κ :=
  TrialsHi2.lpAux113HighTransienceStatement_of_low hκ (highTrialLowStatement_of_crit hκ h)

/-- **Aux. lemma 113's transience `Sec7.LPAux113TransienceStatement κ` (T13 #14 for `κ > 4`) from the remainder.** -/
theorem lpAux113TransienceStatement_of_crit {κ : ℝ} (hκ : 0 < κ) (h : LowCritStatement.{u} κ (κ / 2 - 4)) :
    LPAux113TransienceStatement.{u} κ :=
  TrialsHi2.lpAux113TransienceStatement_of_low hκ (highTrialLowStatement_of_crit hκ h)

/-- **Theorem 1.3's input #4 at `κ = 4`** from the remainder at `κ = 4` (side totals in `(−2, 0]`). -/
theorem lpAux113HighTransienceStatement_four_of_crit (h : LowCritStatement.{u} 4 (-2)) :
    WangWu.LowSide.LPAux113HighTransienceStatement.{u} 4 :=
  TrialsHi2.lpAux113HighTransienceStatement_four (highTrialLowStatement_of_crit (by norm_num)
    (by norm_num [show (4 : ℝ) / 2 - 4 = -2 by norm_num] at h ⊢; exact h))

/-- **Aux. lemma 113's transience for `0 < κ < 4` (T13 #6)** from Proposition 7.3 and the remainder. -/
theorem aux113TransienceStatement_of_crit (h73 : Prop73TraceStatement.{u})
    (h : ∀ κ : ℝ, 0 < κ → κ < 4 → LowCritStatement.{u} κ (-2)) : Aux113TransienceStatement.{u} :=
  TrialsHi2.aux113TransienceStatement_of_mid h73 fun κ hκ hκ4 =>
    highTrialMidStatement_of_crit hκ hκ4 (h κ hκ hκ4)

/-- **`LP.LP8TransienceStatement κ` from the high-left remainder.** -/
theorem lp8TransienceStatement_of_crit {κ : ℝ} (hκ : 0 < κ) (h : LP8CritStatement.{u} κ) :
    LP.LP8TransienceStatement.{u} κ :=
  TrialsHi2.lp8TransienceStatement_of_trial hκ (lp8TrialStatement_of_crit hκ h)

end TrialsHi3

end Sec7

end InteractingSLE
