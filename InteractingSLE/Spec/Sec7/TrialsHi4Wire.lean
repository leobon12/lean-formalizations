/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.TrialsHi4Compare
import InteractingSLE.Spec.Sec7.TrialsHi3Wire

/-!
# The critical and singleton trial statements, and the transience consumers

Packet PROVE-TRIALS-HI4. The two remainders of PROVE-TRIALS-HI3 are proved:

* `lowCritStatement` — `TrialsHi3.LowCritStatement κ lo` for every `κ > 0` and `lo ≥ −2` (Specification p. 364–366,
  Aux. lemma 111, "Both totals are at least `c`" including the critical total `c = κ/2 − 2`, and "A sole right mark
  is allowed to continue"): a word in which every side with two marks or more has total `≥ κ/2 − 2` either has both
  totals `≥ κ/2 − 2` (inner reference, `refTrialPositivity_of_ge`, `TrialsHi.uniformTrialBound_inner`), or has a
  singleton side of weight `> −2`, which is left unchanged by the comparison (`uniformTrialBound_singletonR` and its
  reflection);
* `lp8CritStatement` — `TrialsHi3.LP8CritStatement κ` for every `κ > 0` (Lemma LP8's sector with left total
  `≥ κ/2 − 2`).

Through PROVE-TRIALS-HI3's reductions this gives, unconditionally: `TrialsHi.HighTrialLowStatement κ` (`κ ≥ 4`),
`TrialsHi2.HighTrialMidStatement κ` (`0 < κ < 4`), `TrialsHi.LP8TrialStatement κ` (`κ > 0`), and the transience
consumers `WangWu.LowSide.LPAux113HighTransienceStatement κ` (`κ ≥ 4`; at `κ = 4` Theorem 1.3's input #4),
`Sec7.LPAux113TransienceStatement κ` (`κ ≥ 4`, T13 #14), `LP.LP8TransienceStatement κ` (`κ > 0`), and
`Sec7.Aux113TransienceStatement` (T13 #6) from `Prop73TraceStatement`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace TrialsHi4

variable {κ : ℝ}

/-- The smaller-count hypothesis at `N ≥ 3` gives it at `3`. -/
theorem distinctCompleteBelow_three {N : ℕ} (hN : 3 ≤ N) (hD : LP.DistinctCompleteBelow.{u} κ N) :
    LP.DistinctCompleteBelow.{u} κ 3 := fun xL xR ρL ρR hd hn => hD xL xR ρL ρR hd (lt_of_lt_of_le hn hN)

/-- **Both totals at least `κ/2 − 2`** (critical totals included): the uniform trial bound from the inner
reference. -/
theorem uniformTrialBound_ge (hκ : 0 < κ) (hD3 : LP.DistinctCompleteBelow.{u} κ 3) {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} (hL : κ / 2 - 2 ≤ ∑ i, ρL i) (hR : κ / 2 - 2 ≤ ∑ j, ρR j) :
    TrialsHi.UniformTrialBound κ ρL ρR :=
  TrialsHi.uniformTrialBound_inner hκ fun _ hM => refTrialPositivity_of_ge hκ hD3 hL hR hM

/-- **A left singleton of weight `> −2`, right total at least `κ/2 − 2`** (reflection of
`uniformTrialBound_singletonR`). -/
theorem uniformTrialBound_singletonL (hκ : 0 < κ) (hD3 : LP.DistinctCompleteBelow.{u} κ 3) {nR : ℕ}
    {ρL : Fin 1 → ℝ} {ρR : Fin (nR + 1) → ℝ} (hR : κ / 2 - 2 ≤ ∑ j, ρR j) (hL : -2 < ρL 0) :
    TrialsHi.UniformTrialBound κ ρL ρR :=
  TrialsHi3.uniformTrialBound_reflect hκ (uniformTrialBound_singletonR hκ hD3 hR hL)

/-- **`TrialsHi3.LowCritStatement κ lo` for every `κ > 0` and `lo ≥ −2`** (Aux. lemma 111, "Both totals are at
least `c`" and "A sole right mark is allowed to continue"). -/
theorem lowCritStatement (hκ : 0 < κ) {lo : ℝ} (hlo : -2 ≤ lo) : TrialsHi3.LowCritStatement.{u} κ lo := by
  intro N hN hD nL nR ρL ρR hc hs _ hL hR
  have hD3 : LP.DistinctCompleteBelow.{u} κ 3 := distinctCompleteBelow_three hN hD
  rcases hL with hL0 | hLc <;> rcases hR with hR0 | hRc
  · subst hL0 hR0; omega
  · subst hL0
    have h := hs.1
    rw [Fin.sum_univ_one] at h
    exact uniformTrialBound_singletonL hκ hD3 hRc (by linarith)
  · subst hR0
    have h := hs.2
    rw [Fin.sum_univ_one] at h
    exact uniformTrialBound_singletonR hκ hD3 hLc (by linarith)
  · exact uniformTrialBound_ge hκ hD3 hLc hRc

/-- **`TrialsHi3.LP8CritStatement κ` for every `κ > 0`** (Lemma LP8's sector with left total at least `κ/2 − 2`; the
right singleton has weight `> −2` and is unchanged). -/
theorem lp8CritStatement (hκ : 0 < κ) : TrialsHi3.LP8CritStatement.{u} κ := by
  intro N hN hD nL ρL ρR _ h1 _ hsL
  exact uniformTrialBound_singletonR hκ (distinctCompleteBelow_three hN hD) hsL h1

/-! ### The trial statements -/

/-- **`TrialsHi.HighTrialLowStatement κ` for every `κ ≥ 4`.** -/
theorem highTrialLowStatement (hκ : 4 ≤ κ) : TrialsHi.HighTrialLowStatement.{u} κ :=
  TrialsHi3.highTrialLowStatement_of_crit (by linarith) (lowCritStatement (by linarith) (by linarith))

/-- **`TrialsHi2.HighTrialMidStatement κ` for every `0 < κ < 4`.** -/
theorem highTrialMidStatement (hκ : 0 < κ) (hκ4 : κ < 4) : TrialsHi2.HighTrialMidStatement.{u} κ :=
  TrialsHi3.highTrialMidStatement_of_crit hκ hκ4 (lowCritStatement hκ le_rfl)

/-- **`TrialsHi.LP8TrialStatement κ` for every `κ > 0`.** -/
theorem lp8TrialStatement (hκ : 0 < κ) : TrialsHi.LP8TrialStatement.{u} κ :=
  TrialsHi3.lp8TrialStatement_of_crit hκ (lp8CritStatement hκ)

/-! ### The transience consumers -/

/-- **`WangWu.LowSide.LPAux113HighTransienceStatement κ` for every `κ ≥ 4`.** -/
theorem lpAux113HighTransienceStatement (hκ : 4 ≤ κ) : WangWu.LowSide.LPAux113HighTransienceStatement.{u} κ :=
  TrialsHi3.lpAux113HighTransienceStatement_of_crit (by linarith) (lowCritStatement (by linarith) (by linarith))

/-- **Theorem 1.3's input #4 at `κ = 4`**: `WangWu.LowSide.LPAux113HighTransienceStatement 4`. -/
theorem lpAux113HighTransienceStatement_four : WangWu.LowSide.LPAux113HighTransienceStatement.{u} 4 :=
  TrialsHi3.lpAux113HighTransienceStatement_four_of_crit (lowCritStatement (by norm_num) le_rfl)

/-- **Aux. lemma 113's transience `Sec7.LPAux113TransienceStatement κ` for every `κ ≥ 4`** (T13 #14 for `κ > 4`). -/
theorem lpAux113TransienceStatement (hκ : 4 ≤ κ) : LPAux113TransienceStatement.{u} κ :=
  TrialsHi3.lpAux113TransienceStatement_of_crit (by linarith) (lowCritStatement (by linarith) (by linarith))

/-- **Aux. lemma 113's transience for `0 < κ < 4` (T13 #6)** from Proposition 7.3's trace statement. -/
theorem aux113TransienceStatement (h73 : Prop73TraceStatement.{u}) : Aux113TransienceStatement.{u} :=
  TrialsHi3.aux113TransienceStatement_of_crit h73 fun _ hκ _ => lowCritStatement hκ le_rfl

/-- **`LP.LP8TransienceStatement κ` for every `κ > 0`.** -/
theorem lp8TransienceStatement (hκ : 0 < κ) : LP.LP8TransienceStatement.{u} κ :=
  TrialsHi3.lp8TransienceStatement_of_crit hκ (lp8CritStatement hκ)

end TrialsHi4

end Sec7

end InteractingSLE
