/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.TrialsHiRef
import InteractingSLE.Spec.Sec7.TrialsHiAssembly

/-!
# Aux. lemma 113's third sector: the trial bound split at `κ/2 − 2`

Packet PROVE-TRIALS-HI. In the third sector (both side totals `> d = κ/2 − 4`) the uniform trial bound
(`HighTrialStatement`) is proved here when both side totals exceed `c = κ/2 − 2` from the positivity of the reference
success event of Aux. lemma 111's inner references (`InnerRefPositivityStatement`, the reference law with the side
totals at `∓1` and zero-weight barriers at `∓M`), by the driver-form comparison of Aux. lemmas 108/111
(`uniformTrialBound_inner`). The words with a side total in `(d, c]` (the dipolar finite-overshoot references of Aux.
lemma 110, and the critical total `c`) are the named remainder `HighTrialLowStatement`.

## Main results

* `InnerRefPositivityStatement`, `HighTrialLowStatement` (named inputs);
* `highTrialStatement_of_ref`;
* `lpAux113HighTransienceStatement_of_ref`, `aux113HighTransienceStatement_of_ref`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace TrialsHi

/-- **Named input: positivity of the reference success event for Aux. lemma 111's inner references** (Specification
p. 364, "Both totals are at least `c`. Take the reference weights to be `s_L, s_R`. Aux. lemma 7 supplies a continuous
transient trace whose two marks are never swallowed … Choose deterministic `δ > 0` such that this distance exceeds
`4δ` with positive probability"), in driver form: for side totals `s_L, s_R > κ/2 − 2` and every `M ≥ 1`, the
four-mark word `(−1, −M; 1, M)` with weights `(s_L, 0; s_R, 0)` has an almost surely infinite lifetime and a reference
success event (`RefGood`: nearest marks never hit, bounded side oscillations, quantitative transience) of positive
probability. The smaller-count hypothesis at `N = 3` (two-mark words complete) is available. -/
def InnerRefPositivityStatement (κ : ℝ) : Prop :=
  LP.DistinctCompleteBelow.{u} κ 3 → ∀ sL sR : ℝ, κ / 2 - 2 < sL → κ / 2 - 2 < sR →
    ∀ M : ℝ, 1 ≤ M → RefTrialPositivity κ M ![sL, 0] ![sR, 0]

/-- **Named input: the uniform trial bound when a side total lies in `(κ/2 − 4, κ/2 − 2]`** (Aux. lemma 111's
finite-overshoot case with the dipolar reference of Aux. lemma 110, p. 365, and the critical total `κ/2 − 2`). -/
def HighTrialLowStatement (κ : ℝ) : Prop :=
  ∀ N : ℕ, 3 ≤ N → LP.DistinctCompleteBelow.{u} κ N →
    ∀ {nL nR : ℕ} (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ), nL + 1 + (nR + 1) = N →
      (κ / 2 - 4 < ∑ i, ρL i ∧ κ / 2 - 4 < ∑ i, ρR i) → ((∑ i, ρL i) ≤ κ / 2 - 2 ∨ (∑ i, ρR i) ≤ κ / 2 - 2) →
      UniformTrialBound κ ρL ρR

/-- **The third-sector trial bound from the inner-reference positivity and the low-total remainder** (every
`κ > 0`). -/
theorem highTrialStatement_of_ref {κ : ℝ} (hκ : 0 < κ) (hpos : InnerRefPositivityStatement.{u} κ)
    (hlow : HighTrialLowStatement.{u} κ) : HighTrialStatement.{u} κ := by
  intro N hN hD nL nR ρL ρR hc hs
  by_cases hhigh : κ / 2 - 2 < ∑ i, ρL i ∧ κ / 2 - 2 < ∑ i, ρR i
  · have hD3 : LP.DistinctCompleteBelow.{u} κ 3 := fun xL xR ρL ρR hd hlt => hD xL xR ρL ρR hd (by omega)
    exact uniformTrialBound_inner hκ fun M hM => hpos hD3 _ _ hhigh.1 hhigh.2 M hM
  · rw [not_and_or, not_lt, not_lt] at hhigh
    exact hlow N hN hD ρL ρR hc hs hhigh

/-- **`WangWu.LowSide.LPAux113HighTransienceStatement κ` from Aux. lemma 101, the inner-reference positivity and the
low-total remainder** (every `κ > 0`; at `κ = 4` Theorem 1.3's input #4). -/
theorem lpAux113HighTransienceStatement_of_ref {κ : ℝ} (hκ : 0 < κ) (h101 : Aux101BandClockStatement.{u} κ)
    (hpos : InnerRefPositivityStatement.{u} κ) (hlow : HighTrialLowStatement.{u} κ) :
    WangWu.LowSide.LPAux113HighTransienceStatement.{u} κ :=
  lpAux113HighTransienceStatement_of_trials hκ h101 (highTrialStatement_of_ref hκ hpos hlow)

/-- **`WangWu.LowSide.Aux113HighTransienceStatement` (the `κ < 4` form) from the same inputs for `0 < κ < 4`**. -/
theorem aux113HighTransienceStatement_of_ref
    (h101 : ∀ κ : ℝ, 0 < κ → κ < 4 → Aux101BandClockStatement.{u} κ)
    (hpos : ∀ κ : ℝ, 0 < κ → κ < 4 → InnerRefPositivityStatement.{u} κ)
    (hlow : ∀ κ : ℝ, 0 < κ → κ < 4 → HighTrialLowStatement.{u} κ) :
    WangWu.LowSide.Aux113HighTransienceStatement.{u} :=
  aux113HighTransienceStatement_of_trials h101 fun κ hκ hκ4 =>
    highTrialStatement_of_ref hκ (hpos κ hκ hκ4) (hlow κ hκ hκ4)

end TrialsHi

end Sec7

end InteractingSLE
