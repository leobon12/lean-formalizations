/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2WxMap
import InteractingSLE.Spec.Supplement.GW2GmNest

/-!
# GEOM2's stage boundaries at a root `x` are monotone

Packet PROVE-GW2-BUF (round 18). Step A (`GW2Bh.stageWord_jump_le`) flows the root word along boundaries
`b 0 = 0 ≤ b 1 ≤ …`. GEOM2's root-`x` boundaries `trueBdX` are `0`, then the root-`x` stage starts at the schedule's
times, then the stage start at `T`. On a time-ordered schedule with times `≤ T` they are monotone. Proof:
`schedTime` is monotone, and the stage start is monotone in the time (`monotone_physClockX`, finite caps).

* `schedTime_mono_of_timeOrdered`, `stgStartX_mono`;
* **`trueBdX_zero`**, **`trueBdX_of_le`**, **`monotone_trueBdX`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Bh

open GW2Schedule Sec5.Prop513Schedule GW2Wm GW2Rz

/-- The schedule times of a time-ordered program are monotone on `[0, length]`. -/
theorem schedTime_mono_of_timeOrdered {L : List (ℝ × ℝ≥0)} (hL : TimeOrdered 0 L) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ L.length) : schedTime 0 L i ≤ schedTime 0 L j := by
  rcases i with _ | i
  · exact zero_le
  · rcases j with _ | j
    · omega
    · rw [GW2TipSystem.Gm.schedTime_succ_eq_getElem (by omega),
        GW2TipSystem.Gm.schedTime_succ_eq_getElem (by omega)]
      rcases eq_or_lt_of_le (Nat.le_of_succ_le_succ hij) with h | h
      · subst h; exact le_rfl
      · exact List.pairwise_iff_getElem.1 hL.1 i j (by omega) (by omega) h

section Bd

variable {Ω : Type*} {x₀ : ℝ} {sp : ℝ≥0} {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {GT : Set Ω}
  {V : Ω → ℝ≥0∞} {ω : Ω} {γ α : Ω → ℝ≥0 → ℂ}

/-- The stage start is monotone in the time (finite caps). -/
theorem stgStartX_mono (hGT : ∀ ω ∈ GT, PhysGoodX x₀ sp Wα ζα W γ α ω) (hs : 0 < sp) (hx : 0 ≤ x₀)
    (hV : V ω ≠ ⊤) {t t' : ℝ≥0} (htt : t ≤ t') :
    stgStartX x₀ sp Wα ζα W GT V t ω ≤ stgStartX x₀ sp Wα ζα W GT V t' ω := by
  unfold stgStartX stgStartMX
  refine ENNReal.toNNReal_mono (ne_top_of_le_ne_top hV (min_le_right _ _)) ?_
  exact min_le_min_right _ (monotone_physClockX hGT hs hx ω htt)

theorem trueBdX_zero (L : List (ℝ × ℝ≥0)) (N : ℕ) (T : ℝ≥0) :
    trueBdX x₀ sp Wα ζα W GT V L N T ω 0 = 0 := rfl

theorem trueBdX_of_le (L : List (ℝ × ℝ≥0)) {N : ℕ} (T : ℝ≥0) {j : ℕ} (hj : N ≤ j) (hj0 : j ≠ 0) :
    trueBdX x₀ sp Wα ζα W GT V L N T ω j = stgStartX x₀ sp Wα ζα W GT V T ω := by
  unfold trueBdX
  simp only [hj0, ↓reduceIte, not_lt.2 hj]

/-- **GEOM2's root-`x` boundaries are monotone** on a time-ordered schedule with times `≤ T`. -/
theorem monotone_trueBdX (hGT : ∀ ω ∈ GT, PhysGoodX x₀ sp Wα ζα W γ α ω) (hs : 0 < sp) (hx : 0 ≤ x₀)
    (hV : V ω ≠ ⊤) {L : List (ℝ × ℝ≥0)} (hL : TimeOrdered 0 L) {N : ℕ} (hN : L.length = N)
    {T : ℝ≥0} (hT : ∀ j < N, schedTime 0 L j ≤ T) :
    Monotone (trueBdX x₀ sp Wα ζα W GT V L N T ω) := by
  intro i j hij
  unfold trueBdX
  by_cases hi0 : i = 0
  · simp only [hi0, ↓reduceIte, zero_le]
  · have hj0 : j ≠ 0 := by omega
    simp only [hi0, hj0, ↓reduceIte]
    by_cases hiN : i < N
    · by_cases hjN : j < N
      · simp only [hiN, hjN, ↓reduceIte]
        exact stgStartX_mono hGT hs hx hV (schedTime_mono_of_timeOrdered hL hij (by omega))
      · simp only [hiN, hjN, ↓reduceIte]
        exact stgStartX_mono hGT hs hx hV (hT i hiN)
    · have hjN : ¬ j < N := by omega
      simp only [hiN, hjN, ↓reduceIte, le_refl]

end Bd

end InteractingSLE.Theorem14.GW2Bh
