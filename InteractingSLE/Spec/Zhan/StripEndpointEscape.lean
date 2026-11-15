/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.UpperDrift

/-!
# Linear escape of lower strip gaps (pathwise form)

Packet PROVE-ZHAN-A. Astra §3, "Linear escape of lower strip gaps" (`ig1_formalization_proofs.txt` L1521–L1563):
for a global noncolliding strip word with lower groups and endpoint charges, `q₊ + q₋ = κ − 6`, if
`s_R ≥ −2` and `q₊ > κ/2 − 4`, every right gap grows at least linearly. With `X` the nearest right gap, `Y` the
nearest left gap, `C(x) = coth(x/2)`, the gap equation is

  `X_t − X_u = −√κ(B_t − B_u) + (1 + s_R/2)∫_u^t C(X) − (s_L/2)∫_u^t C(Y) + ½(τ₊ − τ₋)(t − u) + E_t − E_u`  (3.25)

with a bounded finite-variation error `E` (same-side spreads), and `X + Y ≥ X(0) + Y(0) + 2t`. Put
`Δ = 1 + (q₊ − q₋)/2 = 1 + s_R/2 − s_L/2 + ½(τ₊ − τ₋) > 0`.

This file proves the pathwise deduction: from (3.25), the sum bound, Brownian sublinearity of the martingale part
(`∀ ε > 0, ∃ C, |N_u| ≤ C + ε u`), `1 + s_R/2 ≥ 0` and `Δ > 0`, the gap `X` eventually exceeds `α t` for some
`α > 0` (`eventually_mul_le_of_gap_eq`). The source's moving barrier `X_s ≤ a s` is replaced by the barrier
`X_s ≤ s` (on it, `Y_s ≥ s − K`, so `C(Y_s) = 1 + O(e^{−s})`), and the conclusion follows from the barrier argument
of Aux. lemma 21 (`Sec4.barrier_of_integral_eq`, `Sec4.eventually_mul_le_of_barrier`).

The probabilistic inputs — the gap equation (3.25) in strip time with `N = √κ B̃` for the strip Brownian motion `B̃`,
and the sublinearity of `B̃` — are not formalized here (see the handoff, item 1).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory

namespace InteractingSLE

namespace Zhan

/-- The gap drift of (3.25): `(1 + s_R/2) C(X) − (s_L/2) C(Y) + τd`, `τd = ½(τ₊ − τ₋)`. -/
def gapDrift (sR sL τd x y : ℝ) : ℝ := (1 + sR / 2) * Sec4.cothHalf x - sL / 2 * Sec4.cothHalf y + τd

/-- On the barrier, the gap drift is at least `Δ − 4|s_L/2| e^{−y}` (`x > 0`, `y ≥ log 2`). -/
theorem gapDrift_ge {sR sL τd x y : ℝ} (hsR : 0 ≤ 1 + sR / 2) (hx : 0 < x) (hy : Real.log 2 ≤ y) :
    1 + sR / 2 - sL / 2 + τd - |sL / 2| * (4 * Real.exp (-y)) ≤ gapDrift sR sL τd x y := by
  have hy0 : 0 < y := lt_of_lt_of_le (Real.log_pos (by norm_num)) hy
  have h1 := Sec4.one_le_cothHalf hx
  have h2 := Sec4.cothHalf_sub_one_le hy
  have h3 : 0 ≤ Sec4.cothHalf y - 1 := by linarith [Sec4.one_le_cothHalf hy0]
  have h4 : (1 + sR / 2) * 1 ≤ (1 + sR / 2) * Sec4.cothHalf x := mul_le_mul_of_nonneg_left h1 hsR
  have h5 : sL / 2 * (Sec4.cothHalf y - 1) ≤ |sL / 2| * (4 * Real.exp (-y)) :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) h3).trans
      (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
  unfold gapDrift
  nlinarith

/-- **Linear escape of a lower strip gap, pathwise** (Astra (3.24)–(3.25)). -/
theorem eventually_mul_le_of_gap_eq {X Y N E : ℝ → ℝ} {T₀ K V sR sL τd : ℝ}
    (hXc : ContinuousOn X (Ici T₀)) (hX : ∀ u, T₀ ≤ u → 0 < X u)
    (hXY : ∀ u, T₀ ≤ u → 2 * u - K ≤ X u + Y u)
    (hint : ∀ s t, T₀ ≤ s → s ≤ t →
      IntervalIntegrable (fun r => gapDrift sR sL τd (X r) (Y r)) volume s t)
    (heq : ∀ s t, T₀ ≤ s → s ≤ t →
      X t - X s = -(N t - N s) + (∫ r in s..t, gapDrift sR sL τd (X r) (Y r)) - (E t - E s))
    (hN : ∀ ε > 0, ∃ C, ∀ u, T₀ ≤ u → |N u| ≤ C + ε * u)
    (hE : ∀ s t, T₀ ≤ s → s ≤ t → |E t - E s| ≤ V)
    (hsR : 0 ≤ 1 + sR / 2) (hΔ : 0 < 1 + sR / 2 - sL / 2 + τd) :
    ∃ α > 0, ∃ T, ∀ t, T ≤ t → α * t ≤ X t := by
  set Δ := 1 + sR / 2 - sL / 2 + τd with hΔdef
  set b := |sL / 2|
  have hb : 0 ≤ b := abs_nonneg _
  -- a late time after which the left-gap correction is at most `Δ/2`
  set T₁ := max T₀ (K + Real.log 2 + Real.log (1 + 8 * b / Δ)) with hT₁
  have hT₀₁ : T₀ ≤ T₁ := le_max_left _ _
  have hcorr : ∀ u, T₁ ≤ u → b * (4 * Real.exp (-(u - K))) ≤ Δ / 2 := by
    intro u hu
    have hq : 0 < 1 + 8 * b / Δ := by positivity
    have hle : Real.log (1 + 8 * b / Δ) ≤ u - K := by
      have := (le_max_right _ _).trans hu
      have h2 := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
      linarith
    have he : Real.exp (-(u - K)) ≤ 1 / (1 + 8 * b / Δ) := by
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ hq (by rw [← Real.exp_log hq]; exact Real.exp_le_exp.2 hle)
    have : b * (4 * (1 / (1 + 8 * b / Δ))) ≤ Δ / 2 := by
      rw [show 1 + 8 * b / Δ = (Δ + 8 * b) / Δ by field_simp]
      rw [one_div_div, mul_div_assoc', mul_div_assoc', div_le_div_iff₀ (by positivity) two_pos]
      nlinarith
    calc b * (4 * Real.exp (-(u - K))) ≤ b * (4 * (1 / (1 + 8 * b / Δ))) := by gcongr
      _ ≤ Δ / 2 := this
  -- the drift on the barrier
  have hβ : ∀ u, T₁ ≤ u → X u ≤ u → Δ / 2 ≤ gapDrift sR sL τd (X u) (Y u) := by
    intro u hu hXu
    have hu0 : T₀ ≤ u := hT₀₁.trans hu
    have hYu : u - K ≤ Y u := by linarith [hXY u hu0]
    have hlog : Real.log 2 ≤ u - K := by
      have := (le_max_right _ _).trans hu
      have := Real.log_nonneg (show (1 : ℝ) ≤ 1 + 8 * b / Δ by
        have : 0 ≤ 8 * b / Δ := by positivity
        linarith)
      linarith
    have h1 := gapDrift_ge (sL := sL) (τd := τd) hsR (hX u hu0) (hlog.trans hYu)
    have h2 : b * (4 * Real.exp (-Y u)) ≤ b * (4 * Real.exp (-(u - K))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.2 (neg_le_neg hYu)) (by norm_num)) hb
    have h3 := hcorr u hu
    linarith
  -- the barrier argument
  set m := min (Δ / 2) 1 with hm
  have hm0 : 0 < m := lt_min (by linarith) one_pos
  have hmd : m ≤ Δ / 2 := min_le_left _ _
  have hm1 : m ≤ 1 := min_le_right _ _
  obtain ⟨C, hC⟩ := hN (m / 4) (by positivity)
  have hbar := Sec4.barrier_of_integral_eq (X := X) (N := N) (A := E) (β := fun r =>
    gapDrift sR sL τd (X r) (Y r)) (T₀ := T₁) (C := C) (ε := m / 4) (V := V) (d := Δ / 2)
    (fun s t hs hst => hint s t (hT₀₁.trans hs) hst) (fun s t hs hst => heq s t (hT₀₁.trans hs) hst)
    (fun u hu => hC u (hT₀₁.trans hu)) (fun s t hs hst => hE s t (hT₀₁.trans hs) hst) hβ
  obtain ⟨T, hT⟩ := Sec4.eventually_mul_le_of_barrier (X := X) (T₀ := T₁) (d := Δ / 2) (ε := m / 4)
    (α := m / 4) (K := 2 * C + V) (hXc.mono (Ici_subset_Ici.2 hT₀₁)) (by positivity)
    (by linarith) (by linarith) hbar
  exact ⟨m / 4, by positivity, T, hT⟩

end Zhan

end InteractingSLE
