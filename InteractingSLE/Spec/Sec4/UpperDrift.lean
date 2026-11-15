/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.Heights
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Aux. lemma 21: the bounded upper contribution and linear separation (deterministic core)

Packet PROVE-SEC4-A (specification §4.1, Aux. lemma 21, `source/spec/p097-144.md` L291–L405, pp. 109–113).

The proof of Aux. lemma 21 works in the strip `{0 < Im z < π}` with lower force groups and finitely many upper marks
at the jumps `p_j + iπ` of the upper heights `a₀, …, a_m`. This file proves its deterministic steps:

* (UC2): the upper weights `ω_j = (a_{j−1} − a_j)/Λ` and the endpoint charges satisfy
  `q₊ + q₋ + ∑ ω_j = k − 6` (`endCharge_add_sum_upperWeight`); deleting the upper marks and adding half their total
  weight to each endpoint preserves the endpoint drift and restores the sum (`delete_upper_marks`);
* (UC3)–(UC4): Abel summation writes the bounded upper drift
  `b = (q₋ − q₊)/2 − ½ ∑ ω_j tanh(X_j/2)` as `−Λ⁻¹ ∑ a_j (w_j − w_{j+1})` with `w_0 = 1`,
  `w_j = (1 − tanh(X_j/2))/2`, `w_{m+1} = 0` (`upperDrift_eq_abel`);
* (UC5): for ordered marks the coefficients are nonnegative with sum one, so `|b| ≤ max_j |a_j|/Λ`
  (`abs_upperDrift_le`);
* (UC10): if eventually `X_j < 0` for `j ≤ j₀`, `X_j > 0` for `j > j₀`, and `|X_j| ≥ ℓ`, then
  `|b + a_{j₀}/Λ| ≤ 2 e^{−ℓ} ∑_j |a_j| / Λ` (`abs_upperDrift_add_le`);
* the elementary barrier argument after (UC7): the drift bound gives (UC8) (`barrier_of_integral_eq`), and (UC8)
  gives eventual linear growth `X_t ≥ α t` (`eventually_mul_le_of_barrier`), a slightly stronger form of
  `liminf X_t / t ≥ α`;
* the lower bound of the bracketed drift in (UC7) (`one_sub_le_drift_UC7`).
-/

set_option autoImplicit false

noncomputable section

open Real Set Filter Finset MeasureTheory Topology

namespace InteractingSLE

namespace Sec4

/-! ### (UC2): upper weights and endpoint charges -/

/-- The weight `ω_j = (a_{j−1} − a_j)/Λ` of the upper mark at the `j`-th jump (`j = i + 1`). -/
def upperMarkWeight (k : ℝ) (a : ℕ → ℝ) (i : ℕ) : ℝ := (a i - a (i + 1)) / sleLambda k

/-- (UC2): `q₊ + q₋ + ∑_{j=1}^m ω_j = k − 6`, with `q₊ = k/2 − 3 + a_m/Λ`, `q₋ = k/2 − 3 − a₀/Λ`. -/
theorem endCharge_add_sum_upperWeight (k : ℝ) (a : ℕ → ℝ) (m : ℕ) :
    endChargeRight k (a m) + endChargeLeft k (a 0) + ∑ i ∈ range m, upperMarkWeight k a i = k - 6 := by
  have htel : ∑ i ∈ range m, upperMarkWeight k a i = (a 0 - a m) / sleLambda k := by
    simp only [upperMarkWeight, ← Finset.sum_div]
    congr 1
    induction m with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ih]; ring
  rw [htel]
  simp only [endChargeRight, endChargeLeft]
  ring

/-- Deleting the upper marks: adding half their total weight `W` to each endpoint preserves the endpoint drift
`(q₋ − q₊)/2` and the sum `k − 6`. -/
theorem delete_upper_marks (qp qm W k : ℝ) (h : qp + qm + W = k - 6) :
    ((qm + W / 2) - (qp + W / 2)) / 2 = (qm - qp) / 2 ∧ (qp + W / 2) + (qm + W / 2) = k - 6 := by
  constructor <;> linarith

/-! ### (UC3)–(UC4): Abel summation of the upper drift -/

/-- (UC3): the bounded upper drift `b = (q₋ − q₊)/2 − ½ ∑_{j=1}^m ω_j t_j`, where `t_j = tanh(X_j/2)`
(index `j = i + 1`). -/
def upperDrift (k : ℝ) (a : ℕ → ℝ) (m : ℕ) (t : ℕ → ℝ) : ℝ :=
  (endChargeLeft k (a 0) - endChargeRight k (a m)) / 2 -
    (1 / 2) * ∑ i ∈ range m, upperMarkWeight k a i * t (i + 1)

/-- The coefficients of (UC4): `w_0 = 1`, `w_j = (1 − t_j)/2` for `1 ≤ j ≤ m`, `w_{m+1} = 0`. -/
def abelWeight (m : ℕ) (t : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 1 else if j ≤ m then (1 - t j) / 2 else 0

theorem abelWeight_zero (m : ℕ) (t : ℕ → ℝ) : abelWeight m t 0 = 1 := by simp [abelWeight]

theorem abelWeight_of_le {m j : ℕ} (t : ℕ → ℝ) (h1 : 1 ≤ j) (hj : j ≤ m) :
    abelWeight m t j = (1 - t j) / 2 := by
  simp [abelWeight, Nat.one_le_iff_ne_zero.1 h1, hj]

theorem abelWeight_of_lt {m j : ℕ} (t : ℕ → ℝ) (hj : m < j) : abelWeight m t j = 0 := by
  simp [abelWeight, (Nat.zero_le m).trans_lt hj |>.ne', not_le.2 hj]

theorem sum_range_sub_succ (a : ℕ → ℝ) (m : ℕ) : ∑ i ∈ range m, (a i - a (i + 1)) = a 0 - a m := by
  induction m with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; ring

/-- Abel summation. -/
theorem sum_mul_sub_succ (a V : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ range (n + 1), a j * (V j - V (j + 1)) =
      a 0 * V 0 - a n * V (n + 1) - ∑ j ∈ range n, (a j - a (j + 1)) * V (j + 1) := by
  induction n with
  | zero => simp [mul_sub]
  | succ n ih => rw [sum_range_succ, ih, sum_range_succ]; ring

/-- (UC4): `b = −Λ⁻¹ [a₀(1 − w₁) + ∑_{j=1}^{m−1} a_j (w_j − w_{j+1}) + a_m w_m]`. -/
theorem upperDrift_eq_abel {k : ℝ} (hk : 0 < k) (a : ℕ → ℝ) (m : ℕ) (t : ℕ → ℝ) :
    upperDrift k a m t =
      -(1 / sleLambda k) * ∑ j ∈ range (m + 1), a j * (abelWeight m t j - abelWeight m t (j + 1)) := by
  have hl := sleLambda_ne_zero hk
  rw [sum_mul_sub_succ]
  have hi : ∀ i ∈ range m, (a i - a (i + 1)) * abelWeight m t (i + 1) =
      (a i - a (i + 1)) * ((1 - t (i + 1)) / 2) := by
    intro i hi
    rw [abelWeight_of_le t (Nat.le_add_left 1 i) (Finset.mem_range.1 hi)]
  rw [abelWeight_zero, abelWeight_of_lt t (Nat.lt_succ_self m), sum_congr rfl hi]
  have htel := sum_range_sub_succ a m
  have hsplit : ∑ i ∈ range m, (a i - a (i + 1)) * ((1 - t (i + 1)) / 2) =
      (a 0 - a m) / 2 - (1 / 2) * ∑ i ∈ range m, (a i - a (i + 1)) * t (i + 1) := by
    rw [← htel, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine sum_congr rfl fun i _ => by ring
  rw [hsplit]
  simp only [upperDrift, upperMarkWeight, endChargeLeft, endChargeRight]
  rw [show ∑ i ∈ range m, (a i - a (i + 1)) / sleLambda k * t (i + 1) =
      (∑ i ∈ range m, (a i - a (i + 1)) * t (i + 1)) / sleLambda k by
    rw [Finset.sum_div]; exact sum_congr rfl fun i _ => by ring]
  field_simp
  ring

/-- The coefficients of (UC4) are nonnegative when `−1 ≤ t_1 ≤ ⋯ ≤ t_m ≤ 1`. -/
theorem abelWeight_sub_nonneg {m : ℕ} {t : ℕ → ℝ} (hmono : ∀ j, 1 ≤ j → j < m → t j ≤ t (j + 1))
    (hle : ∀ j, 1 ≤ j → j ≤ m → -1 ≤ t j ∧ t j ≤ 1) (j : ℕ) (hj : j ≤ m) :
    0 ≤ abelWeight m t j - abelWeight m t (j + 1) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [abelWeight_zero]
    by_cases hm : 1 ≤ m
    · rw [abelWeight_of_le t le_rfl hm]
      linarith [(hle 1 le_rfl hm).1]
    · rw [abelWeight_of_lt t (by omega)]; norm_num
  · rw [abelWeight_of_le t hj0 hj]
    by_cases hjm : j < m
    · rw [abelWeight_of_le t (by omega) hjm]
      linarith [hmono j hj0 hjm]
    · rw [abelWeight_of_lt t (by omega)]
      linarith [(hle j hj0 hj).2]

/-- The coefficients of (UC4) sum to one. -/
theorem sum_abelWeight_sub (m : ℕ) (t : ℕ → ℝ) :
    ∑ j ∈ range (m + 1), (abelWeight m t j - abelWeight m t (j + 1)) = 1 := by
  have := sum_mul_sub_succ (fun _ => (1 : ℝ)) (abelWeight m t) m
  simp only [one_mul, sub_self, zero_mul, sum_const_zero, sub_zero] at this
  rw [this, abelWeight_zero, abelWeight_of_lt t (Nat.lt_succ_self m), sub_zero]

/-- (UC5): for ordered upper marks (`t_j = tanh(X_j/2)` nondecreasing in `j`, values in `[−1, 1]`) and heights
`|a_j| ≤ M`, the bounded upper drift satisfies `|b| ≤ M/Λ`. No monotonicity of the heights is required. -/
theorem abs_upperDrift_le {k : ℝ} (hk : 0 < k) {a : ℕ → ℝ} {m : ℕ} {t : ℕ → ℝ} {M : ℝ}
    (ha : ∀ j, j ≤ m → |a j| ≤ M) (hmono : ∀ j, 1 ≤ j → j < m → t j ≤ t (j + 1))
    (hle : ∀ j, 1 ≤ j → j ≤ m → -1 ≤ t j ∧ t j ≤ 1) :
    |upperDrift k a m t| ≤ M / sleLambda k := by
  have hl := sleLambda_pos hk
  rw [upperDrift_eq_abel hk, abs_mul, abs_neg, abs_of_pos (one_div_pos.2 hl), one_div,
    div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hl.le)
  calc |∑ j ∈ range (m + 1), a j * (abelWeight m t j - abelWeight m t (j + 1))|
      ≤ ∑ j ∈ range (m + 1), |a j * (abelWeight m t j - abelWeight m t (j + 1))| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range (m + 1), M * (abelWeight m t j - abelWeight m t (j + 1)) := by
        refine sum_le_sum fun j hj => ?_
        have hj' : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        have hc := abelWeight_sub_nonneg hmono hle j hj'
        rw [abs_mul, abs_of_nonneg hc]
        exact mul_le_mul_of_nonneg_right (ha j hj') hc
    _ = M := by rw [← Finset.mul_sum, sum_abelWeight_sub, mul_one]

/-! ### The weights `w(x) = (1 − tanh(x/2))/2 = 1/(1 + e^x)` and (UC10) -/

theorem one_sub_tanh_half_div_two (x : ℝ) : (1 - tanh (x / 2)) / 2 = 1 / (1 + exp x) := by
  have he : exp (x / 2) * exp (x / 2) = exp x := by rw [← exp_add]; ring_nf
  have hn : exp (-(x / 2)) * exp (x / 2) = 1 := by rw [← exp_add]; simp
  have h1 := exp_pos (x / 2)
  have h2 := exp_pos (-(x / 2))
  rw [tanh_eq]
  have hd : exp (x / 2) + exp (-(x / 2)) ≠ 0 := by positivity
  field_simp
  have : exp (-(x / 2)) = 1 / exp (x / 2) := by rw [exp_neg, one_div]
  rw [this, ← he]
  field_simp
  ring

/-- `0 ≤ 1 − w(x) ≤ e^{x}` (useful for `x < 0`). -/
theorem abs_weight_sub_one_le (x : ℝ) : |(1 - tanh (x / 2)) / 2 - 1| ≤ exp x := by
  rw [one_sub_tanh_half_div_two]
  have he := exp_pos x
  have : 1 / (1 + exp x) - 1 = -(exp x / (1 + exp x)) := by field_simp; ring
  rw [this, abs_neg, abs_of_pos (by positivity), div_le_iff₀ (by positivity)]
  nlinarith

/-- For `x > 0`, `0 ≤ w(x) ≤ e^{−x}`. -/
theorem abs_weight_le {x : ℝ} : |(1 - tanh (x / 2)) / 2| ≤ exp (-x) := by
  rw [one_sub_tanh_half_div_two, abs_of_pos (by positivity), exp_neg, one_div]
  exact inv_anti₀ (exp_pos x) (by linarith [exp_pos x])

/-- The weight is strictly antitone, so ordered upper marks `X₁ < ⋯ < X_m` give `1 > w₁ > ⋯ > w_m > 0`. -/
theorem tanh_half_strictMono : StrictMono fun x : ℝ => tanh (x / 2) := by
  intro x y hxy
  have hx := one_sub_tanh_half_div_two x
  have hy := one_sub_tanh_half_div_two y
  have : 1 / (1 + exp y) < 1 / (1 + exp x) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith [exp_lt_exp.2 hxy])
  simp only at *
  linarith

/-- (UC10): on the eventual tail, if `X_j < 0` for `1 ≤ j ≤ j₀`, `X_j > 0` for `j₀ < j ≤ m`, and every
`|X_j| ≥ ℓ`, then `|b + a_{j₀}/Λ| ≤ 2 e^{−ℓ} ∑_{j ≤ m} |a_j| / Λ`, an exponentially small error when `ℓ` grows
linearly. -/
theorem abs_upperDrift_add_le {k : ℝ} (hk : 0 < k) {a : ℕ → ℝ} {m j₀ : ℕ} (hj₀ : j₀ ≤ m)
    {X : ℕ → ℝ} {ℓ : ℝ} (hneg : ∀ j, 1 ≤ j → j ≤ j₀ → X j < 0) (hpos : ∀ j, j₀ < j → j ≤ m → 0 < X j)
    (hℓ : ∀ j, 1 ≤ j → j ≤ m → ℓ ≤ |X j|) :
    |upperDrift k a m (fun j => tanh (X j / 2)) + a j₀ / sleLambda k| ≤
      2 * exp (-ℓ) * (∑ j ∈ range (m + 1), |a j|) / sleLambda k := by
  have hl := sleLambda_pos hk
  set t : ℕ → ℝ := fun j => tanh (X j / 2)
  -- the limiting weights
  set V : ℕ → ℝ := fun j => if j ≤ j₀ then 1 else 0
  have hV : ∀ j, j ≤ m + 1 → |abelWeight m t j - V j| ≤ exp (-ℓ) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [abelWeight, V, (exp_pos _).le]
    · by_cases hjm : j ≤ m
      · have hX := hℓ j hj0 hjm
        by_cases hjj : j ≤ j₀
        · rw [abelWeight_of_le t hj0 hjm]
          simp only [V, hjj, ↓reduceIte, t]
          have hx := hneg j hj0 hjj
          rw [abs_of_neg hx] at hX
          calc _ ≤ exp (X j) := abs_weight_sub_one_le _
            _ ≤ exp (-ℓ) := exp_le_exp.2 (by linarith)
        · rw [abelWeight_of_le t hj0 hjm]
          simp only [V, hjj, ↓reduceIte, t, sub_zero]
          have hx := hpos j (not_le.1 hjj) hjm
          rw [abs_of_pos hx] at hX
          calc _ ≤ exp (-X j) := abs_weight_le
            _ ≤ exp (-ℓ) := exp_le_exp.2 (by linarith)
      · have hjm' : j = m + 1 := le_antisymm hj (not_le.1 hjm)
        have hjj : ¬ j ≤ j₀ := by omega
        simp [abelWeight, V, hjm, hjj, hj0.ne', (exp_pos _).le]
  have hsumV : ∑ j ∈ range (m + 1), a j * (V j - V (j + 1)) = a j₀ := by
    rw [sum_eq_single j₀]
    · simp [V]
    · intro j _ hj
      by_cases h1 : j ≤ j₀
      · have : j + 1 ≤ j₀ := by omega
        simp [V, h1, this]
      · have : ¬ j + 1 ≤ j₀ := by omega
        simp [V, h1, this]
    · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hj₀)) h
  rw [upperDrift_eq_abel hk, ← hsumV]
  rw [show -(1 / sleLambda k) * ∑ j ∈ range (m + 1), a j * (abelWeight m t j - abelWeight m t (j + 1)) +
      (∑ j ∈ range (m + 1), a j * (V j - V (j + 1))) / sleLambda k =
      -((∑ j ∈ range (m + 1), a j * ((abelWeight m t j - V j) - (abelWeight m t (j + 1) - V (j + 1)))) /
        sleLambda k) by
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring]
  rw [abs_neg, abs_div, abs_of_pos hl, div_le_div_iff_of_pos_right hl]
  calc |∑ j ∈ range (m + 1), a j * ((abelWeight m t j - V j) - (abelWeight m t (j + 1) - V (j + 1)))|
      ≤ ∑ j ∈ range (m + 1), |a j| * (2 * exp (-ℓ)) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
        have hj' : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        calc _ ≤ |abelWeight m t j - V j| + |abelWeight m t (j + 1) - V (j + 1)| := abs_sub _ _
          _ ≤ exp (-ℓ) + exp (-ℓ) := add_le_add (hV j (by omega)) (hV (j + 1) (by omega))
          _ = 2 * exp (-ℓ) := by ring
    _ = 2 * exp (-ℓ) * ∑ j ∈ range (m + 1), |a j| := by rw [← Finset.sum_mul, mul_comm]

/-! ### The drift lower bound in (UC7) -/

/-- `coth(x/2) = (e^x + 1)/(e^x − 1)`. -/
def cothHalf (x : ℝ) : ℝ := (exp x + 1) / (exp x - 1)

theorem cothHalf_eq_inv_tanh {x : ℝ} (hx : x ≠ 0) : cothHalf x = 1 / tanh (x / 2) := by
  have h := one_sub_tanh_half_div_two x
  have he : exp x ≠ 1 := fun h' => hx (exp_eq_one_iff x |>.1 h')
  have hth : tanh (x / 2) = (exp x - 1) / (exp x + 1) := by
    have h1 : 0 < 1 + exp x := by positivity
    field_simp at h
    field_simp
    linarith
  rw [hth, cothHalf, one_div_div]

/-- `coth(x/2) ≥ 1` for `x > 0`. -/
theorem one_le_cothHalf {x : ℝ} (hx : 0 < x) : 1 ≤ cothHalf x := by
  have : 1 < exp x := one_lt_exp_iff.2 hx
  rw [cothHalf, one_le_div (by linarith)]
  linarith

/-- `coth(x/2) − 1 = 2/(e^x − 1)`, which tends to zero. -/
theorem cothHalf_sub_one {x : ℝ} (hx : 0 < x) : cothHalf x - 1 = 2 / (exp x - 1) := by
  have : 1 < exp x := one_lt_exp_iff.2 hx
  rw [cothHalf, div_sub_one (by linarith)]; ring_nf

/-- The bracketed drift of (UC7), `(1 + s_R/2) coth(X/2) − s_R/2 − b − (s_L/2){coth(Y/2) − 1}`, is at least
`1 − μ − |s_L/2| (coth(Y/2) − 1)` when `X, Y > 0`, `1 + s_R/2 ≥ 0` and `|b| ≤ μ`. -/
theorem one_sub_le_drift_UC7 {sR sL b μ X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) (hsR : 0 ≤ 1 + sR / 2)
    (hb : |b| ≤ μ) :
    1 - μ - |sL / 2| * (cothHalf Y - 1) ≤
      (1 + sR / 2) * cothHalf X - sR / 2 - b - sL / 2 * (cothHalf Y - 1) := by
  have h1 := one_le_cothHalf hX
  have hY1 : 0 ≤ cothHalf Y - 1 := by linarith [one_le_cothHalf hY]
  have h2 : (1 + sR / 2) * 1 ≤ (1 + sR / 2) * cothHalf X := mul_le_mul_of_nonneg_left h1 hsR
  have h3 : sL / 2 * (cothHalf Y - 1) ≤ |sL / 2| * (cothHalf Y - 1) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hY1
  have h4 : b ≤ μ := (le_abs_self b).trans hb
  linarith

/-! ### The barrier argument: (UC7) ⟹ (UC8) ⟹ linear growth -/

/-- From the integrated form of (UC7) to (UC8): if `X_t − X_s = −(N_t − N_s) + ∫_s^t β − (A_t − A_s)` with
`|N_u| ≤ C + ε u` (the Brownian strong law), `|A_t − A_s| ≤ V` (the finite total variation of `A`), and
`β_u ≥ d` whenever `X_u ≤ u`, then on every late interval `[s, t]` with `X_u ≤ u` throughout,
`X_t − X_s ≥ −K − ε(t + s) + d(t − s)` with `K = 2C + V`. -/
theorem barrier_of_integral_eq {X N A β : ℝ → ℝ} {T₀ C ε V d : ℝ}
    (hint : ∀ s t, T₀ ≤ s → s ≤ t → IntervalIntegrable β volume s t)
    (heq : ∀ s t, T₀ ≤ s → s ≤ t → X t - X s = -(N t - N s) + (∫ u in s..t, β u) - (A t - A s))
    (hN : ∀ u, T₀ ≤ u → |N u| ≤ C + ε * u) (hA : ∀ s t, T₀ ≤ s → s ≤ t → |A t - A s| ≤ V)
    (hβ : ∀ u, T₀ ≤ u → X u ≤ u → d ≤ β u) :
    ∀ s t, T₀ ≤ s → s ≤ t → (∀ u ∈ Icc s t, X u ≤ u) →
      -(2 * C + V) - ε * (t + s) + d * (t - s) ≤ X t - X s := by
  intro s t hs hst hle
  rw [heq s t hs hst]
  have hI : d * (t - s) ≤ ∫ u in s..t, β u := by
    have : ∫ _ in s..t, d = d * (t - s) := by simp [mul_comm]
    rw [← this]
    exact intervalIntegral.integral_mono_on hst intervalIntegrable_const (hint s t hs hst)
      fun u hu => hβ u (hs.trans hu.1) (hle u hu)
  have h1 := hN s hs
  have h2 := hN t (hs.trans hst)
  have h3 := hA s t hs hst
  have h4 : N t - N s ≤ |N t| + |N s| := by
    have := abs_sub (N t) (N s); linarith [le_abs_self (N t - N s)]
  have h5 : A t - A s ≤ V := (le_abs_self _).trans h3
  linarith

/-- On `[u₀, t]` with `X u₀ ≥ u₀` and `X t < t`, the last time `s` with `X s ≥ s` has `X s = s`, and `X u < u` on
`(s, t]`. -/
theorem exists_last_crossing {X : ℝ → ℝ} {u₀ t : ℝ} (hX : ContinuousOn X (Icc u₀ t)) (hut : u₀ ≤ t)
    (h0 : u₀ ≤ X u₀) (ht : X t < t) :
    ∃ s ∈ Icc u₀ t, X s = s ∧ ∀ u ∈ Ioc s t, X u < u := by
  set A : Set ℝ := {u ∈ Icc u₀ t | u ≤ X u}
  have hAc : IsClosed A := by
    have hg : ContinuousOn (fun u => X u - u) (Icc u₀ t) := hX.sub continuousOn_id
    have : A = Icc u₀ t ∩ (fun u => X u - u) ⁻¹' Ici 0 := by
      ext u; simp only [A, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ici,
        sub_nonneg]
    rw [this]
    exact hg.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hAne : A.Nonempty := ⟨u₀, ⟨left_mem_Icc.2 hut, h0⟩⟩
  have hAbdd : BddAbove A := ⟨t, fun u hu => hu.1.2⟩
  set s := sSup A
  have hsA : s ∈ A := hAc.csSup_mem hAne hAbdd
  have hafter : ∀ u ∈ Ioc s t, X u < u := by
    intro u hu
    by_contra hcon
    push Not at hcon
    have : u ∈ A := ⟨⟨hsA.1.1.trans hu.1.le, hu.2⟩, hcon⟩
    exact absurd (le_csSup hAbdd this) (not_le.2 hu.1)
  refine ⟨s, hsA.1, le_antisymm ?_ hsA.2, hafter⟩
  -- `X s ≤ s` by continuity from the right
  have hst : s < t := lt_of_le_of_ne hsA.1.2 fun h => by
    have := hsA.2; rw [h] at this; linarith
  have hsub : Ioc s t ⊆ Icc u₀ t := fun u hu => ⟨hsA.1.1.trans hu.1.le, hu.2⟩
  have hcont : ContinuousWithinAt (fun u => X u - u) (Ioc s t) s :=
    ((hX.sub continuousOn_id) s hsA.1).mono hsub
  have : (𝓝[Ioc s t] s).NeBot := mem_closure_iff_nhdsWithin_neBot.1
    (by rw [closure_Ioc hst.ne]; exact left_mem_Icc.2 hst.le)
  have := le_of_tendsto hcont
    (eventually_nhdsWithin_of_forall fun u hu => (sub_neg.2 (hafter u hu)).le)
  linarith

/-- **The barrier argument of Aux. lemma 21** (after (UC7)): let `X` be continuous on `[T₀, ∞)` and suppose
(UC8): `X_t − X_s ≥ −K − ε(t + s) + d(t − s)` on every interval `[s, t] ⊆ [T₀, ∞)` with `X_u ≤ u` throughout. If
`ε ≥ 0`, `α + ε < d` and `2ε + α < 1` (the source takes `ε = d/8`, `α = d/4`, `d < 1`), then eventually
`X_t ≥ α t`; in particular `liminf X_t/t ≥ α`. -/
theorem eventually_mul_le_of_barrier {X : ℝ → ℝ} {T₀ d ε α K : ℝ} (hX : ContinuousOn X (Ici T₀))
    (hε : 0 ≤ ε) (hd : α + ε < d) (h1 : 2 * ε + α < 1)
    (hbar : ∀ s t, T₀ ≤ s → s ≤ t → (∀ u ∈ Icc s t, X u ≤ u) →
      -K - ε * (t + s) + d * (t - s) ≤ X t - X s) :
    ∃ T, ∀ t, T ≤ t → α * t ≤ X t := by
  have hc : 0 < 1 - 2 * ε - α := by linarith
  -- a late time after which an interval from the line `u ↦ u` down to `α t` is impossible
  set S : ℝ := max (max T₀ 0) (|K| / (1 - 2 * ε - α) + 1)
  have hST₀ : T₀ ≤ S := (le_max_left _ _).trans (le_max_left _ _)
  have hS0 : 0 ≤ S := (le_max_right _ _).trans (le_max_left _ _)
  have hSK : K < (1 - 2 * ε - α) * S := by
    have h2 : |K| / (1 - 2 * ε - α) + 1 ≤ S := le_max_right _ _
    have h3 : |K| < (1 - 2 * ε - α) * (|K| / (1 - 2 * ε - α) + 1) := by
      rw [mul_add, mul_div_cancel₀ _ hc.ne', mul_one]; linarith
    have h4 := mul_le_mul_of_nonneg_left h2 hc.le
    linarith [le_abs_self K]
  have hαd : α < d := by linarith
  by_cases hcase : ∃ u₀, S ≤ u₀ ∧ u₀ ≤ X u₀
  · -- some late time on or above the line: from then on, `X ≥ α t`
    obtain ⟨u₀, hSu, hu₀⟩ := hcase
    refine ⟨u₀, fun t hut => ?_⟩
    by_contra hcon
    push Not at hcon
    have hα1 : α < 1 := by linarith
    have ht0 : 0 ≤ t := hS0.trans (hSu.trans hut)
    have hXt : X t < t := by nlinarith
    obtain ⟨s, hs, hXs, hafter⟩ :=
      exists_last_crossing (hX.mono fun u hu => (hST₀.trans hSu).trans hu.1) hut hu₀ hXt
    have hle : ∀ u ∈ Icc s t, X u ≤ u := by
      intro u hu
      rcases eq_or_lt_of_le hu.1 with h | h
      · rw [← h, hXs]
      · exact (hafter u ⟨h, hu.2⟩).le
    have hb := hbar s t ((hST₀.trans hSu).trans hs.1) hs.2 hle
    have hSs : S ≤ s := hSu.trans hs.1
    -- `K ≥ (d − ε − α)(t − s) + (1 − 2ε − α) s ≥ (1 − 2ε − α) S > K`
    have hts : 0 ≤ t - s := by linarith [hs.2]
    have e1 : 0 ≤ (d - ε - α) * (t - s) := mul_nonneg (by linarith) hts
    have e2 : (1 - 2 * ε - α) * S ≤ (1 - 2 * ε - α) * s := mul_le_mul_of_nonneg_left hSs hc.le
    nlinarith
  · -- the path stays below the line after `S`: (UC8) on `[S, t]` gives slope `d − ε > α`
    push Not at hcase
    set C₀ := X S - K - ε * S - d * S
    refine ⟨max S (-C₀ / (d - ε - α)), fun t ht => ?_⟩
    have hSt : S ≤ t := (le_max_left _ _).trans ht
    have hle : ∀ u ∈ Icc S t, X u ≤ u := fun u hu => (hcase u hu.1).le
    have hb := hbar S t hST₀ hSt hle
    have hpos : 0 < d - ε - α := by linarith
    have ht2 : -C₀ / (d - ε - α) ≤ t := (le_max_right _ _).trans ht
    have : -C₀ ≤ (d - ε - α) * t := by rwa [div_le_iff₀ hpos, mul_comm] at ht2
    nlinarith


/-! ### The drift correction of the lower groups is square integrable on the tail -/

/-- For `x ≥ log 2`, `coth(x/2) − 1 ≤ 4 e^{−x}`. -/
theorem cothHalf_sub_one_le {x : ℝ} (hx : Real.log 2 ≤ x) : cothHalf x - 1 ≤ 4 * exp (-x) := by
  have h2 : 2 ≤ exp x := by
    calc (2 : ℝ) = exp (Real.log 2) := (exp_log (by norm_num)).symm
      _ ≤ exp x := exp_le_exp.2 hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.log_pos (by norm_num)) hx
  rw [cothHalf_sub_one hx0, exp_neg, div_le_iff₀ (by linarith)]
  have he := exp_pos x
  rw [show 4 * (exp x)⁻¹ * (exp x - 1) = 4 - 4 * (exp x)⁻¹ by field_simp]
  have : (exp x)⁻¹ ≤ 1 / 2 := by rw [inv_le_comm₀ he (by norm_num)]; linarith
  linarith

/-- (After (UC8)) once a lower gap grows linearly, `X_t ≥ α t` for `t ≥ T`, the correction
`ρ (coth(X_t/2) − 1)` of that group to the driver drift is square integrable on `(T', ∞)`,
`T' = max T (log 2 / α)`; this is the finiteness of the energy deleted by Girsanov in Aux. lemma 21. -/
theorem integrableOn_sq_correction {X : ℝ → ℝ} {α T ρ : ℝ} (hα : 0 < α)
    (hXm : Measurable X) (hX : ∀ t, T ≤ t → α * t ≤ X t) :
    IntegrableOn (fun t => (ρ * (cothHalf (X t) - 1)) ^ 2) (Ioi (max T (Real.log 2 / α))) := by
  set T' := max T (Real.log 2 / α)
  have hbound : ∀ t ∈ Ioi T', ‖(ρ * (cothHalf (X t) - 1)) ^ 2‖ ≤ 16 * ρ ^ 2 * exp (-(2 * α) * t) := by
    intro t ht
    have ht' : T' < t := ht
    have hTt : T ≤ t := (le_max_left _ _).trans ht'.le
    have hlog : Real.log 2 / α ≤ t := (le_max_right _ _).trans ht'.le
    have hXt := hX t hTt
    have hlog2 : Real.log 2 ≤ X t := by
      have : Real.log 2 ≤ α * t := by rwa [div_le_iff₀ hα, mul_comm] at hlog
      linarith
    have hx0 : 0 < X t := lt_of_lt_of_le (Real.log_pos (by norm_num)) hlog2
    have h0 : 0 ≤ cothHalf (X t) - 1 := by linarith [one_le_cothHalf hx0]
    have h1 := cothHalf_sub_one_le hlog2
    have h3 : exp (-X t) ≤ exp (-(α * t)) := exp_le_exp.2 (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
    have h4 : (cothHalf (X t) - 1) ^ 2 ≤ (4 * exp (-(α * t))) ^ 2 :=
      pow_le_pow_left₀ h0 (h1.trans (by linarith)) 2
    have h5 : (4 * exp (-(α * t))) ^ 2 = 16 * exp (-(2 * α) * t) := by
      rw [mul_pow, ← exp_nat_mul]; norm_num; ring_nf
    nlinarith [sq_nonneg ρ]
  have hint : IntegrableOn (fun t => 16 * ρ ^ 2 * exp (-(2 * α) * t)) (Ioi T') :=
    Integrable.const_mul (exp_neg_integrableOn_Ioi T' (by linarith : 0 < 2 * α)) _
  have hmeas : Measurable fun t => (ρ * (cothHalf (X t) - 1)) ^ 2 := by
    unfold cothHalf; fun_prop
  exact hint.mono' hmeas.aestronglyMeasurable (ae_restrict_of_forall_mem measurableSet_Ioi hbound)

end Sec4

end InteractingSLE
