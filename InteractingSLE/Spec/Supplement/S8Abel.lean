/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Supplement §8: Abel summation in the protected-tail estimate GB5 and the exhaustion GB9

Packet PROVE-SUPP8 (specification supplement §8.5, `source/spec/p481-528.md` L872–L924, pp. 516–518, and §8.9,
L1085–L1090, p. 526). The deterministic content of the proof of **Lemma GB5** and of the stage-independent drift
bound in **Theorem GB9**.

## GB5

Right coordinates `V₁ ≤ ⋯ ≤ V_N` of a one-sided force evolution, `X_i = V_i − W > 0` (so `X` is nondecreasing),
weights `ρ_i`, partial sums `S_i = Σ_{ℓ ≤ i} ρ_ℓ`, a special index `j`, `s = S_{j−1}`, `U_i = X_i/X_j`, and the new
clock `du = dt/X_j²`. The source defines

  `A = X_j Σ_{i ≥ j} ρ_i/X_i − (c − s)`, `E = Σ_{i<j} ρ_i (1/U_i − 1)`, `H = E + 2(1/U₁ − 1)`.

* `gb5_A_bounds`: summation by parts in the outer group (partial sums relative to `s` at least `c − s`) gives
  `0 ≤ A ≤ Σ_{i ≥ j} |ρ_i| + |c − s|`;
* `gb5_E_eq`, `gb5_H_eq`: `E = Σ_{i<j} S_i (1/U_i − 1/U_{i+1})`, `H = Σ_{i<j} (S_i + 2)(1/U_i − 1/U_{i+1})`;
* `gb5_H_ge`, `gb5_abs_E_le`: `H ≥ ε (1/U₁ − 1) ≥ 0` for `ε ≤ min (S_i + 2)` and `|E| ≤ max |S_i| (1/U₁ − 1)`;
* the drift algebra behind the four Itô identities: `gb5_drift_logX` (`2 + X_j Σ_i ρ_i/X_i − k/2 = E + A`, the
  drift of `log X_j` in the new clock), `gb5_gap_rate` (`d log(V_j − V₁) = −(2/U₁) du`), `gb5_drift_logZ`
  (`−2/U₁ − (E + A) = −(2 + A + H)`), `gb5_drift_U` (the drift of `U₁ = 1 − Z`), and `gb5_inv_eq`
  (`U⁻¹ = (1 − U)²/U + 2 − U`).

## GB9

`gb9_abel_abs_le`: if the reciprocal gaps `r_i` decrease outward, are nonnegative and at most `R`, and the partial
sums of the weights have modulus at most `M`, then `|Σ ρ_i r_i| ≤ M R`; with gaps at least `3/4` this is the bound
`4M/3` per side (`8M/3` for both sides), and the initial labels contribute at most `(4/3) Σ |ρ_i|`
(`gb9_initial_le`).

The basic identity is Abel's summation `Σ_{i<n} a_i (f_i − f_n) = Σ_{i<n} (Σ_{ℓ ≤ i} a_ℓ)(f_i − f_{i+1})`
(`abel_sum`).
-/

set_option autoImplicit false

open Finset

namespace InteractingSLE

namespace Supp8

/-! ### Abel summation -/

/-- **Abel summation**: `Σ_{i<n} a_i (f_i − f_n) = Σ_{i<n} (Σ_{ℓ ≤ i} a_ℓ)(f_i − f_{i+1})`. -/
theorem abel_sum (a f : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range n, a i * (f i - f n) =
      ∑ i ∈ range n, (∑ l ∈ range (i + 1), a l) * (f i - f (i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : ∑ i ∈ range n, a i * (f i - f (n + 1)) =
        ∑ i ∈ range n, a i * (f i - f n) + (∑ i ∈ range n, a i) * (f n - f (n + 1)) := by
      rw [sum_mul, ← sum_add_distrib]
      exact sum_congr rfl fun i _ => by ring
    rw [sum_range_succ, h, ih, sum_range_succ _ n, sum_range_succ a n]
    ring

/-- Telescoping of the Abel coefficients. -/
theorem sum_sub_succ (f : ℕ → ℝ) (n : ℕ) : ∑ i ∈ range n, (f i - f (i + 1)) = f 0 - f n :=
  sum_range_sub' f n

/-- Abel lower bound: if `f` is nonincreasing on `[0, n]` and every partial sum is at least `L`, then
`L (f₀ − f_n) ≤ Σ_{i<n} a_i (f_i − f_n)`. -/
theorem abel_lower {a f : ℕ → ℝ} {n : ℕ} {L : ℝ} (hf : ∀ i < n, f (i + 1) ≤ f i)
    (hS : ∀ i < n, L ≤ ∑ l ∈ range (i + 1), a l) :
    L * (f 0 - f n) ≤ ∑ i ∈ range n, a i * (f i - f n) := by
  rw [abel_sum, ← sum_sub_succ, mul_sum]
  refine sum_le_sum fun i hi => ?_
  have hi' := mem_range.1 hi
  exact mul_le_mul_of_nonneg_right (hS i hi') (sub_nonneg.2 (hf i hi'))

/-- Abel upper bound: if `f` is nonincreasing on `[0, n]` and every partial sum is at most `M`, then
`Σ_{i<n} a_i (f_i − f_n) ≤ M (f₀ − f_n)`. -/
theorem abel_upper {a f : ℕ → ℝ} {n : ℕ} {M : ℝ} (hf : ∀ i < n, f (i + 1) ≤ f i)
    (hS : ∀ i < n, ∑ l ∈ range (i + 1), a l ≤ M) :
    ∑ i ∈ range n, a i * (f i - f n) ≤ M * (f 0 - f n) := by
  rw [abel_sum, ← sum_sub_succ, mul_sum]
  refine sum_le_sum fun i hi => ?_
  have hi' := mem_range.1 hi
  exact mul_le_mul_of_nonneg_right (hS i hi') (sub_nonneg.2 (hf i hi'))

/-- Abel bound in modulus: `|Σ_{i<n} a_i (f_i − f_n)| ≤ M (f₀ − f_n)` when all partial sums have modulus `≤ M`. -/
theorem abel_abs_le {a f : ℕ → ℝ} {n : ℕ} {M : ℝ} (hf : ∀ i < n, f (i + 1) ≤ f i)
    (hS : ∀ i < n, |∑ l ∈ range (i + 1), a l| ≤ M) :
    |∑ i ∈ range n, a i * (f i - f n)| ≤ M * (f 0 - f n) := by
  have h1 := abel_lower (L := -M) hf fun i hi => (abs_le.1 (hS i hi)).1
  have h2 := abel_upper (M := M) hf fun i hi => (abs_le.1 (hS i hi)).2
  rw [abs_le]
  constructor <;> linarith

/-! ### Sequences ending at zero -/

/-- The sequence `r` truncated to `0` from index `n` on. -/
def truncZero (r : ℕ → ℝ) (n : ℕ) (i : ℕ) : ℝ := if i < n then r i else 0

theorem truncZero_antitone {r : ℕ → ℝ} {n : ℕ} (hr : ∀ i, i + 1 < n → r (i + 1) ≤ r i)
    (hr0 : ∀ i < n, 0 ≤ r i) : ∀ i < n, truncZero r n (i + 1) ≤ truncZero r n i := by
  intro i hi
  simp only [truncZero, ite_eq_left hi]
  split_ifs with h
  · exact hr i h
  · exact hr0 i hi

theorem sum_mul_truncZero (ρ r : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range n, ρ i * (truncZero r n i - truncZero r n n) = ∑ i ∈ range n, ρ i * r i := by
  refine sum_congr rfl fun i hi => ?_
  simp [truncZero, mem_range.1 hi]

/-- Abel lower bound for a nonnegative nonincreasing sequence: `L r₀ ≤ Σ_{i<n} ρ_i r_i` when every partial sum is at
least `L` (`n > 0`). -/
theorem abel_lower_of_antitone {ρ r : ℕ → ℝ} {n : ℕ} (hn : 0 < n) {L : ℝ}
    (hr : ∀ i, i + 1 < n → r (i + 1) ≤ r i) (hr0 : ∀ i < n, 0 ≤ r i)
    (hS : ∀ i < n, L ≤ ∑ l ∈ range (i + 1), ρ l) :
    L * r 0 ≤ ∑ i ∈ range n, ρ i * r i := by
  have h := abel_lower (a := ρ) (truncZero_antitone hr hr0) hS
  rw [sum_mul_truncZero] at h
  simpa [truncZero, hn] using h

/-- **GB9**, Abel bound: `|Σ_{i<n} ρ_i r_i| ≤ M r₀` for nonnegative nonincreasing `r` and partial sums of modulus at
most `M` (`n > 0`). -/
theorem gb9_abel_abs_le {ρ r : ℕ → ℝ} {n : ℕ} (hn : 0 < n) {M : ℝ}
    (hr : ∀ i, i + 1 < n → r (i + 1) ≤ r i) (hr0 : ∀ i < n, 0 ≤ r i)
    (hS : ∀ i < n, |∑ l ∈ range (i + 1), ρ l| ≤ M) :
    |∑ i ∈ range n, ρ i * r i| ≤ M * r 0 := by
  have h := abel_abs_le (a := ρ) (truncZero_antitone hr hr0) hS
  rw [sum_mul_truncZero] at h
  simpa [truncZero, hn] using h

/-- **GB9**, one side of the stage-independent drift bound: gaps `g_i ≥ 3/4` increasing outward and angle-change
partial sums of modulus at most `M ≥ 0` give `|Σ ρ_i/g_i| ≤ 4M/3`. -/
theorem gb9_side_drift_le {ρ g : ℕ → ℝ} {n : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (hg : ∀ i < n, 3 / 4 ≤ g i) (hmono : ∀ i, i + 1 < n → g i ≤ g (i + 1))
    (hS : ∀ i < n, |∑ l ∈ range (i + 1), ρ l| ≤ M) :
    |∑ i ∈ range n, ρ i * (1 / g i)| ≤ 4 * M / 3 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp; positivity
  have hgpos : ∀ i < n, 0 < g i := fun i hi => lt_of_lt_of_le (by norm_num) (hg i hi)
  have h := gb9_abel_abs_le (ρ := ρ) (r := fun i => 1 / g i) hn
    (fun i hi => one_div_le_one_div_of_le (hgpos i (by omega)) (hmono i hi))
    (fun i hi => (one_div_pos.2 (hgpos i hi)).le) hS
  refine h.trans ?_
  have h0 : 1 / g 0 ≤ 4 / 3 := by
    rw [div_le_iff₀ (hgpos 0 hn)]; linarith [hg 0 hn]
  calc M * (1 / g 0) ≤ M * (4 / 3) := mul_le_mul_of_nonneg_left h0 hM
    _ = 4 * M / 3 := by ring

/-- **GB9**: both sides together contribute at most `8M/3`. -/
theorem gb9_two_sides_le {a b M : ℝ} (ha : |a| ≤ 4 * M / 3) (hb : |b| ≤ 4 * M / 3) : |a + b| ≤ 8 * M / 3 :=
  (abs_add_le a b).trans (by linarith)

/-- **GB9**: the finitely many initial labels, each at distance at least `3/4`, contribute at most
`(4/3) Σ |ρ_i|`. -/
theorem gb9_initial_le {ρ g : ℕ → ℝ} {n : ℕ} (hg : ∀ i < n, 3 / 4 ≤ |g i|) :
    |∑ i ∈ range n, ρ i / g i| ≤ 4 / 3 * ∑ i ∈ range n, |ρ i| := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [mul_sum]
  refine sum_le_sum fun i hi => ?_
  have hgi := hg i (mem_range.1 hi)
  have hpos : 0 < |g i| := lt_of_lt_of_le (by norm_num) hgi
  rw [abs_div, div_le_iff₀ hpos]
  nlinarith [abs_nonneg (ρ i)]

/-! ### GB5: the quantities `A`, `E`, `H` -/

/-- **GB5**, the outer group: with `X` positive and nondecreasing on the outer marks `0, …, n − 1` (source indices
`j, …, N`) and every outer partial sum (relative to `s`) at least `L = c − s`,
`0 ≤ A = X₀ Σ_{i<n} ρ_i/X_i − L ≤ Σ_{i<n} |ρ_i| + |L|`. -/
theorem gb5_A_bounds {ρ X : ℕ → ℝ} {n : ℕ} (hn : 0 < n) (hX : ∀ i < n, 0 < X i)
    (hmono : ∀ i, i + 1 < n → X i ≤ X (i + 1)) {L : ℝ}
    (hS : ∀ i < n, L ≤ ∑ l ∈ range (i + 1), ρ l) :
    0 ≤ X 0 * ∑ i ∈ range n, ρ i / X i - L ∧
      X 0 * ∑ i ∈ range n, ρ i / X i - L ≤ ∑ i ∈ range n, |ρ i| + |L| := by
  have hX0 := hX 0 hn
  have hle : ∀ i < n, X 0 ≤ X i := by
    intro i hi
    induction i with
    | zero => exact le_rfl
    | succ i ih => exact (ih (by omega)).trans (hmono i hi)
  have hsum : X 0 * ∑ i ∈ range n, ρ i / X i = ∑ i ∈ range n, ρ i * (X 0 / X i) := by
    rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
  have hr1 : ∀ i < n, X 0 / X i ≤ 1 := fun i hi => (div_le_one (hX i hi)).2 (hle i hi)
  have hr0 : ∀ i < n, 0 ≤ X 0 / X i := fun i hi => (div_pos hX0 (hX i hi)).le
  have hlow := abel_lower_of_antitone (ρ := ρ) (r := fun i => X 0 / X i) hn
    (fun i hi => div_le_div_of_nonneg_left hX0.le (hX i (by omega)) (hmono i hi)) hr0 hS
  simp only [div_self hX0.ne', mul_one] at hlow
  rw [hsum]
  refine ⟨by linarith, ?_⟩
  have hup : ∑ i ∈ range n, ρ i * (X 0 / X i) ≤ ∑ i ∈ range n, |ρ i| := by
    refine sum_le_sum fun i hi => ?_
    have hi' := mem_range.1 hi
    calc ρ i * (X 0 / X i) ≤ |ρ i| * (X 0 / X i) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (hr0 i hi')
      _ ≤ |ρ i| * 1 := mul_le_mul_of_nonneg_left (hr1 i hi') (abs_nonneg _)
      _ = |ρ i| := mul_one _
  linarith [neg_abs_le L]

/-- **GB5**, the inner group (indices `0, …, n − 1`, source `1, …, j − 1`, with `U_n = U_j = 1`):
`E = Σ_{i<n} ρ_i (1/U_i − 1) = Σ_{i<n} S_i (1/U_i − 1/U_{i+1})`. -/
theorem gb5_E_eq (ρ U : ℕ → ℝ) (n : ℕ) (hUn : U n = 1) :
    ∑ i ∈ range n, ρ i * (1 / U i - 1) =
      ∑ i ∈ range n, (∑ l ∈ range (i + 1), ρ l) * (1 / U i - 1 / U (i + 1)) := by
  have h := abel_sum ρ (fun i => 1 / U i) n
  simp only [hUn, div_one] at h
  exact h

/-- **GB5**: `H = E + 2(1/U₁ − 1) = Σ_{i<n} (S_i + 2)(1/U_i − 1/U_{i+1})`. -/
theorem gb5_H_eq (ρ U : ℕ → ℝ) (n : ℕ) (hUn : U n = 1) :
    ∑ i ∈ range n, ρ i * (1 / U i - 1) + 2 * (1 / U 0 - 1) =
      ∑ i ∈ range n, (∑ l ∈ range (i + 1), ρ l + 2) * (1 / U i - 1 / U (i + 1)) := by
  rw [gb5_E_eq ρ U n hUn]
  have ht := sum_sub_succ (fun i => 1 / U i) n
  simp only [hUn, div_one] at ht
  rw [← ht, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun i _ => by ring

/-- **GB5**: with `U` positive and nondecreasing up to `U_n = 1` and `S_i + 2 ≥ ε` (admissibility),
`H ≥ ε (1/U₁ − 1)`. -/
theorem gb5_H_ge {ρ U : ℕ → ℝ} {n : ℕ} (hUn : U n = 1) (hU : ∀ i ≤ n, 0 < U i)
    (hmono : ∀ i < n, U i ≤ U (i + 1)) {ε : ℝ} (hε : ∀ i < n, ε ≤ ∑ l ∈ range (i + 1), ρ l + 2) :
    ε * (1 / U 0 - 1) ≤ ∑ i ∈ range n, ρ i * (1 / U i - 1) + 2 * (1 / U 0 - 1) := by
  rw [gb5_H_eq ρ U n hUn]
  have ht := sum_sub_succ (fun i => 1 / U i) n
  simp only [hUn, div_one] at ht
  rw [← ht, mul_sum]
  refine sum_le_sum fun i hi => ?_
  have hi' := mem_range.1 hi
  exact mul_le_mul_of_nonneg_right (hε i hi')
    (sub_nonneg.2 (one_div_le_one_div_of_le (hU i hi'.le) (hmono i hi')))

/-- **GB5**: `|E| ≤ max_i |S_i| (1/U₁ − 1)`. -/
theorem gb5_abs_E_le {ρ U : ℕ → ℝ} {n : ℕ} (hUn : U n = 1) (hU : ∀ i ≤ n, 0 < U i)
    (hmono : ∀ i < n, U i ≤ U (i + 1)) {M : ℝ} (hM : ∀ i < n, |∑ l ∈ range (i + 1), ρ l| ≤ M) :
    |∑ i ∈ range n, ρ i * (1 / U i - 1)| ≤ M * (1 / U 0 - 1) := by
  have hf : ∀ i < n, 1 / U (i + 1) ≤ 1 / U i := fun i hi =>
    one_div_le_one_div_of_le (hU i hi.le) (hmono i hi)
  have h := abel_abs_le (a := ρ) (f := fun i => 1 / U i) hf hM
  simp only [hUn, div_one] at h
  exact h

/-! ### GB5: the drift algebra -/

/-- **GB5**, drift of `log X_j` in the new clock: for nonzero gaps `X_i`, `s = Σ_{i<j} ρ_i`, `c = k/2 − 2`,
`2 + X_j Σ_{i<N} ρ_i/X_i − k/2 = E + A` with `E = Σ_{i<j} ρ_i (X_j/X_i − 1)` and
`A = X_j Σ_{j ≤ i < N} ρ_i/X_i − (c − s)`. -/
theorem gb5_drift_logX (ρ X : ℕ → ℝ) {j N : ℕ} (hjN : j ≤ N) (k : ℝ) :
    2 + X j * ∑ i ∈ range N, ρ i / X i - k / 2 =
      ∑ i ∈ range j, ρ i * (X j / X i - 1) +
        (X j * ∑ i ∈ Ico j N, ρ i / X i - ((k / 2 - 2) - ∑ i ∈ range j, ρ i)) := by
  rw [← sum_range_add_sum_Ico _ hjN, mul_add]
  have : ∑ i ∈ range j, ρ i * (X j / X i - 1) = X j * ∑ i ∈ range j, ρ i / X i - ∑ i ∈ range j, ρ i := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [this]
  ring

/-- **GB5**: the coordinate gap of two right marks moves at the rate
`(2/X_j − 2/X₁)/(X_j − X₁) = −2/(X₁ X_j) = −(2/U₁)/X_j²`, i.e. `d log(V_j − V₁) = −(2/U₁) du`. -/
theorem gb5_gap_rate {X₁ Xj : ℝ} (h₁ : X₁ ≠ 0) (hj : Xj ≠ 0) (hne : Xj ≠ X₁) :
    (2 / Xj - 2 / X₁) / (Xj - X₁) = -(2 / (X₁ / Xj)) / Xj ^ 2 := by
  have : Xj - X₁ ≠ 0 := sub_ne_zero.2 hne
  field_simp
  ring

/-- **GB5**: the drift of `log Z = log(V_j − V₁) − log X_j`: `−2/U₁ − (E + A) = −(2 + A + H)` with
`H = E + 2(1/U₁ − 1)`. -/
theorem gb5_drift_logZ (U E A : ℝ) : -(2 / U) - (E + A) = -(2 + A + (E + 2 * (1 / U - 1))) := by ring

/-- **GB5**: the drift of `U₁ = 1 − Z`: `−Z · (−(2 + A + H)) − (k/2) Z = (1 − U₁)(−c + A + H)` with
`Z = 1 − U₁`, `c = k/2 − 2`. -/
theorem gb5_drift_U (U A H k : ℝ) :
    -(1 - U) * (-(2 + A + H)) - k / 2 * (1 - U) = (1 - U) * (-(k / 2 - 2) + A + H) := by ring

/-- **GB5**: `U⁻¹ = (1 − U)²/U + 2 − U`, which turns `∫ (1 − U₁)²/U₁ < ∞` into `∫ 1/U₁ < ∞`. -/
theorem gb5_inv_eq {U : ℝ} (hU : U ≠ 0) : U⁻¹ = (1 - U) ^ 2 / U + 2 - U := by
  field_simp
  ring

end Supp8

end InteractingSLE
