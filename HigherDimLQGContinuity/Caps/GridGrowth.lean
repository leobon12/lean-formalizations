import HigherDimLQGContinuity.Caps.GridCount

/-!
# Exponential cardinal estimate for inspected grids (packet P4)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

/-- The inspected grid has at most a linear-in-`n` factor times its volume
growth. This is the count used in Lemma 2.2(a). -/
theorem p4_grid_card_growth {d : ℕ} {lam κ : ℝ} (hlam : 1 < lam) (hκ : 0 < κ) :
    ∃ A : ℝ, 0 < A ∧ ∀ {n : ℕ} {W : ℝ}, 1 ≤ n → 0 ≤ W →
      ((p4_gridPairsFinset d lam κ n W).card : ℝ) ≤
        A * n * ((1 + W) * Real.exp n) ^ d := by
  let q : ℝ := Real.log lam
  let b : ℝ := 2 / κ + 5
  let A : ℝ := (1 / q + 2) * b ^ d
  have hq : 0 < q := Real.log_pos hlam
  have hb : 0 < b := by dsimp [b]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro n W hn hW
  let M : ℕ := ⌈(n : ℝ) / q⌉₊ + 1
  let N : ℕ := ⌈(W + 1) / (κ * Real.exp (-(n : ℝ)))⌉₊ + 1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) ≤ n := by positivity
  have hW1 : 1 ≤ 1 + W := by linarith
  have he : 1 ≤ Real.exp (n : ℝ) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hnp
  have hM : (M : ℝ) ≤ (1 / q + 2) * n := by
    have hceil := Nat.ceil_lt_add_one (div_nonneg hnp hq.le)
    have hM' : (M : ℝ) < (n : ℝ) / q + 2 := by
      dsimp [M]
      push_cast
      linarith only [hceil]
    have hqeq : (n : ℝ) / q = (1 / q) * n := by ring
    have h2 : (2 : ℝ) ≤ 2 * n := by linarith only [hnR]
    rw [hqeq] at hM'
    nlinarith only [hM', h2]
  have hden : 0 < κ * Real.exp (-(n : ℝ)) := by positivity
  have hN : (2 * N + 1 : ℕ) ≤ b * ((1 + W) * Real.exp n) := by
    have hceil := Nat.ceil_lt_add_one (div_nonneg (by linarith : 0 ≤ W + 1) hden.le)
    have hinv : (W + 1) / (κ * Real.exp (-(n : ℝ))) =
        (W + 1) * Real.exp n / κ := by
      rw [Real.exp_neg]
      field_simp
    let P : ℝ := (1 + W) * Real.exp n
    have hprod : 1 ≤ P := by dsimp [P]; nlinarith only [hW1, he, hW, Real.exp_pos (n : ℝ)]
    have hlarge : (5 : ℝ) ≤ 5 * P := by nlinarith only [hprod]
    have hraw : (N : ℝ) < P * κ⁻¹ + 2 := by
      dsimp [N, P]
      push_cast
      rw [hinv, div_eq_mul_inv]
      rw [hinv, div_eq_mul_inv] at hceil
      linarith only [hceil]
    push_cast
    change (2 * (N : ℝ) + 1) ≤ b * P
    dsimp [b]
    rw [div_eq_mul_inv]
    nlinarith only [hraw, hlarge]
  have hcardN := card_p4_gridPairsFinset_le d lam κ n W
  have hcard : ((p4_gridPairsFinset d lam κ n W).card : ℝ) ≤
      (M : ℝ) * ((2 * N + 1 : ℕ) : ℝ) ^ d := by
    have hc : (p4_gridPairsFinset d lam κ n W).card ≤ M * (2 * N + 1) ^ d := by
      simpa only [M, N, q] using hcardN
    exact_mod_cast hc
  have hpow : (((2 * N + 1 : ℕ) : ℝ)) ^ d ≤
      (b * ((1 + W) * Real.exp n)) ^ d := by
    exact pow_le_pow_left₀ (by positivity) hN d
  calc
    ((p4_gridPairsFinset d lam κ n W).card : ℝ) ≤
        (M : ℝ) * (((2 * N + 1 : ℕ) : ℝ)) ^ d := hcard
    _ ≤ ((1 / q + 2) * n) * (b * ((1 + W) * Real.exp n)) ^ d := by
      gcongr
    _ = A * n * ((1 + W) * Real.exp n) ^ d := by
      dsimp [A]
      rw [mul_pow]
      ring

/-- The spatial-window hypothesis turns the grid count into exponential
growth in `n`, with a single prefactor. -/
theorem p4_grid_card_exp {d : ℕ} {lam κ c₀ : ℝ} (hlam : 1 < lam)
    (hκ : 0 < κ) (_hc₀ : 0 ≤ c₀) :
    ∃ A : ℝ, 0 < A ∧ ∀ {n : ℕ} {W : ℝ}, 1 ≤ n → 0 ≤ W →
      Real.log (1 + W) ≤ c₀ * n →
      ((p4_gridPairsFinset d lam κ n W).card : ℝ) ≤
        A * n * Real.exp ((d : ℝ) * (c₀ + 1) * n) := by
  obtain ⟨A, hA, hcard⟩ := p4_grid_card_growth (d := d) hlam hκ
  refine ⟨A, hA, ?_⟩
  intro n W hn hW hWlog
  have hWexp : 1 + W ≤ Real.exp (c₀ * n) := by
    calc
      1 + W = Real.exp (Real.log (1 + W)) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp (c₀ * n) := Real.exp_le_exp.mpr hWlog
  have hprod : (1 + W) * Real.exp n ≤ Real.exp ((c₀ + 1) * n) := by
    calc
      (1 + W) * Real.exp n ≤ Real.exp (c₀ * n) * Real.exp n :=
        mul_le_mul_of_nonneg_right hWexp (Real.exp_pos _).le
      _ = Real.exp ((c₀ + 1) * n) := by rw [← Real.exp_add]; congr 1; ring
  have hpow : ((1 + W) * Real.exp n) ^ d ≤
      Real.exp ((d : ℝ) * (c₀ + 1) * n) := by
    calc
      _ ≤ Real.exp ((c₀ + 1) * n) ^ d :=
        pow_le_pow_left₀ (by positivity) hprod d
      _ = Real.exp ((d : ℝ) * (c₀ + 1) * n) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  calc
    ((p4_gridPairsFinset d lam κ n W).card : ℝ) ≤
        A * n * ((1 + W) * Real.exp n) ^ d := hcard hn hW
    _ ≤ A * n * Real.exp ((d : ℝ) * (c₀ + 1) * n) := by gcongr

end HigherDimLQGContinuity
