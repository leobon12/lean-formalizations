import InteractingSLE.SLE8.Counting.Selection

/-!
# Real-number estimates for the proof of Proposition 4.1

SLE₈ note `source/sle8-continuity.pdf`, §4, pp. 8–10 (anchor `prop-4.1-proof`): the arithmetic behind
"for all sufficiently large `n`" and the summability of (4.13) and (4.25), with `N = 2ⁿ`, `r = N^δ`,
`a = exp(-r/n²)` (`bigN`, `scaleR`, `levelA`).

## Main results

* `eventually_linear_le_scaleR`: `r = N^δ` eventually dominates every affine function of `n`;
* `summable_bigN_pow_mul_exp`: `Σ_n N^p e^{-c r} < ∞`;
* `sum_box_le`: the `m`-sum of the two-point bound (3.11) over a dyadic box row ((4.12)–(4.13));
* `eventually_selectionParams`: the parameter inequalities of Steps 1–3 hold for all large `n`.
-/

noncomputable section

open Set Filter Finset
open scoped Topology

namespace InteractingSLE.SLE8

theorem scaleR_eq (δ : ℝ) (n : ℕ) : scaleR δ n = Real.exp (δ * (n * Real.log 2)) := by
  rw [scaleR, bigN, Real.rpow_def_of_pos (by positivity), Real.log_pow]; ring_nf

theorem scaleR_pos (δ : ℝ) (n : ℕ) : 0 < scaleR δ n := by rw [scaleR_eq]; exact Real.exp_pos _

theorem bigN_pow_eq (p n : ℕ) : bigN n ^ p = Real.exp (p * (n * Real.log 2)) := by
  rw [bigN, ← pow_mul, ← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
  push_cast; ring_nf

theorem one_le_bigN (n : ℕ) : 1 ≤ bigN n := one_le_pow₀ (by norm_num)

/-- `r = N^δ` eventually dominates every affine function of `n`. -/
theorem eventually_linear_le_scaleR {δ : ℝ} (hδ : 0 < δ) (A B : ℝ) :
    ∀ᶠ n : ℕ in atTop, A * n + B ≤ scaleR δ n := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set c := (δ * Real.log 2) ^ 2 / 2 with hc
  have hc0 : 0 < c := by positivity
  filter_upwards [eventually_ge_atTop ⌈(|A| + |B|) / c⌉₊, eventually_ge_atTop 1] with n hn hn1
  have hn' : (|A| + |B|) / c ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hx : 0 ≤ δ * (n * Real.log 2) := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg hx
  rw [scaleR_eq]
  have h1 : c * n ^ 2 ≤ Real.exp (δ * (n * Real.log 2)) := by
    have : c * n ^ 2 = (δ * (n * Real.log 2)) ^ 2 / 2 := by rw [hc]; ring
    rw [this]; linarith
  have h2 : |A| + |B| ≤ c * n := by rwa [div_le_iff₀ hc0, mul_comm] at hn'
  have h3 : A * n + B ≤ (|A| + |B|) * n := by
    have h4 : A * n ≤ |A| * n := mul_le_mul_of_nonneg_right (le_abs_self A) (by linarith)
    have h5 : B ≤ |B| * n := (le_abs_self B).trans (le_mul_of_one_le_right (abs_nonneg B) hn1')
    linarith
  have h6 : (|A| + |B|) * n ≤ c * n * n := mul_le_mul_of_nonneg_right h2 (by linarith)
  nlinarith

theorem tendsto_scaleR {δ : ℝ} (hδ : 0 < δ) : Tendsto (scaleR δ) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [eventually_linear_le_scaleR hδ 0 b] with n hn
  linarith

/-- **Summability.** `Σ_n N^p e^{-c r} < ∞` for `c, δ > 0`. -/
theorem summable_bigN_pow_mul_exp (p : ℕ) {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    Summable fun n : ℕ => bigN n ^ p * Real.exp (-(c * scaleR δ n)) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine Summable.of_norm_bounded_eventually_nat (g := fun n : ℕ => (1 / 2 : ℝ) ^ n)
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)) ?_
  filter_upwards [eventually_linear_le_scaleR hδ ((p + 1) * Real.log 2 / c) 0] with n hn
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (bigN_pos n).le p) (Real.exp_pos _).le),
    bigN_pow_eq, ← Real.exp_add]
  have hhalf : (1 / 2 : ℝ) ^ n = Real.exp (-(n * Real.log 2)) := by
    rw [one_div, inv_pow, ← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ n), ← Real.exp_neg,
      Real.log_pow]
  rw [hhalf, Real.exp_le_exp]
  have : (p + 1) * Real.log 2 * n ≤ c * scaleR δ n := by
    have h := mul_le_mul_of_nonneg_left hn hc.le
    rw [add_zero, ← mul_assoc, mul_div_cancel₀ _ hc.ne'] at h
    linarith
  nlinarith

/-- **(4.12)–(4.13), one row of boxes.** For `d ∈ ℕ`, `ρ ≥ 1` and `0 ≤ R ≤ ρ 2^d`:
`Σ_{|m| ≤ R} (2^{-d})^{16/9} (1 + m²)^{1/3} ≤ 6 ρ³ 2^{-d/9}`. -/
theorem sum_box_le {d : ℕ} {ρ : ℝ} (hρ : 1 ≤ ρ) {R : ℤ} (hR0 : 0 ≤ R)
    (hR : (R : ℝ) ≤ ρ * 2 ^ d) :
    ∑ m ∈ Finset.Icc (-R) R, ((2 : ℝ) ^ (-(d : ℝ))) ^ (16 / 9 : ℝ) * (1 + (m : ℝ) ^ 2) ^ (1 / 3 : ℝ) ≤
      6 * ρ ^ 3 * (2 : ℝ) ^ (-(d : ℝ) / 9) := by
  have h2d : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
  have hR0' : (0 : ℝ) ≤ R := by exact_mod_cast hR0
  have hterm : ∀ m ∈ Finset.Icc (-R) R,
      ((2 : ℝ) ^ (-(d : ℝ))) ^ (16 / 9 : ℝ) * (1 + (m : ℝ) ^ 2) ^ (1 / 3 : ℝ) ≤
        ((2 : ℝ) ^ (-(d : ℝ))) ^ (16 / 9 : ℝ) * (1 + (R : ℝ) ^ 2) ^ (1 / 3 : ℝ) := by
    intro m hm
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hm
    have h1' : -(R : ℝ) ≤ m := by exact_mod_cast h1
    have h2' : (m : ℝ) ≤ R := by exact_mod_cast h2
    have hsq : (m : ℝ) ^ 2 ≤ (R : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.2 h2') (show (0 : ℝ) ≤ R + m by linarith)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by linarith)
      (by norm_num)) (by positivity)
  have hcard : ((Finset.Icc (-R) R).card : ℝ) = 2 * R + 1 := by
    rw [Int.card_Icc]
    have : R + 1 - -R = 2 * R + 1 := by ring
    rw [this, ← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    push_cast; ring
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, nsmul_eq_mul, hcard] at hsum
  refine hsum.trans ?_
  -- the powers of two
  have hA : ((2 : ℝ) ^ (-(d : ℝ))) ^ (16 / 9 : ℝ) = (2 : ℝ) ^ (-(d : ℝ) * (16 / 9)) := by
    rw [← Real.rpow_mul (by norm_num)]
  have hB : (1 + (R : ℝ) ^ 2) ^ (1 / 3 : ℝ) ≤ (2 * ρ ^ 2) * (2 : ℝ) ^ ((d : ℝ) * (2 / 3)) := by
    have hle : 1 + (R : ℝ) ^ 2 ≤ (2 * ρ ^ 2) * (2 : ℝ) ^ ((2 * d : ℕ) : ℝ) := by
      rw [Real.rpow_natCast, pow_mul]
      have : (1 : ℝ) ≤ ρ ^ 2 * (2 ^ 2) ^ d := by
        have := one_le_pow₀ (M₀ := ℝ) (n := d) (show (1 : ℝ) ≤ 2 ^ 2 by norm_num)
        nlinarith
      have hR2 : (R : ℝ) ^ 2 ≤ ρ ^ 2 * (2 ^ 2) ^ d := by
        rw [← pow_mul, mul_comm 2 d, pow_mul, ← mul_pow]
        exact pow_le_pow_left₀ hR0' hR 2
      nlinarith
    calc (1 + (R : ℝ) ^ 2) ^ (1 / 3 : ℝ)
        ≤ ((2 * ρ ^ 2) * (2 : ℝ) ^ ((2 * d : ℕ) : ℝ)) ^ (1 / 3 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hle (by norm_num)
      _ = (2 * ρ ^ 2) ^ (1 / 3 : ℝ) * (2 : ℝ) ^ ((d : ℝ) * (2 / 3)) := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by norm_num)]
          push_cast; ring_nf
      _ ≤ (2 * ρ ^ 2) * (2 : ℝ) ^ ((d : ℝ) * (2 / 3)) := by
          gcongr
          exact Real.rpow_le_self_of_one_le (by nlinarith) (by norm_num)
  have hC : (2 * (R : ℝ) + 1) ≤ 3 * ρ * (2 : ℝ) ^ (d : ℝ) := by
    rw [Real.rpow_natCast]; nlinarith
  have hpow : (2 : ℝ) ^ (d : ℝ) * (2 : ℝ) ^ (-(d : ℝ) * (16 / 9)) * (2 : ℝ) ^ ((d : ℝ) * (2 / 3)) =
      (2 : ℝ) ^ (-(d : ℝ) / 9) := by
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
    ring_nf
  calc (2 * (R : ℝ) + 1) * (((2 : ℝ) ^ (-(d : ℝ))) ^ (16 / 9 : ℝ) * (1 + (R : ℝ) ^ 2) ^ (1 / 3 : ℝ))
      ≤ (3 * ρ * (2 : ℝ) ^ (d : ℝ)) * ((2 : ℝ) ^ (-(d : ℝ) * (16 / 9)) *
          ((2 * ρ ^ 2) * (2 : ℝ) ^ ((d : ℝ) * (2 / 3)))) := by
        rw [hA]; gcongr
    _ = 6 * ρ ^ 3 * ((2 : ℝ) ^ (d : ℝ) * (2 : ℝ) ^ (-(d : ℝ) * (16 / 9)) *
          (2 : ℝ) ^ ((d : ℝ) * (2 / 3))) := by ring
    _ = 6 * ρ ^ 3 * (2 : ℝ) ^ (-(d : ℝ) / 9) := by rw [hpow]

/-! ## The parameter inequalities hold for all large `n` -/

theorem log_two_ge_half : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have := Real.log_two_gt_d9; linarith

theorem log_sqrt_five_le_one : Real.log (Real.sqrt 5) ≤ 1 := by
  rw [Real.log_sqrt (by norm_num)]
  have h : Real.log 5 < 2 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have := Real.exp_one_gt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith
  linarith

theorem log_sqrt_five_nonneg : 0 ≤ Real.log (Real.sqrt 5) :=
  Real.log_nonneg (by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num)

theorem log_bigN (n : ℕ) : Real.log (bigN n) = n * Real.log 2 := by
  rw [bigN, Real.log_pow]

theorem sqrt_bigN_le (n : ℕ) : Real.sqrt (bigN n) ≤ bigN n := by
  have h1 := one_le_bigN n
  rw [Real.sqrt_le_left (by linarith)]; nlinarith

/-- `r⁵ ≤ √N` for `δ ≤ 1/10`. -/
theorem scaleR_pow_five_le {δ : ℝ} (hδ1 : δ ≤ 1 / 10) (n : ℕ) :
    scaleR δ n ^ 5 ≤ Real.sqrt (bigN n) := by
  rw [scaleR, ← Real.rpow_natCast, ← Real.rpow_mul (bigN_pos n).le, Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le (one_le_bigN n) (by push_cast; linarith)

/-- **The parameter inequalities of Steps 1–3 hold for all large `n`** (for `δ ∈ (0, 1/10)`). -/
theorem eventually_selectionParams {M Cocc δ : ℝ} (hM : 0 ≤ M) (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 10) : ∀ᶠ n : ℕ in atTop, SelectionParams M Cocc δ n := by
  have hl2 := log_two_ge_half
  have hl5 := log_sqrt_five_le_one
  filter_upwards [eventually_linear_le_scaleR hδ0 0 5,
    eventually_linear_le_scaleR hδ0 (Real.log 2) (Real.log (8 * M + 1)),
    eventually_linear_le_scaleR hδ0 0 (2 * |Cocc|),
    eventually_ge_atTop (⌈2 * |Cocc|⌉₊ + 1), eventually_ge_atTop 6] with n h5 hlin hCocc hn hn6
  simp only [zero_mul, zero_add] at h5 hCocc
  set r := scaleR δ n with hr
  set N := bigN n with hN
  have hN1 : 1 ≤ N := one_le_bigN n
  have hr0 : 0 < r := scaleR_pos δ n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  refine ⟨by linarith, ?_, ?_, ?_, ?_⟩
  · -- hL1
    have hsq := sqrt_bigN_le n
    have he : 1 ≤ Real.exp r := Real.one_le_exp hr0.le
    have h1 : 2 * (4 * M * Real.sqrt N * Real.exp r) + 1 ≤ ((8 * M + 1) * N) * Real.exp r := by
      have : 8 * M * Real.sqrt N ≤ 8 * M * N := by gcongr
      nlinarith
    have h2 : Real.log (((8 * M + 1) * N) * Real.exp r) = Real.log (8 * M + 1) + n * Real.log 2 + r := by
      rw [Real.log_mul (by positivity) (Real.exp_pos r).ne', Real.log_exp,
        Real.log_mul (by positivity) (by positivity), hN, log_bigN]
    calc Real.log (2 * (4 * M * Real.sqrt N * Real.exp r) + 1)
        ≤ Real.log (((8 * M + 1) * N) * Real.exp r) := Real.log_le_log (by positivity) h1
      _ = Real.log (8 * M + 1) + n * Real.log 2 + r := h2
      _ ≤ 2 * r := by linarith
  · -- hL2
    have hceil : (⌈r⌉₊ : ℝ) - 1 ≤ r := by linarith [Nat.ceil_lt_add_one hr0.le]
    have hceil0 : 0 ≤ (⌈r⌉₊ : ℝ) - 1 := by
      have : 1 ≤ ⌈r⌉₊ := Nat.one_le_iff_ne_zero.2 (by rw [Ne, Nat.ceil_eq_zero]; linarith)
      have : (1 : ℝ) ≤ ⌈r⌉₊ := by exact_mod_cast this
      linarith
    have hX : (2 * r ^ 5 + r + Real.log (Real.sqrt 5)) / Real.log 2 + 1 ≤ 5 * r ^ 5 := by
      have hpos : 0 < Real.log 2 := by linarith
      have h1 : (2 * r ^ 5 + r + Real.log (Real.sqrt 5)) / Real.log 2 ≤
          2 * (2 * r ^ 5 + r + Real.log (Real.sqrt 5)) := by
        rw [div_le_iff₀ hpos]
        have : 0 ≤ 2 * r ^ 5 + r + Real.log (Real.sqrt 5) := by
          have := log_sqrt_five_nonneg; positivity
        nlinarith
      have h2 : 2 * r + 3 ≤ r ^ 5 := by
        have h4 : (5 : ℝ) ^ 4 ≤ r ^ 4 := pow_le_pow_left₀ (by norm_num) h5 4
        have : r ^ 5 = r * r ^ 4 := by ring
        nlinarith
      linarith
    calc ((⌈r⌉₊ : ℝ) - 1) * ((2 * r ^ 5 + r + Real.log (Real.sqrt 5)) / Real.log 2 + 1)
        ≤ r * (5 * r ^ 5) := mul_le_mul hceil hX (by
          have := log_sqrt_five_nonneg; have : 0 < Real.log 2 := by linarith
          positivity) hr0.le
      _ = 5 * r ^ 6 := by ring
      _ ≤ r * r ^ 6 := by gcongr
      _ = r ^ 7 := by ring
  · -- hL3
    have hr5 := scaleR_pow_five_le hδ1.le n
    have hrr5 : r ≤ r ^ 5 := le_self_pow₀ (by linarith) (by norm_num)
    have hrn : r / (n : ℝ) ^ 2 ≤ r := div_le_self hr0.le (by nlinarith)
    have hsqN : 7 ≤ Real.sqrt N := by
      rw [Real.le_sqrt (by norm_num) (by linarith), hN, bigN]
      calc (7 : ℝ) ^ 2 ≤ 2 ^ 6 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn6
    have hNsq : N = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt (by linarith)).symm
    have : N * (1 / 2) ≤ N * Real.log 2 := mul_le_mul_of_nonneg_left hl2 (by linarith)
    nlinarith
  · -- hL4
    rcases le_or_gt Cocc 0 with hC | hC
    · have : Cocc * (1 + r / (n : ℝ) ^ 2) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hC (by positivity)
      linarith
    · rw [abs_of_pos hC] at hCocc hn
      have hn2 : 2 * Cocc ≤ (n : ℝ) ^ 2 := by
        have : 2 * Cocc ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈2 * Cocc⌉₊ ≤ n by omega))
        nlinarith
      have : Cocc * (r / (n : ℝ) ^ 2) ≤ r / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      nlinarith

end InteractingSLE.SLE8
