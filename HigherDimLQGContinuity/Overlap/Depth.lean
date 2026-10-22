import HigherDimLQGContinuity.Core.Interfaces

/-!
# Depth arithmetic for Proposition 4.5 (packet Q8b)

This is the deterministic logarithmic estimate of NA2 R13 and blueprint (4.21).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

theorem prop45_depth {κ μ D₀ M₀ CJ CKJ ℓ : ℝ} {k m₀ : ℕ}
    (hκ : 0 < κ) (hD₀ : 0 < D₀) (hM₀ : 0 < M₀)
    (hCJ : 1 ≤ CJ) (hCKJ : 1 ≤ CKJ)
    (hk : (4 * μ + 4) / (κ / 2) ≤ k) (hm₀ : κ * k ≤ m₀)
    (hℓ : max (max (Real.log CJ / D₀) (4 * (Real.log k + Real.log CKJ) / (κ / 2)))
      (max (64 * k * D₀ * M₀ ^ 2 / ((κ / 2) ^ 2)) (2 * Real.log k)) ≤ ℓ) :
    (CKJ ^ k * k ^ k / Real.exp (m₀ * ℓ / 2)) *
        Real.exp (k * M₀ * Real.sqrt (2 * (k * (D₀ * ℓ + Real.log CJ)))) ≤
      Real.exp (-(2 * μ + 2) * ℓ) := by
  have hρ : 0 < κ / 2 := by positivity
  have hCJlog : 0 ≤ Real.log CJ := Real.log_nonneg hCJ
  have hCKJlog : 0 ≤ Real.log CKJ := Real.log_nonneg hCKJ
  have hℓCJ : Real.log CJ / D₀ ≤ ℓ := le_trans (le_max_left _ _ |>.trans (le_max_left _ _)) hℓ
  have hℓ0 : 0 ≤ ℓ := by
    have := div_nonneg hCJlog hD₀.le
    linarith
  by_cases hk0 : k = 0
  · subst k
    have hμ : 2 * μ + 2 ≤ 0 := by
      norm_num at hk
      have h := (div_le_iff₀ hρ).mp hk
      linarith
    have hm0 : 0 ≤ (m₀ : ℝ) := Nat.cast_nonneg _
    have hleft : -(m₀ : ℝ) * ℓ / 2 ≤ -(2 * μ + 2) * ℓ := by
      nlinarith [mul_nonneg (show 0 ≤ -(2 * μ + 2) by linarith) hℓ0,
        mul_nonneg hm0 hℓ0]
    have h := Real.exp_le_exp.mpr hleft
    simpa only [pow_zero, Nat.cast_zero, zero_mul, Real.sqrt_zero, Real.exp_zero,
      mul_one, zero_add, one_mul, Real.exp_neg, one_div, div_eq_mul_inv,
      neg_mul, neg_div] using h
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk0)
  have hklog : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast Nat.succ_le_iff.mp (Nat.pos_of_ne_zero hk0))
  have hℓlog : 4 * (Real.log k + Real.log CKJ) / (κ / 2) ≤ ℓ :=
    le_trans (le_max_right _ _ |>.trans (le_max_left _ _)) hℓ
  have hℓsq : 64 * (k : ℝ) * D₀ * M₀ ^ 2 / ((κ / 2) ^ 2) ≤ ℓ :=
    le_trans (le_max_left _ _ |>.trans (le_max_right _ _)) hℓ
  have hCJle : Real.log CJ ≤ D₀ * ℓ := by
    simpa only [mul_comm] using (div_le_iff₀ hD₀).mp hℓCJ
  have hlog : Real.log k + Real.log CKJ ≤ (κ / 2) * ℓ / 4 := by
    have h := (div_le_iff₀ hρ).mp hℓlog
    nlinarith only [h]
  have hsq : 64 * (k : ℝ) * D₀ * M₀ ^ 2 ≤ (κ / 2) ^ 2 * ℓ := by
    simpa only [mul_comm] using (div_le_iff₀ (sq_pos_of_pos hρ)).mp hℓsq
  let r := Real.sqrt (2 * ((k : ℝ) * (D₀ * ℓ + Real.log CJ)))
  have hrarg : 0 ≤ 2 * ((k : ℝ) * (D₀ * ℓ + Real.log CJ)) := by positivity
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = 2 * ((k : ℝ) * (D₀ * ℓ + Real.log CJ)) := Real.sq_sqrt hrarg
  have hr2le : r ^ 2 ≤ 4 * (k : ℝ) * D₀ * ℓ := by
    rw [hr2]
    have h := mul_le_mul_of_nonneg_left (show D₀ * ℓ + Real.log CJ ≤ 2 * D₀ * ℓ by linarith) hkpos.le
    nlinarith only [h]
  have hrbound : 4 * M₀ * r ≤ (κ / 2) * ℓ := by
    have h1 := mul_le_mul_of_nonneg_left hr2le (show 0 ≤ 16 * M₀ ^ 2 by positivity)
    have h2 := mul_le_mul_of_nonneg_right hsq hℓ0
    have hsqbound : (4 * M₀ * r) ^ 2 ≤ ((κ / 2) * ℓ) ^ 2 := by
      nlinarith only [h1, h2]
    have hx0 : 0 ≤ 4 * M₀ * r := by positivity
    have hy0 : 0 ≤ (κ / 2) * ℓ := by positivity
    nlinarith only [hsqbound, hx0, hy0]
  have hlogbound : (k : ℝ) * (Real.log CKJ + Real.log k) ≤
      (κ / 2) * k * ℓ / 4 := by
    have h := mul_le_mul_of_nonneg_left hlog hkpos.le
    nlinarith only [h]
  have hrbound' : (k : ℝ) * M₀ * r ≤ (κ / 2) * k * ℓ / 4 := by
    have h := mul_le_mul_of_nonneg_left hrbound hkpos.le
    nlinarith only [h]
  have hmbound : (κ / 2) * k * ℓ ≤ (m₀ : ℝ) * ℓ / 2 := by
    have h := mul_le_mul_of_nonneg_right hm₀ hℓ0
    nlinarith only [h]
  have hμbound : 2 * μ + 2 ≤ (κ / 2) * k / 2 := by
    have h := (div_le_iff₀ hρ).mp hk
    nlinarith only [h]
  have hexponent : (k : ℝ) * Real.log CKJ + k * Real.log k -
      m₀ * ℓ / 2 + k * M₀ * r ≤ -(2 * μ + 2) * ℓ := by
    have hμℓ := mul_le_mul_of_nonneg_right hμbound hℓ0
    nlinarith only [hlogbound, hrbound', hmbound, hμℓ]
  have hCKJpow : CKJ ^ k = Real.exp ((k : ℝ) * Real.log CKJ) := by
    simpa only [Real.exp_log (by linarith : 0 < CKJ)] using
      (Real.exp_nat_mul (Real.log CKJ) k).symm
  have hkpow : (k : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log k) := by
    simpa only [Real.exp_log hkpos] using
      (Real.exp_nat_mul (Real.log k) k).symm
  rw [hCKJpow, hkpow]
  change (Real.exp ((k : ℝ) * Real.log CKJ) *
    Real.exp ((k : ℝ) * Real.log k) / Real.exp ((m₀ : ℝ) * ℓ / 2)) *
    Real.exp ((k : ℝ) * M₀ * r) ≤ Real.exp (-(2 * μ + 2) * ℓ)
  rw [← Real.exp_add, ← Real.exp_sub, ← Real.exp_add]
  exact Real.exp_le_exp.mpr hexponent

/-- The depth estimate after absorbing the factor `(k+1)^k` and the catalogue count. -/
theorem q8b_prop45_depth_from_card {κ μ D₀ M₀ CJ CKJ ℓ N : ℝ} {k m₀ : ℕ}
    (hκ : 0 < κ) (hD₀ : 0 < D₀) (hM₀ : 0 < M₀)
    (hCJ : 1 ≤ CJ) (hCKJ : 1 ≤ CKJ)
    (hk : (4 * μ + 4) / (κ / 2) ≤ k) (hm₀ : κ * k ≤ m₀)
    (hkpos : 0 < k) (hNpos : 0 < N)
    (hℓ : max (max (Real.log CJ / D₀)
        (4 * (2 * Real.log k + Real.log CKJ + 1) / (κ / 2)))
      (max (64 * k * D₀ * M₀ ^ 2 / ((κ / 2) ^ 2)) (2 * Real.log k)) ≤ ℓ)
    (hcard : N ≤ (CJ * Real.exp (D₀ * ℓ)) ^ k) :
    ((CKJ ^ k * ((k : ℝ) + 1) ^ k) * (k : ℝ) ^ k /
        Real.exp (m₀ * ℓ / 2)) *
        Real.exp (k * M₀ * Real.sqrt (2 * Real.log N)) ≤
      Real.exp (-(2 * μ + 2) * ℓ) := by
  let K : ℝ := k
  let CKJ' : ℝ := Real.exp 1 * K * CKJ
  have hKpos : 0 < K := Nat.cast_pos.mpr hkpos
  have hKone : 1 ≤ K := by
    have h : 1 ≤ k := by omega
    dsimp [K]
    exact_mod_cast h
  have hCKJpos : 0 < CKJ := by linarith
  have hCJpos : 0 < CJ := by linarith
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by
    simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith
  have hCKJ' : 1 ≤ CKJ' := by
    dsimp [CKJ']
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le he1 hKone) hCKJ
  have hlogCKJ' : Real.log CKJ' = 1 + Real.log K + Real.log CKJ := by
    dsimp [CKJ']
    rw [Real.log_mul (by positivity : Real.exp 1 * K ≠ 0) hCKJpos.ne',
      Real.log_mul (Real.exp_pos 1).ne' hKpos.ne', Real.log_exp]
  have hℓ' : max (max (Real.log CJ / D₀)
        (4 * (Real.log k + Real.log CKJ') / (κ / 2)))
      (max (64 * k * D₀ * M₀ ^ 2 / ((κ / 2) ^ 2)) (2 * Real.log k)) ≤ ℓ := by
    have heq : 4 * (Real.log k + Real.log CKJ') / (κ / 2) =
        4 * (2 * Real.log k + Real.log CKJ + 1) / (κ / 2) := by
      rw [hlogCKJ']
      ring
    rw [heq]
    exact hℓ
  have hKadd : K + 1 ≤ Real.exp 1 * K := by
    have h := mul_le_mul_of_nonneg_right he2 hKpos.le
    nlinarith only [h, hKone]
  have hUle : CKJ ^ k * (K + 1) ^ k ≤ CKJ' ^ k := by
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ K + 1) hKadd k
    calc
      CKJ ^ k * (K + 1) ^ k ≤ CKJ ^ k * (Real.exp 1 * K) ^ k :=
        mul_le_mul_of_nonneg_left hpow (pow_nonneg (zero_le_one.trans hCKJ) _)
      _ = CKJ' ^ k := by dsimp [CKJ']; rw [mul_pow]; ring
  have hNlog : Real.log N ≤ (k : ℝ) * (D₀ * ℓ + Real.log CJ) := by
    have h := Real.log_le_log hNpos hcard
    rw [Real.log_pow, Real.log_mul hCJpos.ne' (Real.exp_pos _).ne',
      Real.log_exp] at h
    nlinarith only [h]
  have hsqrt : Real.sqrt (2 * Real.log N) ≤
      Real.sqrt (2 * ((k : ℝ) * (D₀ * ℓ + Real.log CJ))) :=
    Real.sqrt_le_sqrt (by nlinarith only [hNlog])
  have hexp : Real.exp ((k : ℝ) * M₀ * Real.sqrt (2 * Real.log N)) ≤
      Real.exp ((k : ℝ) * M₀ *
        Real.sqrt (2 * ((k : ℝ) * (D₀ * ℓ + Real.log CJ)))) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hsqrt (by positivity)
  have hdepth := prop45_depth hκ hD₀ hM₀ hCJ hCKJ' hk hm₀ hℓ'
  calc
    ((CKJ ^ k * (K + 1) ^ k) * K ^ k /
        Real.exp (m₀ * ℓ / 2)) *
        Real.exp (k * M₀ * Real.sqrt (2 * Real.log N)) ≤
      (CKJ' ^ k * K ^ k / Real.exp (m₀ * ℓ / 2)) *
        Real.exp (k * M₀ * Real.sqrt
          (2 * ((k : ℝ) * (D₀ * ℓ + Real.log CJ)))) := by
      gcongr
    _ ≤ Real.exp (-(2 * μ + 2) * ℓ) := hdepth

end HigherDimLQGContinuity
