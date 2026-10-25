import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCTailX0Rate
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPowerRate

 






set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 
theorem laneC_tailX0_five_pow_le_powers
    {q c₀ c₁ ε : ℝ} (hq : 0 < q) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (K : ℕ) (hK : 1 ≤ K) :
    T20B.tailX0 q ((5 : ℝ) ^ K) c₀
        (c₁ / (4 * (K : ℝ) ^ (3 * ε))) ≤
      3 + (16 * (q + 1) / c₁) ^ 2 * (K : ℝ) ^ (6 * ε) +
        (32 * (Real.log (q * c₀ + 1) + Real.log 4) / c₁) ^ ((2 : ℝ) / 3) *
          (K : ℝ) ^ ((2 : ℝ) / 3 + 2 * ε) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK)
  let x : ℝ := (K : ℝ) ^ (3 * ε)
  have hx : 0 < x := Real.rpow_pos_of_pos hK0 _
  let L : ℝ := Real.log (q * c₀ + 1) + Real.log 4
  have hL : 0 ≤ L := by
    dsimp [L]
    have : 1 ≤ q * c₀ + 1 := by nlinarith [mul_pos hq hc₀]
    exact add_nonneg (Real.log_nonneg this) (Real.log_nonneg (by norm_num))
  have hbase₁ : 4 * (q + 1) / (c₁ / (4 * x)) =
      16 * (q + 1) / c₁ * x := by
    field_simp
    ring
  have hbase₂ : 4 * L / (c₁ / (4 * x)) * (2 * (K : ℝ)) =
      (32 * L / c₁) * (x * K) := by
    field_simp
    ring
  have hpow₁ : x ^ 2 = (K : ℝ) ^ (6 * ε) := by
    dsimp [x]
    calc
      ((K : ℝ) ^ (3 * ε)) ^ 2 = (K : ℝ) ^ ((3 * ε) * (2 : ℕ)) :=
        (Real.rpow_mul_natCast hK0.le (3 * ε) 2).symm
      _ = (K : ℝ) ^ (6 * ε) := by congr 1; push_cast; ring
  have hpow₂ : (x * K) ^ ((2 : ℝ) / 3) =
      (K : ℝ) ^ ((2 : ℝ) / 3 + 2 * ε) := by
    have hbase : x * K = (K : ℝ) ^ (3 * ε + 1) := by
      dsimp [x]
      rw [Real.rpow_add hK0]
      simp
    rw [hbase, ← Real.rpow_mul hK0.le]
    congr 1
    ring
  have hfirst :
      (4 * (q + 1) / (c₁ / (4 * x))) ^ 2 =
        (16 * (q + 1) / c₁) ^ 2 * (K : ℝ) ^ (6 * ε) := by
    rw [hbase₁, mul_pow, hpow₁]
  have hsecond :
      (4 * L / (c₁ / (4 * x))) ^ ((2 : ℝ) / 3) *
          (2 * (K : ℝ)) ^ ((2 : ℝ) / 3) =
        (32 * L / c₁) ^ ((2 : ℝ) / 3) *
          (K : ℝ) ^ ((2 : ℝ) / 3 + 2 * ε) := by
    rw [← Real.mul_rpow (by positivity : 0 ≤ 4 * L / (c₁ / (4 * x)))
      (by positivity : 0 ≤ 2 * (K : ℝ))]
    rw [hbase₂, Real.mul_rpow (by positivity : 0 ≤ 32 * L / c₁)
      (by positivity : 0 ≤ x * K), hpow₂]
  have h := laneC_tailX0_five_pow_le (ε := ε) hq hc₀ hc₁ K hK
  change T20B.tailX0 q ((5 : ℝ) ^ K) c₀ (c₁ / (4 * x)) ≤
    3 + (4 * (q + 1) / (c₁ / (4 * x))) ^ 2 +
      (4 * L / (c₁ / (4 * x))) ^ ((2 : ℝ) / 3) *
        (2 * (K : ℝ)) ^ ((2 : ℝ) / 3) at h
  rw [hfirst, hsecond] at h
  exact h

end SupercriticalLQGUniqueness.B2.DG20Conc
