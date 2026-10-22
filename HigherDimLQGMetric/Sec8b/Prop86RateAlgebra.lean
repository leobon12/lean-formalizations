import HigherDimLQGMetric.Sec8b.Prop86CandidateBound

/-! Power algebra for the Proposition 8.6 probability estimate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

theorem s7b_rate_algebra {s A E K S a : ℝ} {n m k : ℕ}
    (hs : 0 < s) (hA : 0 < A) (hE : 0 ≤ E) (hK : 0 ≤ K)
    (hS : 0 ≤ S) (hSa : S ≤ A * s ^ n)
    (ha : 0 ≤ a) (hk : 1 ≤ k) :
    E * S ^ a * K / ((s ^ (1 / 2 : ℝ)) / k) ^ m ≤
      (E * A ^ a * K * k ^ m) * s ^ ((n : ℝ) * a - m / 2) := by
  have hsp : 0 < s ^ (1 / 2 : ℝ) := by positivity
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hden : 0 < ((s ^ (1 / 2 : ℝ)) / k) ^ m := by positivity
  have hpow : S ^ a ≤ (A * s ^ n) ^ a :=
    Real.rpow_le_rpow hS hSa ha
  calc
    E * S ^ a * K / ((s ^ (1 / 2 : ℝ)) / k) ^ m ≤
      E * (A * s ^ n) ^ a * K / ((s ^ (1 / 2 : ℝ)) / k) ^ m := by
        gcongr
    _ = (E * A ^ a * K * k ^ m) * s ^ ((n : ℝ) * a - m / 2) := by
      rw [Real.mul_rpow hA.le (pow_nonneg hs.le _),
        div_pow, div_div_eq_mul_div]
      rw [show s ^ n = s ^ (n : ℝ) from (Real.rpow_natCast s n).symm,
        ← Real.rpow_mul hs.le]
      rw [show (s ^ (1 / 2 : ℝ)) ^ m = s ^ ((m : ℝ) / 2) by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
        congr 1
        ring]
      rw [Real.rpow_sub hs]
      field_simp

theorem s7b_final_power {ε A B e N : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (he : (1 / 4 : ℝ) + e ≤ -N) :
    A * ((ε⁻¹) ^ (1 / 8 : ℝ)) ^ (2 : ℕ) *
      (B * (ε⁻¹) ^ e) ≤ A * B * ε ^ N := by
  have hs : 1 ≤ ε⁻¹ := one_le_inv_iff₀.mpr ⟨hε, hε1⟩
  have hs0 : 0 ≤ ε⁻¹ := by positivity
  have hspos : 0 < ε⁻¹ := by positivity
  have hpow := (s7b_inv_eighth_powers hε hε1).2.1
  rw [hpow]
  calc
    A * (ε⁻¹) ^ (1 / 4 : ℝ) * (B * (ε⁻¹) ^ e) =
        A * B * (ε⁻¹) ^ ((1 / 4 : ℝ) + e) := by
      rw [Real.rpow_add hspos]
      ring
    _ ≤ A * B * (ε⁻¹) ^ (-N) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hs he) (mul_nonneg hA hB)
    _ = A * B * ε ^ N := by
      rw [Real.rpow_neg_eq_inv_rpow]
      simp only [inv_inv]

end HigherDimLQGMetric
