import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier.FiniteScaleProbability
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier.DyadicTransfer




set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier

 

theorem dyadic_bad_probability
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (bad : ℕ → Set Ω) {C q : ℝ} (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hbad : ∀ n : ℕ, P (bad n) ≤
      ENNReal.ofReal (C * (q * (1 / 2 : ℝ) ^ n) ^ (4 : ℕ))) :
    P (⋃ n, bad n) ≤ ENNReal.ofReal (C * q ^ (4 : ℕ)) * (1 - ENNReal.ofReal (1 / 16 : ℝ))⁻¹ := by
  have hterm : ∀ n : ℕ,
      ENNReal.ofReal (C * (q * (1 / 2 : ℝ) ^ n) ^ (4 : ℕ)) =
      ENNReal.ofReal (C * q ^ (4 : ℕ)) * (ENNReal.ofReal (1 / 16 : ℝ)) ^ n := by
    intro n
    have hpow : ((1 / 2 : ℝ) ^ n) ^ (4 : ℕ) =
        (1 / 16 : ℝ) ^ n := by
      rw [← pow_mul, mul_comm n 4, pow_mul]
      norm_num
    have hreal : C * (q * (1 / 2 : ℝ) ^ n) ^ (4 : ℕ) =
        (C * q ^ (4 : ℕ)) * (1 / 16 : ℝ) ^ n := by
      rw [mul_pow, hpow]
      ring
    rw [hreal, ENNReal.ofReal_mul (by positivity : 0 ≤ C * q ^ (4 : ℕ)),
      ENNReal.ofReal_pow (by norm_num : 0 ≤ (1 / 16 : ℝ))]
  calc
    P (⋃ n, bad n) ≤ ∑' n, P (bad n) := measure_iUnion_le _
    _ ≤ ∑' n, ENNReal.ofReal (C * (q * (1 / 2 : ℝ) ^ n) ^ (4 : ℕ)) :=
      ENNReal.tsum_le_tsum hbad
    _ = ENNReal.ofReal (C * q ^ (4 : ℕ)) * (1 - ENNReal.ofReal (1 / 16 : ℝ))⁻¹ := by
      simp_rw [hterm]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier
