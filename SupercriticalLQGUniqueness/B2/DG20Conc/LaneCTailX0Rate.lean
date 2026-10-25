import LQGMetric.Papers.DDDF.T20CMain

 








set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneC_tailX0_swap_middle (l N C c : ℝ) :
    T20B.tailX0 l N C c = T20B.tailX0 l C N c := by
  unfold T20B.tailX0
  rw [show l * N * C = l * C * N by ring]

 


theorem laneC_tailX0_five_pow_le
    {q c₀ c₁ ε : ℝ} (hq : 0 < q) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (K : ℕ) (hK : 1 ≤ K) :
    T20B.tailX0 q ((5 : ℝ) ^ K) c₀
        (c₁ / (4 * (K : ℝ) ^ (3 * ε))) ≤
      3 + (4 * (q + 1) / (c₁ / (4 * (K : ℝ) ^ (3 * ε)))) ^ 2 +
        (4 * (Real.log (q * c₀ + 1) + Real.log 4) /
          (c₁ / (4 * (K : ℝ) ^ (3 * ε)))) ^ ((2 : ℝ) / 3) *
          (2 * (K : ℝ)) ^ ((2 : ℝ) / 3) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK)
  have hc : 0 < c₁ / (4 * (K : ℝ) ^ (3 * ε)) :=
    div_pos hc₁ (by positivity)
  have hpow : (5 : ℝ) ^ K ≤ 4 ^ (2 * K) := by
    calc
      (5 : ℝ) ^ K ≤ (16 : ℝ) ^ K := by gcongr; norm_num
      _ = 4 ^ (2 * K) := by
        conv_lhs => rw [show (16 : ℝ) = 4 ^ 2 by norm_num]
        rw [← pow_mul]
  have hK' : 1 ≤ 2 * K := by omega
  have h := T20C.tailX0_le hq hc₀ hc (by norm_num : 0 < (1 : ℝ))
    (by positivity : 0 ≤ (5 : ℝ) ^ K) hK' (by simpa only [one_mul] using hpow)
  simpa only [one_mul, mul_one, Nat.cast_mul, Nat.cast_ofNat] using h

end SupercriticalLQGUniqueness.B2.DG20Conc
