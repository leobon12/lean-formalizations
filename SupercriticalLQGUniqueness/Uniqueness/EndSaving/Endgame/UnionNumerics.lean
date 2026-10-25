import Mathlib




 
set_option autoImplicit false
noncomputable section
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame

theorem endpoint_union_numeric
    (α ν C η ε δ N : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hC : 0 < C)
    (hN0 : 0 ≤ N)
    (hεpow : ε ^ α = 2 * δ)
    (hN : N * (δ ^ ν) ^ 2 ≤ (203 : ℝ) ^ 2)
    (hδsmall : δ ≤ η / (2 * ((203 : ℝ) ^ 4 * C * 2 ^ (4 * ν + 1)))) :
    N ^ 2 * C * ε ^ (α * (4 * ν + 1)) ≤ η / 2 := by
  have hx : 0 < δ ^ ν := Real.rpow_pos_of_pos hδ _
  have hN2 : N ^ 2 * (δ ^ ν) ^ 4 ≤ (203 : ℝ) ^ 4 := by
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ N * (δ ^ ν) ^ 2) hN 2
    nlinarith only [hsq]
  have heps : ε ^ (α * (4 * ν + 1)) =
      2 ^ (4 * ν + 1) * (δ ^ ν) ^ 4 * δ := by
    rw [Real.rpow_mul hε.le, hεpow, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hδ.le]
    have hpow : δ ^ (4 * ν + 1) = (δ ^ ν) ^ 4 * δ := by
      rw [show 4 * ν + 1 = ν * 4 + 1 by ring, Real.rpow_add hδ,
        Real.rpow_mul hδ.le, Real.rpow_one]
      exact congrArg (fun t : ℝ => t * δ) (Real.rpow_natCast (δ ^ ν) 4)
    rw [hpow]
    ring
  have hpow2 : 0 ≤ (2 : ℝ) ^ (4 * ν + 1) :=
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le
  have hcoef : 0 ≤ C * 2 ^ (4 * ν + 1) * δ := by positivity
  have hlarge : N ^ 2 * C * ε ^ (α * (4 * ν + 1)) ≤
      (203 : ℝ) ^ 4 * C * 2 ^ (4 * ν + 1) * δ := by
    rw [heps]
    calc
      N ^ 2 * C * (2 ^ (4 * ν + 1) * (δ ^ ν) ^ 4 * δ) =
          (N ^ 2 * (δ ^ ν) ^ 4) * (C * 2 ^ (4 * ν + 1) * δ) := by ring
      _ ≤ (203 : ℝ) ^ 4 * (C * 2 ^ (4 * ν + 1) * δ) :=
        mul_le_mul_of_nonneg_right hN2 hcoef
      _ = (203 : ℝ) ^ 4 * C * 2 ^ (4 * ν + 1) * δ := by ring
  have hk : 0 < (203 : ℝ) ^ 4 * C * 2 ^ (4 * ν + 1) := by positivity
  have hsmall : ((203 : ℝ) ^ 4 * C * 2 ^ (4 * ν + 1)) * δ ≤ η / 2 := by
    have hden : 0 < 2 * ((203 : ℝ) ^ 4 * C * 2 ^ (4 * ν + 1)) := by positivity
    have hmul := (le_div_iff₀ hden).mp hδsmall
    nlinarith only [hmul]
  exact hlarge.trans hsmall

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame
