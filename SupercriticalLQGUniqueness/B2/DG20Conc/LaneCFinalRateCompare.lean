import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCExpFactorRate

 
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped ENNReal
namespace SupercriticalLQGUniqueness.B2.DG20Conc

 
theorem laneC_final_rate_compare
    {ρ τ ν r : ℝ} (hν : 0 ≤ ν) (hr : 0 ≤ r)
    (hρ : ρ + r * (ν / Real.log 2 + 1) ≤ τ)
    (K : ℕ) (hK : 1 ≤ K) :
    ENNReal.ofReal ((2 : ℝ) ^ (ρ * K)) *
      ENNReal.ofReal (Real.exp (ν * K) + 1) ^ r ≤
        ENNReal.ofReal ((2 : ℝ) ^ (τ * K)) := by
  have hE := laneC_exp_factor_rate hν hr K hK
  have htwo : 0 ≤ (2 : ℝ) ^ (ρ * K) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  calc
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (ρ * K)) *
        ENNReal.ofReal ((2 : ℝ) ^ ((r * (ν / Real.log 2 + 1)) * K)) :=
      mul_le_mul_of_nonneg_left hE bot_le
    _ = ENNReal.ofReal ((2 : ℝ) ^ ((ρ + r * (ν / Real.log 2 + 1)) * K)) := by
      rw [← ENNReal.ofReal_mul htwo, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 2
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (mul_le_mul_of_nonneg_right hρ (by positivity)))

end SupercriticalLQGUniqueness.B2.DG20Conc
