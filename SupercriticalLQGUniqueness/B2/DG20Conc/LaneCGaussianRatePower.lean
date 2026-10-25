import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCScalePower

 
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped ENNReal
namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneC_gaussian_rate_power
    (K : ℕ) (ζ p ξ : ℝ) (hζ : 0 < ζ) :
    ((ENNReal.ofReal (Real.exp (((K : ℝ) * Real.log 2) *
      (((1 + ζ) * p * ξ) ^ 2) / 2))) ^ (1 / (1 + ζ))) ^ (2 : ℝ) =
      ENNReal.ofReal ((2 : ℝ) ^ (((1 + ζ) * p ^ 2 * ξ ^ 2) * K)) := by
  have hζ1 : 0 < 1 + ζ := by linarith
  have he : (1 / (1 + ζ)) * (2 : ℝ) = 2 / (1 + ζ) := by ring
  rw [← ENNReal.rpow_mul, he]
  rw [ENNReal.ofReal_rpow_of_nonneg
    (Real.exp_pos _).le (div_nonneg (by norm_num) hζ1.le)]
  rw [← Real.exp_mul]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 2
  field_simp

end SupercriticalLQGUniqueness.B2.DG20Conc
