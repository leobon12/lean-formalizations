import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCGaussianRatePower

 
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped ENNReal
namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneC_ennreal_scale_cancel
    {ell ξ Q δ p : ℝ} (hell : 0 < ell) (hp : 0 ≤ p) (K : ℕ) :
    (ENNReal.ofReal (((2 : ℝ)⁻¹ ^ K) * ell) /
      ENNReal.ofReal ((2 : ℝ) ^ (-(1 - ξ * Q + δ) * (K : ℝ)) * ell)) ^
        (2 * p) =
      ENNReal.ofReal ((2 : ℝ) ^ ((-ξ * Q + δ) * (2 * p) * (K : ℝ))) := by
  have hs : 0 < (2 : ℝ)⁻¹ ^ K * ell :=
    mul_pos (by positivity) hell
  have ha : 0 < (2 : ℝ) ^ (-(1 - ξ * Q + δ) * (K : ℝ)) * ell :=
    mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hell
  rw [← ENNReal.ofReal_div_of_pos ha]
  rw [ENNReal.ofReal_rpow_of_nonneg (div_nonneg hs.le ha.le)
    (by positivity : 0 ≤ 2 * p)]
  rw [Real.div_rpow hs.le ha.le]
  exact congrArg ENNReal.ofReal (laneC_real_scale_cancel hell (by positivity : 0 ≤ 2 * p) K)

end SupercriticalLQGUniqueness.B2.DG20Conc
