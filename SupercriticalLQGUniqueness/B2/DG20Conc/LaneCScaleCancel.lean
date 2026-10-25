import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCNormalizedL2

 
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneC_real_scale_cancel
    {ell ξ Q δ p : ℝ} (hell : 0 < ell) (hp : 0 ≤ p) (K : ℕ) :
    ((((2 : ℝ)⁻¹ ^ K * ell) ^ p) /
      (((2 : ℝ) ^ (-(1 - ξ * Q + δ) * (K : ℝ)) * ell) ^ p)) =
        (2 : ℝ) ^ ((-ξ * Q + δ) * p * (K : ℝ)) := by
  have htwo : 0 < (2 : ℝ) := by norm_num
  have hpow (x : ℝ) : 0 < (2 : ℝ) ^ x := Real.rpow_pos_of_pos htwo _
  have hinv : (2 : ℝ)⁻¹ ^ K = (2 : ℝ) ^ (-(K : ℝ)) := by
    rw [← Real.rpow_natCast, Real.inv_rpow htwo.le, Real.rpow_neg htwo.le]
  rw [hinv]
  rw [Real.mul_rpow (hpow _).le hell.le,
    Real.mul_rpow (hpow _).le hell.le]
  have hellp : 0 < ell ^ p := Real.rpow_pos_of_pos hell _
  rw [mul_div_mul_right _ _ hellp.ne']
  rw [← Real.rpow_mul htwo.le, ← Real.rpow_mul htwo.le,
    ← Real.rpow_sub htwo]
  congr 1
  ring

end SupercriticalLQGUniqueness.B2.DG20Conc
