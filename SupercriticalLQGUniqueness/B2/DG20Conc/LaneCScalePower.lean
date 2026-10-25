import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCScaleCancel

 
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped ENNReal
namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneC_scale_power_cancel
    (a s E : ℝ≥0∞) {p q t : ℝ}
    (hp : 0 ≤ p) (ht : 0 ≤ t) (hqt : q * t = 1) :
    ((a ^ p)⁻¹) ^ (2 : ℝ) * (s ^ (p * q) * E) ^ (2 * t) =
      (s / a) ^ (2 * p) * E ^ (2 * t) := by
  have h2t : 0 ≤ 2 * t := by positivity
  rw [ENNReal.mul_rpow_of_nonneg _ _ h2t]
  rw [← ENNReal.inv_rpow, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  have he : (p * q) * (2 * t) = 2 * p := by nlinarith [hqt]
  rw [he]
  rw [ENNReal.div_rpow_of_nonneg s a (by positivity : 0 ≤ 2 * p)]
  simp only [div_eq_mul_inv]
  rw [show p * (2 : ℝ) = 2 * p by ring]
  rw [ENNReal.inv_rpow]
  ac_rfl

end SupercriticalLQGUniqueness.B2.DG20Conc
