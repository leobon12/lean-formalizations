import SupercriticalLQGUniqueness.B2.DG20Lim.PointScaleSection4

 


set_option autoImplicit false
noncomputable section

open Set LQGMetric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem point_scale_real_coefficient
    (ξ : ℝ) (a a' : Ioi (0 : ℝ)) (r : Ioi (0 : ℝ))
    (c : ℝ) :
    (ENNReal.ofReal ((a : ℝ) * Real.exp (-(ξ * c)) /
      ((a' : ℝ) * (r : ℝ))))⁻¹ =
      ENNReal.ofReal
        (((r : ℝ) * (a' : ℝ) / (a : ℝ)) * Real.exp (ξ * c)) := by
  have hcoeff : 0 < (a : ℝ) * Real.exp (-(ξ * c)) /
      ((a' : ℝ) * (r : ℝ)) :=
    div_pos (mul_pos a.property (Real.exp_pos _))
      (mul_pos a'.property r.property)
  rw [← ENNReal.ofReal_inv_of_pos hcoeff]
  congr 1
  rw [Real.exp_neg]
  field_simp [(Set.mem_Ioi.mp a.property).ne',
    (Set.mem_Ioi.mp a'.property).ne',
    (Set.mem_Ioi.mp r.property).ne',
    Real.exp_ne_zero (ξ * c)]

end SupercriticalLQGUniqueness.B2.DG20Lim
