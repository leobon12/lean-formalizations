import SupercriticalLQGUniqueness.B2.DG20Lim.ScaledCircleAverageDecay

 


set_option autoImplicit false
noncomputable section

open Set

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem point_scale_power_bound
    {r ξ β p C a c : ℝ}
    (hr : 0 < r) (hξ : 0 < ξ) (hC : 0 ≤ C)
    (hbase : a ≤ C * r ^ (p + ξ * β))
    (hc : c ≤ β * Real.log r⁻¹) :
    a * Real.exp (ξ * c) ≤ C * r ^ p := by
  have hexp : Real.exp (ξ * c) ≤ r ^ (-(ξ * β)) := by
    rw [Real.rpow_def_of_pos hr]
    apply Real.exp_le_exp.mpr
    calc
      ξ * c ≤ ξ * (β * Real.log r⁻¹) :=
        mul_le_mul_of_nonneg_left hc hξ.le
      _ = Real.log r * (-(ξ * β)) := by rw [Real.log_inv]; ring_nf
  calc
    a * Real.exp (ξ * c) ≤
        (C * r ^ (p + ξ * β)) * r ^ (-(ξ * β)) :=
      mul_le_mul hbase hexp (Real.exp_pos _).le
        (mul_nonneg hC (Real.rpow_nonneg hr.le _))
    _ = C * r ^ p := by
      rw [mul_assoc, ← Real.rpow_add hr]
      congr 1
      ring_nf

end SupercriticalLQGUniqueness.B2.DG20Lim
