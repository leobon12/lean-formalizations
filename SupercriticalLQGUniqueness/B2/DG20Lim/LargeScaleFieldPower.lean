import SupercriticalLQGUniqueness.B2.DG20Lim.LargeScalePower

 


set_option autoImplicit false
noncomputable section

open Set

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem large_scale_field_power_bound
    {r ξ β p C a c : ℝ}
    (hr : 0 < r) (hξ : 0 < ξ) (hC : 0 ≤ C)
    (hbase : C * r ^ (p + ξ * β) ≤ a)
    (hc : -(β * Real.log r) ≤ c) :
    C * r ^ p ≤ a * Real.exp (ξ * c) := by
  have hexp : r ^ (-(ξ * β)) ≤ Real.exp (ξ * c) := by
    rw [Real.rpow_def_of_pos hr]
    apply Real.exp_le_exp.mpr
    calc
      Real.log r * (-(ξ * β)) = ξ * (-(β * Real.log r)) := by ring
      _ ≤ ξ * c := mul_le_mul_of_nonneg_left hc hξ.le
  calc
    C * r ^ p = (C * r ^ (p + ξ * β)) * r ^ (-(ξ * β)) := by
      rw [mul_assoc, ← Real.rpow_add hr]
      congr 1
      ring
    _ ≤ a * Real.exp (ξ * c) :=
      mul_le_mul hbase hexp (Real.rpow_nonneg hr.le _)
        (le_trans (mul_nonneg hC (Real.rpow_nonneg hr.le _)) hbase)

end SupercriticalLQGUniqueness.B2.DG20Lim
