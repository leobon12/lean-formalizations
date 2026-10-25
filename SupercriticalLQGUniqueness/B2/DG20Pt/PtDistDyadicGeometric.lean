import SupercriticalLQGUniqueness.B2.DG20Pt.PtDistOpenConnectedFinite

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_dyadic_power_eq_geometric (α : ℝ) (k : ℕ) :
    (2 : ℝ) ^ (-α * (k : ℝ)) = ((2 : ℝ) ^ (-α)) ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]

theorem pt_dist_dyadic_geometric_tail (α : ℝ) (hα : 0 < α)
    (k₀ N : ℕ) :
    ∑ j ∈ Finset.range N,
      (2 : ℝ) ^ (-α * ((k₀ + j : ℕ) : ℝ)) ≤
      (2 : ℝ) ^ (-α * (k₀ : ℝ)) /
        (1 - (2 : ℝ) ^ (-α)) := by
  let q : ℝ := (2 : ℝ) ^ (-α)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    rw [← Real.rpow_zero (2 : ℝ)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
      (by linarith)
  simp_rw [pt_dist_dyadic_power_eq_geometric]
  change (∑ j ∈ Finset.range N, q ^ (k₀ + j)) ≤ q ^ k₀ / (1 - q)
  calc
    _ = q ^ k₀ * (∑ j ∈ Finset.range N, q ^ j) := by
      simp_rw [pow_add]
      rw [Finset.mul_sum]
    _ ≤ q ^ k₀ * (1 / (1 - q)) :=
      mul_le_mul_of_nonneg_left
        (pt_dist_geometric_range_le q hq0 hq1 N) (pow_nonneg hq0 _)
    _ = _ := by ring

end SupercriticalLQGUniqueness.B2.DG20Pt
