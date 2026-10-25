import SupercriticalLQGUniqueness.B2.DG20Pt.PtDistDyadicGeometric

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_dyadic_arm_sum_le (α : ℝ) (hα : 0 < α)
    (k₀ N : ℕ) :
    ∑ j ∈ Finset.range N,
      ((2 : ℝ) ^ (-α * ((k₀ + (j + 1) : ℕ) : ℝ)) +
       (2 : ℝ) ^ (-α * ((k₀ + (j + 1) : ℕ) : ℝ)) +
       (2 : ℝ) ^ (-α * ((k₀ + j : ℕ) : ℝ))) ≤
      3 * (2 : ℝ) ^ (-α * (k₀ : ℝ)) /
        (1 - (2 : ℝ) ^ (-α)) := by
  let q : ℝ := (2 : ℝ) ^ (-α)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    rw [← Real.rpow_zero (2 : ℝ)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
      (by linarith)
  simp_rw [pt_dist_dyadic_power_eq_geometric]
  exact pt_dist_geometric_arm_le q hq0 hq1 k₀ N

end SupercriticalLQGUniqueness.B2.DG20Pt
