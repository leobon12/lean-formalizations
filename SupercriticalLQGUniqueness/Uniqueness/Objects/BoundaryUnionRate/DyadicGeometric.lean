import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate.DyadicMoment




 


set_option autoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate

theorem dyadicQ_rpow_tsum_lt_top (γ : ℝ) (hγ : 0 < γ) :
    (∑' i : ℕ × Bool, ENNReal.ofReal (Objects.BoundaryUnionDyadic.dyadicQ i.1 ^ γ)) < ∞ := by
  let ρ : ENNReal := ENNReal.ofReal ((1 / 2 : ℝ) ^ γ)
  have hρ : ρ < 1 := by
    dsimp [ρ]
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff one_pos]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) hγ
  have heq (k : ℕ) :
      ENNReal.ofReal (Objects.BoundaryUnionDyadic.dyadicQ k ^ γ) = ρ ^ (k + 1) := by
    dsimp [Objects.BoundaryUnionDyadic.dyadicQ, ρ]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    rw [mul_comm (↑(k + 1) : ℝ) γ, Real.rpow_mul (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    rw [Real.rpow_natCast, ENNReal.ofReal_pow
      (Real.rpow_nonneg (by norm_num) _)]
  rw [ENNReal.tsum_prod']
  simp_rw [heq]
  simp only [tsum_fintype, Fintype.sum_bool]
  rw [ENNReal.tsum_add]
  have hfinite : (∑' k : ℕ, ρ ^ (k + 1)) < ∞ := by
    rw [ENNReal.tsum_geometric_add_one]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr
      (ne_top_of_lt hρ)) (ENNReal.inv_lt_top.mpr (by
        exact (tsub_pos_iff_lt).mpr hρ))
  exact ENNReal.add_lt_top.mpr ⟨hfinite, hfinite⟩


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate
