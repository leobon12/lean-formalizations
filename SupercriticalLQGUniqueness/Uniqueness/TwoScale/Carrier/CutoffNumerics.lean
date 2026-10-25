import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier.CarrierDyadic




set_option autoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier

 
theorem dyadic_geometric_factor_le_two :
    (1 - ENNReal.ofReal (1 / 16 : ℝ))⁻¹ ≤ 2 := by
  conv_rhs => rw [← inv_inv (2 : ℝ≥0∞)]
  apply ENNReal.inv_le_inv.mpr
  have hc : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
  rw [← hc, ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hr := ENNReal.ofReal_le_ofReal
    (by norm_num : (2 : ℝ)⁻¹ ≤ 1 - 1 / 16)
  rw [ENNReal.ofReal_sub 1 (by norm_num : (0 : ℝ) ≤ 1 / 16),
    ENNReal.ofReal_one] at hr
  exact hr

 

theorem exists_ratio_cutoff
    {p C L : ℝ} (hp : 0 < p) (hC : 0 < C) (hL : 0 < L) :
    ∃ q : ℝ, 0 < q ∧ q ≤ 1 / 16 ∧ q ≤ L ∧
      q ^ ((3 : ℝ) / 4) ≤ 1 / 8 ∧
      q ^ ((3 : ℝ) / 4) ≤ 1 / 512 ∧
      ENNReal.ofReal (C * q ^ (4 : ℕ)) *
        (1 - ENNReal.ofReal (1 / 16 : ℝ))⁻¹ ≤
          ENNReal.ofReal (p / 4) := by
  let q := min (1 / 4096 : ℝ) (min L (p / (8 * C)))
  have hq : 0 < q := lt_min (by norm_num) (lt_min hL (div_pos hp (by positivity)))
  have hqsmall : q ≤ 1 / 4096 := min_le_left _ _
  have hq16 : q ≤ 1 / 16 := by linarith
  have hqL : q ≤ L := (min_le_right _ _).trans (min_le_left _ _)
  have hqbudget : q ≤ p / (8 * C) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hq1 : q ≤ 1 := by linarith
  have hqradSmall : q ^ ((3 : ℝ) / 4) ≤ 1 / 512 := by
    have hpwr := Real.rpow_le_rpow hq.le hqsmall
      (by norm_num : (0 : ℝ) ≤ 3 / 4)
    norm_num at hpwr
    exact hpwr
  have hqrad : q ^ ((3 : ℝ) / 4) ≤ 1 / 8 := by linarith
  have hq4 : q ^ (4 : ℕ) ≤ q := by
    have hq3 : q ^ (3 : ℕ) ≤ 1 := pow_le_one₀ hq.le hq1
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ]
    nlinarith [mul_le_mul_of_nonneg_right hq3 hq.le]
  have hreal : 2 * C * q ^ (4 : ℕ) ≤ p / 4 := by
    have hb : (8 * C) * q ≤ p := by
      simpa only [mul_comm] using
        (le_div_iff₀ (by positivity : 0 < 8 * C)).mp hqbudget
    nlinarith [mul_le_mul_of_nonneg_left hq4 (by positivity : 0 ≤ 2 * C)]
  refine ⟨q, hq, hq16, hqL, hqrad, hqradSmall, ?_⟩
  calc
    ENNReal.ofReal (C * q ^ (4 : ℕ)) *
        (1 - ENNReal.ofReal (1 / 16 : ℝ))⁻¹ ≤
      ENNReal.ofReal (C * q ^ (4 : ℕ)) * 2 := by
        gcongr
        exact dyadic_geometric_factor_le_two
    _ = ENNReal.ofReal (2 * C * q ^ (4 : ℕ)) := by
      rw [mul_comm (ENNReal.ofReal (C * q ^ (4 : ℕ))) 2]
      calc
        2 * ENNReal.ofReal (C * q ^ (4 : ℕ)) =
          ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal (C * q ^ (4 : ℕ)) := by norm_num
        _ = ENNReal.ofReal ((2 : ℝ) * (C * q ^ (4 : ℕ))) :=
          (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)).symm
        _ = ENNReal.ofReal (2 * C * q ^ (4 : ℕ)) := by congr 1; ring
    _ ≤ ENNReal.ofReal (p / 4) := ENNReal.ofReal_le_ofReal hreal


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier
