import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS1S2.Bridges




 






set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS1S2

open scoped ENNReal

 
theorem regK_lower (k : ℕ) (hk : 48 ≤ k) :
    (k : ℝ) / 12 - 2 ≤ (Objects.CorrectedEvent.regK k : ℝ) := by
  have hdiv : k ≤ 12 * (k / 12) + 11 := by omega
  have hK : Objects.CorrectedEvent.regK k + 1 = k / 12 := by
    unfold Objects.CorrectedEvent.regK
    omega
  have hdivR : (k : ℝ) ≤ 12 * (k / 12 : ℕ) + 11 := by exact_mod_cast hdiv
  have hKR : (Objects.CorrectedEvent.regK k : ℝ) + 1 = (k / 12 : ℕ) := by exact_mod_cast hK
  linarith

 

theorem regK_exp_tail (k : ℕ) (hk : 48 ≤ k) :
    Real.exp (-(72 * Real.log 2) * (Objects.CorrectedEvent.regK k : ℝ)) ≤
      (2 : ℝ) ^ (144 : ℝ) * (2 : ℝ) ^ (-(6 : ℝ) * k) := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hK := regK_lower k hk
  have hE : -(72 * Real.log 2) * (Objects.CorrectedEvent.regK k : ℝ) ≤
      Real.log 2 * (144 - 6 * (k : ℝ)) := by nlinarith only [hK, hlog]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  convert hE using 1
  ring

 
theorem lattice_geometric_budget (c : ℝ≥0∞) (k₀ : ℕ) :
    (∑' n : ℕ, (1089 : ℝ≥0∞) * (2 : ℝ≥0∞) ^ (144 : ℕ) * c *
      ((1/16 : ℝ≥0∞) ^ (n + k₀))) ≤
        (1162 : ℝ≥0∞) * (2 : ℝ≥0∞) ^ (144 : ℕ) * c *
          ((1/16 : ℝ≥0∞) ^ k₀) := by
  let q : ℝ≥0∞ := 1/16
  have hq : q < 1 := by dsimp [q]; norm_num
  have hsum : (∑' n : ℕ, q ^ (n + k₀)) = q ^ k₀ * (1 - q)⁻¹ := by
    simp_rw [pow_add]
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
    exact mul_comm _ _
  simp only [ENNReal.tsum_mul_left]
  dsimp [q] at hsum ⊢
  rw [hsum]
  have hnum : (1089 : ℝ≥0∞) * (1 - q)⁻¹ ≤ 1162 := by
    dsimp [q]
    rw [show (1 / 16 : ℝ≥0∞) = ENNReal.ofReal (1 / 16 : ℝ) by
      calc
        (1 / 16 : ℝ≥0∞) = (ENNReal.ofReal (16 : ℝ))⁻¹ := by norm_num
        _ = ENNReal.ofReal (16 : ℝ)⁻¹ :=
          (ENNReal.ofReal_inv_of_pos (by norm_num : 0 < (16 : ℝ))).symm
        _ = ENNReal.ofReal (1 / 16 : ℝ) := by norm_num,
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by norm_num)]
    rw [show (1 - 1 / 16 : ℝ) = 15 / 16 by norm_num]
    rw [← ENNReal.ofReal_inv_of_pos (by norm_num : 0 < (15 / 16 : ℝ))]
    rw [show (1089 : ℝ≥0∞) = ENNReal.ofReal (1089 : ℝ) by norm_num,
      show (1162 : ℝ≥0∞) = ENNReal.ofReal (1162 : ℝ) by norm_num]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1089)]
    norm_num
  calc
    (1089 : ℝ≥0∞) * (2 : ℝ≥0∞) ^ (144 : ℕ) * c *
        (q ^ k₀ * (1 - q)⁻¹) =
      ((1089 : ℝ≥0∞) * (1 - q)⁻¹) *
        ((2 : ℝ≥0∞) ^ (144 : ℕ) * c * q ^ k₀) := by ring
    _ ≤ 1162 * ((2 : ℝ≥0∞) ^ (144 : ℕ) * c * q ^ k₀) := by gcongr
    _ = 1162 * (2 : ℝ≥0∞) ^ (144 : ℕ) * c * q ^ k₀ := by ring

end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS1S2
