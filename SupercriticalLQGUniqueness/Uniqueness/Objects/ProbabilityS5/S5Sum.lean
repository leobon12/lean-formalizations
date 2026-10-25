import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS5.S5Prob




 



set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS5

theorem compareScale_pos (k : ℕ) : 0 < Objects.CorrectedEvent.compareScale k := by
  unfold Objects.CorrectedEvent.compareScale
  positivity

theorem compareScale_antitone {j k : ℕ} (hjk : j ≤ k) :
    Objects.CorrectedEvent.compareScale k ≤ Objects.CorrectedEvent.compareScale j := by
  unfold Objects.CorrectedEvent.compareScale
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have : (j : ℝ) ≤ k := by exact_mod_cast hjk
  linarith

theorem compareScale_pow_four (k : ℕ) :
    (Objects.CorrectedEvent.compareScale k ^ (-(1:ℝ)/16)) ^ (-(64:ℝ)) =
      (Objects.CorrectedEvent.compareScale k) ^ (4:ℝ) := by
  rw [← Real.rpow_mul (compareScale_pos k).le]
  congr 1
  ring

theorem compareScale_geom (k : ℕ) :
    (Objects.CorrectedEvent.compareScale k) ^ 2 = (((21:ℝ)/20)⁻¹ ^ 2) ^ k := by
  have ht : Objects.CorrectedEvent.compareScale k = (((21:ℝ)/20)⁻¹) ^ k := by
    unfold Objects.CorrectedEvent.compareScale
    rw [show -(k:ℝ) = (-1:ℝ) * k by ring,
      Real.rpow_mul (by norm_num), Real.rpow_neg_one, Real.rpow_natCast]
  rw [ht, ← pow_mul, ← pow_mul, Nat.mul_comm]

theorem summable_compareScale_sq : Summable fun k : ℕ => (Objects.CorrectedEvent.compareScale k) ^ 2 := by
  have hgeom : Summable fun k : ℕ => ((((21:ℝ)/20)⁻¹)^2)^k := by
    apply summable_geometric_of_lt_one
    · positivity
    · norm_num
  simpa only [compareScale_geom] using hgeom

end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS5
