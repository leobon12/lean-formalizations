import SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45.CountMarkov




 
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45

 

theorem probability_le_of_inverse_window
    {a : ℝ} (ha : 0 < a) {n k : ℕ} (hnk : n ≤ k)
    {x y : ℝ≥0∞}
    (h : ENNReal.ofReal ((a⁻¹) ^ n) * x ≤ y) :
    x ≤ ENNReal.ofReal ((max a 1) ^ k) * y := by
  have haPow : 0 ≤ a ^ n := (pow_pos ha _).le
  have hprod : ENNReal.ofReal (a ^ n) *
      ENNReal.ofReal ((a⁻¹) ^ n) = 1 := by
    rw [← ENNReal.ofReal_mul haPow, ← mul_pow, mul_inv_cancel₀ ha.ne',
      one_pow, ENNReal.ofReal_one]
  have hbase : 1 ≤ max a 1 := le_max_right _ _
  have hPow : a ^ n ≤ (max a 1) ^ k := by
    calc
      a ^ n ≤ (max a 1) ^ n := by
        gcongr
        exact le_max_left _ _
      _ ≤ (max a 1) ^ k := pow_le_pow_right₀ hbase hnk
  calc
    x = ENNReal.ofReal (a ^ n) *
      (ENNReal.ofReal ((a⁻¹) ^ n) * x) := by
        rw [← mul_assoc, hprod, one_mul]
    _ ≤ ENNReal.ofReal (a ^ n) * y := by gcongr
    _ ≤ ENNReal.ofReal ((max a 1) ^ k) * y := by gcongr

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45
