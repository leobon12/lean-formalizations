import SupercriticalLQGUniqueness.Uniqueness.Objects.Compare.CompareGeometry




 

set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Compare

private theorem compareScale_eq (k : ℕ) :
    Objects.CorrectedEvent.compareScale k = ((20 : ℝ) / 21) ^ k := by
  unfold Objects.CorrectedEvent.compareScale
  rw [show (21 : ℝ) / 20 = ((20 : ℝ) / 21)⁻¹ by norm_num,
    Real.inv_rpow (by norm_num : 0 ≤ (20 : ℝ) / 21)]
  norm_num

 
theorem exists_compare_scale {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ (20 : ℝ) / 21) :
    ∃ k : ℕ, 0 < Objects.CorrectedEvent.compareScale k ∧
      δ / ((21 : ℝ) / 20) < Objects.CorrectedEvent.compareScale k ∧
      Objects.CorrectedEvent.compareScale k ≤ δ := by
  have hδone : δ ≤ 1 := hδle.trans (by norm_num)
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near_of_lt_one hδ hδone
    (by norm_num : 0 < (20 : ℝ) / 21) (by norm_num : (20 : ℝ) / 21 < 1)
  rcases lt_or_eq_of_le hn2 with hlt | heq
  · refine ⟨n+1, ?_, ?_, ?_⟩
    · rw [compareScale_eq]
      positivity
    · rw [compareScale_eq]
      have hbase : 0 < (20 : ℝ) / 21 := by norm_num
      have h := mul_lt_mul_of_pos_right hlt hbase
      have heq' : δ / ((21 : ℝ) / 20) = δ * ((20 : ℝ) / 21) := by ring
      rw [heq']
      simpa only [pow_succ] using h
    · rw [compareScale_eq]
      exact hn1.le
  · refine ⟨n, ?_, ?_, ?_⟩
    · rw [compareScale_eq, ← heq]
      exact hδ
    · rw [compareScale_eq, ← heq]
      exact div_lt_self hδ (by norm_num)
    · rw [compareScale_eq, ← heq]


end SupercriticalLQGUniqueness.Uniqueness.Objects.Compare
