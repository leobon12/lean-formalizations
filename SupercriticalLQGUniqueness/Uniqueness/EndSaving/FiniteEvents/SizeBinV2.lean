import SupercriticalLQGUniqueness.Uniqueness.EndSaving.FiniteEvents.FiniteEventsV2




 
set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.FiniteEvents

 

theorem localSizeBin_upper_ennreal
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (r b q : Set.Ioi (0 : ℝ)) (hrz hbr : ℝ)
    (hsize : LocalSizeBin ξ Q r b q hrz hbr) :
    ENNReal.ofReal ((r : ℝ) ^ ((ξ : ℝ) * Q) *
      Real.exp ((ξ : ℝ) * hrz)) ≤
      2 * ENNReal.ofReal ((q : ℝ) * (b : ℝ) ^ ((ξ : ℝ) * Q) *
        Real.exp ((ξ : ℝ) * hbr)) := by
  have hreal :
      (r : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hrz) ≤
        2 * ((q : ℝ) * (b : ℝ) ^ ((ξ : ℝ) * Q) *
          Real.exp ((ξ : ℝ) * hbr)) := by
    simpa only [LocalSizeBin, mul_assoc] using hsize.2
  calc
    _ ≤ ENNReal.ofReal (2 * ((q : ℝ) * (b : ℝ) ^ ((ξ : ℝ) * Q) *
          Real.exp ((ξ : ℝ) * hbr))) := ENNReal.ofReal_le_ofReal hreal
    _ = 2 * ENNReal.ofReal ((q : ℝ) * (b : ℝ) ^ ((ξ : ℝ) * Q) *
          Real.exp ((ξ : ℝ) * hbr)) := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      norm_num

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.FiniteEvents
