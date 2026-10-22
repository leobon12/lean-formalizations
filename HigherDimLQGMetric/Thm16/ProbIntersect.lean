import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Three uniformly small bad events and one null event leave a sample. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

theorem l9c_exists_good_four {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {A B C N : Set Ω}
    (hA : P A < (8⁻¹ : ℝ≥0∞))
    (hB : P B < (8⁻¹ : ℝ≥0∞))
    (hC : P C < (8⁻¹ : ℝ≥0∞))
    (hN : P N = 0) :
    ∃ ω : Ω, ω ∉ A ∧ ω ∉ B ∧ ω ∉ C ∧ ω ∉ N := by
  by_contra hn
  have hcover : (univ : Set Ω) ⊆ A ∪ B ∪ C ∪ N := by
    intro ω _
    by_contra hω
    apply hn
    simp only [mem_union, not_or] at hω
    exact ⟨ω, hω.1.1.1, hω.1.1.2, hω.1.2, hω.2⟩
  have hle : (1 : ℝ≥0∞) ≤ P (A ∪ B ∪ C ∪ N) := by
    calc
      (1 : ℝ≥0∞) = P univ := by simp
      _ ≤ _ := measure_mono hcover
  have hsum : P (A ∪ B ∪ C ∪ N) ≤ P A + P B + P C + P N := by
    calc
      P (A ∪ B ∪ C ∪ N) ≤ P (A ∪ B ∪ C) + P N := measure_union_le _ _
      _ ≤ (P (A ∪ B) + P C) + P N := by
        gcongr
        exact measure_union_le _ _
      _ ≤ (P A + P B + P C) + P N := by
        gcongr
        exact measure_union_le _ _
      _ = P A + P B + P C + P N := by ac_rfl
  have hlt : P A + P B + P C + P N < (1 : ℝ≥0∞) := by
    rw [hN, add_zero]
    calc
      P A + P B + P C < (8⁻¹ : ℝ≥0∞) + 8⁻¹ + 8⁻¹ := by
        gcongr
      _ < 1 := by
        rw [← ENNReal.ofReal_ofNat 8,
          ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 8)]
        norm_num [← ENNReal.ofReal_add]
  exact (not_lt_of_ge (hle.trans hsum)) hlt

end HigherDimLQGMetric
