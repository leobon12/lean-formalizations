import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! A half-probability event meets two events whose complements have small mass. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

theorem l9c_exists_half_good {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {A B C N : Set Ω}
    (hA : (2⁻¹ : ℝ≥0∞) ≤ P A)
    (hB : P B ≤ (8⁻¹ : ℝ≥0∞))
    (hC : P C ≤ (8⁻¹ : ℝ≥0∞))
    (hN : P N = 0) :
    ∃ ω : Ω, ω ∈ A ∧ ω ∉ B ∧ ω ∉ C ∧ ω ∉ N := by
  by_contra hn
  have hcover : A ⊆ B ∪ C ∪ N := by
    intro ω hω
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    exact hn ⟨ω, hω, hnot.1.1, hnot.1.2, hnot.2⟩
  have hle : (2⁻¹ : ℝ≥0∞) ≤ P B + P C + P N := by
    calc
      (2⁻¹ : ℝ≥0∞) ≤ P A := hA
      _ ≤ P (B ∪ C ∪ N) := measure_mono hcover
      _ ≤ P B + P C + P N := by
        calc
          P (B ∪ C ∪ N) ≤ P (B ∪ C) + P N := measure_union_le _ _
          _ ≤ (P B + P C) + P N := by gcongr; exact measure_union_le _ _
  have hlt : P B + P C + P N < (2⁻¹ : ℝ≥0∞) := by
    rw [hN, add_zero]
    calc
      P B + P C ≤ (8⁻¹ : ℝ≥0∞) + 8⁻¹ := add_le_add hB hC
      _ < 2⁻¹ := by
        rw [← ENNReal.ofReal_ofNat 8, ← ENNReal.ofReal_ofNat 2,
          ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 8),
          ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        norm_num
  exact (not_lt_of_ge hle) hlt

end HigherDimLQGMetric
