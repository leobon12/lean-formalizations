import HigherDimLQGMetric.LfppTight.MedianBasics
import HigherDimLFPP.Exist.CrudeBounds

/-!
# Lower medians of products with two tight positive factors

The lower-median comparison in MA5 A7 needs a strict probability margin.
Two exceptional probabilities at most `1/8` leave a product interval with
probability at least `3/4`, which suffices for the lower median.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

/-- If each factor lies in `[m,M]` outside an event of probability at most
`1/8`, the lower median of their product lies in `[m²,M²]`. -/
theorem l6a_lowerMedian_product_bounds {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : Ω → ℝ) (hAB : AEMeasurable (fun ω => A ω * B ω) P)
    {m M : ℝ} (hm : 0 ≤ m) (hM : 0 ≤ M)
    (hA : P {ω | A ω < m ∨ M < A ω} ≤ (8⁻¹ : ℝ≥0∞))
    (hB : P {ω | B ω < m ∨ M < B ω} ≤ (8⁻¹ : ℝ≥0∞)) :
    m ^ 2 ≤ lowerMedian P (fun ω => A ω * B ω) ∧
      lowerMedian P (fun ω => A ω * B ω) ≤ M ^ 2 := by
  have hbad : P {ω | A ω * B ω < m ^ 2 ∨ M ^ 2 < A ω * B ω} ≤
      (4⁻¹ : ℝ≥0∞) := by
    have hsub : {ω | A ω * B ω < m ^ 2 ∨ M ^ 2 < A ω * B ω} ⊆
        {ω | A ω < m ∨ M < A ω} ∪ {ω | B ω < m ∨ M < B ω} := by
      intro ω hω
      by_contra hnot
      simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hnot
      obtain ⟨hAm, hAM⟩ := hnot.1
      obtain ⟨hBm, hBM⟩ := hnot.2
      have hlow : m ^ 2 ≤ A ω * B ω := by
        calc m ^ 2 = m * m := pow_two m
          _ ≤ A ω * B ω := mul_le_mul hAm hBm hm (le_trans hm hAm)
      have hupp : A ω * B ω ≤ M ^ 2 := by
        calc A ω * B ω ≤ M * M := mul_le_mul hAM hBM (le_trans hm hBm) hM
          _ = M ^ 2 := (pow_two M).symm
      exact hω.elim (fun h => (not_lt_of_ge hlow) h)
        (fun h => (not_lt_of_ge hupp) h)
    calc
      P {ω | A ω * B ω < m ^ 2 ∨ M ^ 2 < A ω * B ω} ≤
          P ({ω | A ω < m ∨ M < A ω} ∪ {ω | B ω < m ∨ M < B ω}) :=
            measure_mono hsub
      _ ≤ P {ω | A ω < m ∨ M < A ω} + P {ω | B ω < m ∨ M < B ω} :=
        measure_union_le _ _
      _ ≤ (8⁻¹ : ℝ≥0∞) + 8⁻¹ := add_le_add hA hB
      _ = (4⁻¹ : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_ofNat 8, ← ENNReal.ofReal_ofNat 4,
          ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 8),
          ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 4),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        norm_num
  rw [l6a_lowerMedian_eq_lowerQuantile_map P _ hAB]
  exact HigherDimLFPP.Crude.lowerQuantile_mem_Icc_of_measure_le hAB
    (by norm_num : (0 : ℝ≥0∞) < 2⁻¹)
    (by norm_num : (2⁻¹ : ℝ≥0∞) < 1)
    (by norm_num : (4⁻¹ : ℝ≥0∞) < 2⁻¹)
    (by norm_num : (4⁻¹ : ℝ≥0∞) ≤ 1 - 2⁻¹) hbad

end HigherDimLQGMetric
