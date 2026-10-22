import HigherDimLQGMetric.B3.Interfaces
import HigherDimLQGMetric.LfppTight.MedianBasics
import HigherDimLFPP.Exist.Quantile
import LQGMetric.Prob.Median

/-!
# Lower medians for the limits packet

The B3 interface uses a lower median of a real random variable.  These lemmas
identify it with the pinned quantile API and record positivity for positive
random variables.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HigherDimLQGMetric

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The interface median agrees with the lower quantile of the pushforward law. -/
theorem l6c_lowerMedian_eq_lowerQuantile {X : Ω → ℝ} (hX : AEMeasurable X P) :
    lowerMedian P X = LQGMetric.lowerQuantile (P.map X) (2 : ℝ≥0∞)⁻¹ :=
  l6a_lowerMedian_eq_lowerQuantile_map P X hX

/-- A lower median of an almost surely positive random variable is positive. -/
theorem l6c_lowerMedian_pos [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : AEMeasurable X P) (hpos : ∀ᵐ ω ∂P, 0 < X ω) :
    0 < lowerMedian P X := l6a_lowerMedian_pos P X hX hpos

/-- The median threshold is characterized by the corresponding closed tail. -/
theorem l6c_half_le_measure_iff_lowerMedian_le [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P) {t : ℝ} :
    (2 : ℝ≥0∞)⁻¹ ≤ P {ω | X ω ≤ t} ↔ lowerMedian P X ≤ t := by
  rw [l6c_lowerMedian_eq_lowerQuantile hX,
    ← LQGMetric.le_measure_Iic_iff_lowerQuantile_le
      LQGMetric.inv_two_pos' LQGMetric.inv_two_lt_one']
  rw [Measure.map_apply_of_aemeasurable hX measurableSet_Iic]
  rfl

/-- A positive deterministic scale multiplies the lower median exactly. -/
theorem l6c_lowerMedian_const_mul [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P) {a : ℝ} (ha : 0 < a) :
    lowerMedian P (fun ω => a * X ω) = a * lowerMedian P X := by
  have hY : AEMeasurable (fun ω => a * X ω) P := aemeasurable_const.mul hX
  apply le_antisymm
  · apply (l6c_half_le_measure_iff_lowerMedian_le hY).mp
    have h := (l6c_half_le_measure_iff_lowerMedian_le hX).mpr (le_refl _)
    have heq : {ω | a * X ω ≤ a * lowerMedian P X} =
        {ω | X ω ≤ lowerMedian P X} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      constructor
      · exact fun hω => le_of_mul_le_mul_left hω ha
      · exact fun hω => mul_le_mul_of_nonneg_left hω ha.le
    rw [heq]
    exact h
  · have h := (l6c_half_le_measure_iff_lowerMedian_le hY).mpr (le_refl _)
    have h' : (2 : ℝ≥0∞)⁻¹ ≤
        P {ω | X ω ≤ (lowerMedian P (fun ω => a * X ω)) / a} := by
      have heq : {ω | X ω ≤ (lowerMedian P (fun ω => a * X ω)) / a} =
          {ω | a * X ω ≤ lowerMedian P (fun ω => a * X ω)} := by
        ext ω
        simp only [Set.mem_ofPred_eq]
        constructor
        · intro hω
          simpa only [mul_comm] using (le_div_iff₀ ha).mp hω
        · intro hω
          exact (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hω)
      rw [heq]
      exact h
    have hq := (l6c_half_le_measure_iff_lowerMedian_le hX).mp h'
    simpa only [mul_comm] using (le_div_iff₀ ha).mp hq

/-- A lower median can be calculated after pushing forward the law. -/
theorem l6c_lowerMedian_map {E : Type*} [MeasurableSpace E]
    [IsProbabilityMeasure P] {X : Ω → E} (hX : AEMeasurable X P)
    {e : E → ℝ} (he : Measurable e) :
    lowerMedian (P.map X) e = lowerMedian P (fun ω => e (X ω)) := by
  unfold lowerMedian
  congr 1
  ext t
  simp only [Set.mem_ofPred_eq]
  change (2 : ℝ≥0∞)⁻¹ ≤ (P.map X) (e ⁻¹' Set.Iic t) ↔ _
  rw [Measure.map_apply_of_aemeasurable hX
    (he measurableSet_Iic)]
  rfl

end HigherDimLQGMetric
