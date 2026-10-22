import HigherDimLQGMetric.LfppTight.TightRandomScale

/-! Uniform absolute tails give tightness of a real-valued random family. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

theorem l6a_tight_scalar_of_abs_tail {ι Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Set ι) (X : ι → Ω → ℝ)
    (hXm : ∀ i ∈ S, AEMeasurable (X i) P)
    (hTail : ∀ θ : ℝ, 0 < θ → ∃ M : ℝ, 0 ≤ M ∧
      ∀ i ∈ S, P {ω | M < |X i ω|} ≤ ENNReal.ofReal θ) :
    IsTightMeasureSet {ν : Measure ℝ | ∃ i ∈ S, ν = P.map (X i)} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨θ, hθ, hθε⟩ : ∃ θ : ℝ, 0 < θ ∧ ENNReal.ofReal θ ≤ ε := by
    rcases eq_top_or_lt_top ε with rfl | hfin
    · exact ⟨1, by norm_num, by simp⟩
    · refine ⟨ε.toReal, ENNReal.toReal_pos hε.ne' hfin.ne, ?_⟩
      rw [ENNReal.ofReal_toReal hfin.ne]
  obtain ⟨M, hM, hbound⟩ := hTail θ hθ
  refine ⟨Icc (-M) M, isCompact_Icc, ?_⟩
  rintro ν ⟨i, hi, rfl⟩
  rw [Measure.map_apply_of_aemeasurable (hXm i hi) isCompact_Icc.isClosed.measurableSet.compl]
  have hset : (X i) ⁻¹' (Icc (-M) M)ᶜ = {ω | M < |X i ω|} := by
    ext ω
    simp only [mem_preimage, mem_compl_iff, mem_Icc, mem_ofPred_eq]
    rw [← abs_le]
    exact not_le
  rw [hset]
  exact (hbound i hi).trans hθε

end HigherDimLQGMetric
