import MatedCRTHarmonic.CellFamily.Core

/-!
# Outer-measure union bounds for the scaled-grid estimate

These lemmas use `Measure` on arbitrary sets, hence its underlying outer measure. They require no
measurability of the good or bad events.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRTHarmonic.CellFamily

/-- Convert a lower probability bound on a measurable good event into an upper bound on its bad
complement. This adapter is only for legacy good-event hypotheses. -/
theorem measure_compl_le_of_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {A : Set Ω} (hA : MeasurableSet A)
    {δ : ℝ≥0∞} (hlower : 1 - δ ≤ μ A) : μ Aᶜ ≤ δ := by
  have hsum := measure_add_measure_compl (μ := μ) hA
  have hsum' : μ Aᶜ + μ A = 1 := by simpa [add_comm] using hsum
  have hlow : 1 ≤ δ + μ A := (tsub_le_iff_left).1 hlower
  have hle : μ Aᶜ + μ A ≤ δ + μ A := by
    rw [hsum']
    simpa [add_comm] using hlow
  exact (ENNReal.add_le_add_iff_right (ne_of_lt (by
    calc
      μ A ≤ μ Set.univ := measure_mono (subset_univ A)
      _ = 1 := measure_univ
      _ < ⊤ := ENNReal.one_lt_top))).mp hle

/-- If the outer measure of a bad event is at most `δ`, the outer measure of its complement is at
least `1 - δ` in a probability space. -/
theorem measure_compl_ge_one_sub_of_upper {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {A : Set Ω} {δ : ℝ≥0∞}
    (hbad : μ Aᶜ ≤ δ) : 1 - δ ≤ μ A := by
  have hcover : Set.univ ⊆ A ∪ Aᶜ := by
    intro ω _
    simp
  have htotal : 1 ≤ μ A + μ Aᶜ := by
    calc
      1 = μ Set.univ := by rw [measure_univ]
      _ ≤ μ (A ∪ Aᶜ) := measure_mono hcover
      _ ≤ μ A + μ Aᶜ := measure_union_le A Aᶜ
  apply (tsub_le_iff_left).2
  calc
    1 ≤ μ A + δ := by
      calc
        1 ≤ μ A + μ Aᶜ := htotal
        _ ≤ μ A + δ := by simpa [add_comm] using add_le_add_right hbad (μ A)
    _ = δ + μ A := by ac_rfl

/-- Outer-measure union bound for the complement of a finite intersection. -/
theorem measure_finset_iInter_compl_le_sum {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Finset ι) (E : ι → Set Ω) :
    μ (⋂ i ∈ s, E i)ᶜ ≤ ∑ i ∈ s, μ (E i)ᶜ := by
  have heq : (⋂ i ∈ s, E i)ᶜ = ⋃ i ∈ s, (E i)ᶜ := by
    ext ω
    simp
  rw [heq]
  exact measure_biUnion_finset_le s (fun i => (E i)ᶜ)

/-- Finite-intersection outer-measure bound when each bad event has a common upper bound. -/
theorem measure_finset_iInter_compl_le_card_mul {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Finset ι) (E : ι → Set Ω) {δ : ℝ≥0∞}
    (hbad : ∀ i ∈ s, μ (E i)ᶜ ≤ δ) :
    μ (⋂ i ∈ s, E i)ᶜ ≤ (s.card : ℝ≥0∞) * δ := by
  calc
    μ (⋂ i ∈ s, E i)ᶜ ≤ ∑ i ∈ s, μ (E i)ᶜ :=
      measure_finset_iInter_compl_le_sum μ s E
    _ ≤ ∑ i ∈ s, δ := by
      exact Finset.sum_le_sum hbad
    _ = (s.card : ℝ≥0∞) * δ := by simp [Finset.sum_const, nsmul_eq_mul]

end MatedCRTHarmonic.CellFamily
