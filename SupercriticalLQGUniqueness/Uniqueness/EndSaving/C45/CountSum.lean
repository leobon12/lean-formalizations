import SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45.RawRNNullMeasurable




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Finset
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45

 
theorem tsum_measure_le_of_ae_finite_occupancy
    {Ω ι : Type} [MeasurableSpace Ω] [Countable ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (M : ℕ)
    (hocc : ∀ᵐ ω ∂P, ∀ s : Finset ι,
      Set.ncard ((s : Set ι) ∩ {i | ω ∈ A i}) ≤ M) :
    (∑' i, P (A i)) ≤ M := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro s
  have hsum : (∑ i ∈ s, P (A i)) =
      ∫⁻ ω, ∑ i ∈ s, (A i).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
    rw [lintegral_finsetSum s]
    · apply Finset.sum_congr rfl
      intro i hi
      simp [lintegral_indicator (hA i)]
    · intro i hi
      exact (measurable_const.indicator (hA i))
  rw [hsum]
  calc
    (∫⁻ ω, ∑ i ∈ s, (A i).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P)
        ≤ ∫⁻ _ω, (M : ℝ≥0∞) ∂P := by
          apply lintegral_mono_ae
          filter_upwards [hocc] with ω hω
          have heq : (∑ i ∈ s, (A i).indicator (fun _ => (1 : ℝ≥0∞)) ω) =
              ((s.filter fun i => ω ∈ A i).card : ℝ≥0∞) := by
            simp [Set.indicator_apply]
          rw [heq]
          have hcard :
              (s.filter fun i => ω ∈ A i).card =
                Set.ncard ((s : Set ι) ∩ {i | ω ∈ A i}) := by
            rw [← Set.ncard_coe_finset (s.filter fun i => ω ∈ A i)]
            congr 1
            ext i
            simp
          rw [hcard]
          exact_mod_cast hω s
    _ = M := by simp

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45
