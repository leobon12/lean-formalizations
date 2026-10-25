import SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45.CountMarkov




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Finset
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45

theorem card_le_tsum_indicator_of_family
    {Ω ι : Type} [Countable ι] (A : ι → Set Ω)
    (ω : Ω) (F : Finset ι)
    (hF : ∀ i ∈ F, ω ∈ A i) :
    (F.card : ℝ≥0∞) ≤
      ∑' i, (A i).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  have hs : (∑ i ∈ F, (1 : ℝ≥0∞)) ≤
      ∑' i, (A i).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    calc
      (∑ i ∈ F, (1 : ℝ≥0∞)) =
          ∑ i ∈ F, (A i).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [hF i hi]
      _ ≤ _ := ENNReal.sum_le_tsum F
  simpa using hs

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.C45
