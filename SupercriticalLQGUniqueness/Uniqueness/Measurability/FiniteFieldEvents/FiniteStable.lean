import SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents.LocalCircleStable




 
set_option autoImplicit false
noncomputable section
open Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents

theorem uniqueStable_finite_iff
    {ι : Type} (Z : Finset ι) (Db Da : LSCMetric)
    (K₁ K₂ : Set ℂ) (W : ι → Set ℂ)
    (V : ι → TopologicalSpace.Opens ℂ) (L : ι → ℝ≥0∞) :
    (∃ P : ℝ → ℂ, ∃ T : ℝ,
      EndSaving.FiniteEvents.UniqueSetGeodesic Db K₁ K₂ P T ∧
      ∀ i ∈ Z, SourceStable Da P T (W i) (V i) (L i)) ↔
    ((∃ P : ℝ → ℂ, ∃ T : ℝ,
      EndSaving.FiniteEvents.UniqueSetGeodesic Db K₁ K₂ P T) ∧
      ∀ i ∈ Z, ∃ P : ℝ → ℂ, ∃ T : ℝ,
        EndSaving.FiniteEvents.UniqueSetGeodesic Db K₁ K₂ P T ∧
        SourceStable Da P T (W i) (V i) (L i)) := by
  constructor
  · rintro ⟨P, T, hUnique, hAll⟩
    exact ⟨⟨P, T, hUnique⟩, fun i hi => ⟨P, T, hUnique, hAll i hi⟩⟩
  · rintro ⟨⟨P, T, hUnique⟩, hEach⟩
    refine ⟨P, T, hUnique, ?_⟩
    intro i hi
    obtain ⟨Pi, Ti, hUniqueI, hStableI⟩ := hEach i hi
    obtain ⟨hTi, hEq⟩ := hUnique.2 Pi Ti hUniqueI.1
    subst Ti
    exact (sourceStable_congr_on Da Pi P T (W i) (V i) (L i) hEq).1 hStableI

end SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents
