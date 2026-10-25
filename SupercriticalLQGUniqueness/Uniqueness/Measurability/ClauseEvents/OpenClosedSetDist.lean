import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.Section3




 


set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents

private theorem measurable_iInf_of_isSigmaCompact {S : Set (ℂ × ℂ)}
    (hS : IsSigmaCompact S) :
    Measurable (fun D : LSCMetric => ⨅ p ∈ S, D p) := by
  obtain ⟨K, hK, hU⟩ := hS
  have hEach : ∀ n : ℕ,
      Measurable (fun D : LSCMetric => ⨅ p ∈ K n, D p) :=
    fun n => LSCMetric.measurable_iInf_of_isCompact (hK n)
  have hInf : Measurable (fun D : LSCMetric =>
      ⨅ n : ℕ, ⨅ p ∈ K n, D p) := Measurable.iInf hEach
  have heq : (fun D : LSCMetric => ⨅ p ∈ S, D p) =
      (fun D : LSCMetric => ⨅ n : ℕ, ⨅ p ∈ K n, D p) := by
    funext D
    rw [← hU]
    simp only [iInf_iUnion]
  exact heq.symm ▸ hInf

 
theorem measurable_setDist_open_closed (A B : Set ℂ)
    (hA : IsOpen A) (hB : IsClosed B) :
    Measurable (fun D : LSCMetric => OptimalConstants.Ratios.setDist D A B) := by
  let : LocallyCompactSpace A := hA.locallyCompactSpace
  let : LocallyCompactSpace B := hB.locallyCompactSpace
  let : SigmaCompactSpace A := inferInstance
  let : SigmaCompactSpace B := inferInstance
  let ι : A × B → ℂ × ℂ := fun p => ((p.1 : ℂ), (p.2 : ℂ))
  have hι : Continuous ι :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  have hrange : Set.range ι = A ×ˢ B := by
    ext p
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q.1.property, q.2.property⟩
    · rintro ⟨hp, hq⟩
      exact ⟨(⟨p.1, hp⟩, ⟨p.2, hq⟩), rfl⟩
  have hS : IsSigmaCompact (A ×ˢ B) := by
    rw [← hrange]
    exact isSigmaCompact_range hι
  simpa only [OptimalConstants.Ratios.setDist_eq_iInf_prod] using
    measurable_iInf_of_isSigmaCompact hS

end SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents
