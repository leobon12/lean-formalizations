import SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents.ExcursionUnit




 
set_option autoImplicit false
noncomputable section
open Set
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents

theorem excursion_congr_on (P Q : ℝ → ℂ) (T : ℝ)
    (O : Set ℂ) (V : TopologicalSpace.Opens ℂ)
    (τ' τ σ σ' : ℝ) (h : Set.EqOn P Q (Icc 0 T)) :
    EndSaving.Interfaces.Excursion P T O V τ' τ σ σ' ↔
      EndSaving.Interfaces.Excursion Q T O V τ' τ σ σ' := by
  have forward (A B : ℝ → ℂ) (hab : Set.EqOn A B (Icc 0 T)) :
      EndSaving.Interfaces.Excursion A T O V τ' τ σ σ' →
        EndSaving.Interfaces.Excursion B T O V τ' τ σ σ' := by
    have hpoint (t : ℝ) (ht : t ∈ Icc 0 T) : A t = B t := hab ht
    rintro ⟨h0, h12, h23, h34, h4T, hf1, hf2, hin, hV1, hV2, hno1, hno2⟩
    have ht1 : τ' ∈ Icc 0 T := ⟨h0, (h12.trans (h23.trans (h34.trans h4T)))⟩
    have ht2 : τ ∈ Icc 0 T := ⟨h0.trans h12, h23.trans (h34.trans h4T)⟩
    have ht3 : σ ∈ Icc 0 T := ⟨h0.trans (h12.trans h23), h34.trans h4T⟩
    have ht4 : σ' ∈ Icc 0 T := ⟨h0.trans (h12.trans (h23.trans h34)), h4T⟩
    refine ⟨h0, h12, h23, h34, h4T, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hpoint τ' ht1]; exact hf1
    · rw [← hpoint σ' ht4]; exact hf2
    · intro t ht
      rw [← hpoint t ⟨h0.trans ht.1.le, ht.2.le.trans h4T⟩]
      exact hin t ht
    · rw [← hpoint τ ht2]; exact hV1
    · rw [← hpoint σ ht3]; exact hV2
    · intro t ht
      rw [← hpoint t ⟨h0.trans ht.1.le, ht.2.le.trans (h23.trans (h34.trans h4T))⟩]
      exact hno1 t ht
    · intro t ht
      rw [← hpoint t ⟨h0.trans (h12.trans (h23.trans ht.1.le)), ht.2.le.trans h4T⟩]
      exact hno2 t ht
  exact ⟨forward P Q h, forward Q P h.symm⟩

end SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents
