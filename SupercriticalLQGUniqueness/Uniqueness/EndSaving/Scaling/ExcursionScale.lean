import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling.GeodesicScale




 


set_option autoImplicit false
noncomputable section
open Set
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling

theorem excursion_rescale
    (P : ℝ → ℂ) (T : ℝ) (O : Set ℂ) (V : TopologicalSpace.Opens ℂ)
    (τ' τ σ σ' k : ℝ) (hk : 0 < k)
    (hex : EndSaving.Interfaces.Excursion P T O V τ' τ σ σ') :
    EndSaving.Interfaces.Excursion (P ∘ fun t => t / k) (k * T) O V
      (k * τ') (k * τ) (k * σ) (k * σ') := by
  rcases hex with ⟨h0, h12, h23, h34, h4T, hfr1, hfr2,
    hinside, hτ, hσ, hno1, hno2⟩
  have htime (s : ℝ) : (k * s) / k = s := by field_simp
  refine ⟨mul_nonneg hk.le h0, mul_le_mul_of_nonneg_left h12 hk.le,
    mul_le_mul_of_nonneg_left h23 hk.le,
    mul_le_mul_of_nonneg_left h34 hk.le,
    mul_le_mul_of_nonneg_left h4T hk.le, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Function.comp_def, htime] using hfr1
  · simpa only [Function.comp_def, htime] using hfr2
  · intro t ht
    have ht' : t / k ∈ Ioo τ' σ' := by
      constructor
      · exact (lt_div_iff₀ hk).2 (by nlinarith [ht.1])
      · exact (div_lt_iff₀ hk).2 (by nlinarith [ht.2])
    exact hinside _ ht'
  · simpa only [Function.comp_def, htime] using hτ
  · simpa only [Function.comp_def, htime] using hσ
  · intro t ht
    have ht' : t / k ∈ Ioo τ' τ := by
      constructor
      · exact (lt_div_iff₀ hk).2 (by nlinarith [ht.1])
      · exact (div_lt_iff₀ hk).2 (by nlinarith [ht.2])
    exact hno1 _ ht'
  · intro t ht
    have ht' : t / k ∈ Ioo σ σ' := by
      constructor
      · exact (lt_div_iff₀ hk).2 (by nlinarith [ht.1])
      · exact (div_lt_iff₀ hk).2 (by nlinarith [ht.2])
    exact hno2 _ ht'

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling
