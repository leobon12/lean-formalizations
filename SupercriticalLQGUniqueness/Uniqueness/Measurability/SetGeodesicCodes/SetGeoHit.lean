import SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes.RawUniqueMeas




 
set_option autoImplicit false
noncomputable section
open Set unitInterval MeasureTheory
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes

theorem setGeoCode_hit_open (O : Set ℂ) (hO : IsOpen O) :
    IsOpen {R : Measurability.GeodesicCodes.Path | ∃ q : unitInterval, R q ∈ O} := by
  have heq : {R : Measurability.GeodesicCodes.Path | ∃ q : unitInterval, R q ∈ O} =
      ⋃ q : unitInterval, {R : Measurability.GeodesicCodes.Path | R q ∈ O} := by
    ext R
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [heq]
  apply isOpen_iUnion
  intro q
  exact hO.preimage (continuous_eval_const q)

theorem setGeodesic_hit_iff_code_hit
    (D : LSCMetric) (K₁ K₂ O : Set ℂ)
    (hforget : Continuous (euclidForget D))
    (P : ℝ → ℂ) (T : ℝ)
    (hSet : EndSaving.FiniteEvents.SetGeodesic D K₁ K₂ P T) :
    ∃ R : Measurability.GeodesicCodes.Path,
      Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (D, (R, (P 0, P T))) ∧
      ((∃ t ∈ Icc 0 T, P t ∈ O) ↔
        ∃ q : unitInterval, R q ∈ O) := by
  obtain ⟨R, hR, hscaled⟩ :=
    setGeodesic_scaled_candidate D K₁ K₂ P T hforget hSet
  refine ⟨R, hR, ?_⟩
  constructor
  · rintro ⟨t, ht, hPt⟩
    have hT : 0 ≤ T := hSet.1.1.1
    rcases hT.eq_or_lt with hzero | hpos
    · have ht0 : t = 0 := le_antisymm (hzero ▸ ht.2) ht.1
      refine ⟨0, ?_⟩
      simpa [hscaled, ht0] using hPt
    · let q : unitInterval := ⟨t / T,
        ⟨div_nonneg ht.1 hT, (div_le_one hpos).mpr ht.2⟩⟩
      refine ⟨q, ?_⟩
      have htime : T * (q : ℝ) = t := by
        change T * (t / T) = t
        field_simp
      rw [hscaled, htime]
      exact hPt
  · rintro ⟨q, hRq⟩
    refine ⟨T * (q : ℝ), ?_, ?_⟩
    · exact ⟨mul_nonneg hSet.1.1.1 q.2.1,
        mul_le_of_le_one_right hSet.1.1.1 q.2.2⟩
    · rwa [hscaled] at hRq

end SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes
