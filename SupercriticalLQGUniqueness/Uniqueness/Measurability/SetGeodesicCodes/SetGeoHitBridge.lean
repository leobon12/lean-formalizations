import SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes.SetGeoHit




 
set_option autoImplicit false
noncomputable section
open Set unitInterval MeasureTheory
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes

theorem uniqueSetGeodesic_hits_iff_code
    {ι : Type} (Z : Finset ι) (O : ι → Set ℂ)
    (D : LSCMetric) (K₁ K₂ : Set ℂ)
    (hforget : Continuous (euclidForget D)) :
    (∃ P : ℝ → ℂ, ∃ T : ℝ,
      EndSaving.FiniteEvents.UniqueSetGeodesic D K₁ K₂ P T ∧
      ∀ i ∈ Z, ∃ t ∈ Icc 0 T, P t ∈ O i) ↔
    ((∃! w : Measurability.GeodesicCodes.Path × (ℂ × ℂ),
      Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (D, w)) ∧
      ∃ R : Measurability.GeodesicCodes.Path, ∃ u v : ℂ,
        Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (D, (R, (u, v))) ∧
        ∀ i ∈ Z, ∃ q : unitInterval, R q ∈ O i) := by
  constructor
  · rintro ⟨P, T, hUnique, hHits⟩
    have hU : ∃! w : Measurability.GeodesicCodes.Path × (ℂ × ℂ),
        Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (D, w) :=
      (uniqueSetGeodesic_iff_unique_candidate D K₁ K₂ hforget).1
        ⟨P, T, hUnique⟩
    rcases hU with ⟨w, hw, huniq⟩
    obtain ⟨R, hR, hscaled⟩ :=
      setGeodesic_scaled_candidate D K₁ K₂ P T hforget hUnique.1
    refine ⟨⟨w, hw, huniq⟩, R, P 0, P T, hR, ?_⟩
    intro i hi
    obtain ⟨R', hR', hHitIff⟩ :=
      setGeodesic_hit_iff_code_hit D K₁ K₂ (O i) hforget P T hUnique.1
    have hEq : R' = R := by
      have hW := huniq (R', (P 0, P T)) hR'
      have hW0 := huniq (R, (P 0, P T)) hR
      exact congrArg Prod.fst (hW.trans hW0.symm)
    rw [← hEq]
    exact hHitIff.1 (hHits i hi)
  · rintro ⟨hU, R, u, v, hR, hHits⟩
    obtain ⟨P, T, hP, hscaled⟩ :=
      setGeoCandidate_has_scaled_source D K₁ K₂ R u v hR
    obtain ⟨P', T', hUnique⟩ :=
      (uniqueSetGeodesic_iff_unique_candidate D K₁ K₂ hforget).2 hU
    have hEq := hUnique.2 P T hP
    refine ⟨P', T', hUnique, ?_⟩
    intro i hi
    obtain ⟨q, hRq⟩ := hHits i hi
    have htime : T * (q : ℝ) ∈ Icc 0 T :=
      ⟨mul_nonneg hP.1.1.1 q.2.1,
        mul_le_of_le_one_right hP.1.1.1 q.2.2⟩
    have ht' : T' * (q : ℝ) ∈ Icc 0 T' := by
      simpa only [← hEq.1] using htime
    refine ⟨T' * (q : ℝ), ht', ?_⟩
    have hPq : P' (T' * (q : ℝ)) = R q :=
      (hEq.2 ht').symm.trans (by simpa only [hEq.1] using hscaled q)
    exact hPq ▸ hRq

end SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes
