import SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes.SetGeoHitBridge




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory unitInterval
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes
open LQGMetric (DistC)

theorem uniqueSetGeoCandidateHitsEvent_um
    {ι : Type} (Z : Finset ι) (O : ι → Set ℂ)
    (hO : ∀ i ∈ Z, IsOpen (O i))
    (D : DistC → LSCMetric) (hD : Measurable D)
    (K₁ K₂ : Set ℂ) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) :
    LQGMetric.UMeasurableSet
      {g : DistC |
        (∃! w : Measurability.GeodesicCodes.Path × (ℂ × ℂ),
          Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (D g, w)) ∧
        ∃ R : Measurability.GeodesicCodes.Path, ∃ u v : ℂ,
          Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (D g, (R, (u, v))) ∧
          ∀ i ∈ Z, ∃ q : unitInterval, R q ∈ O i} := by
  let W := Measurability.GeodesicCodes.Path × (ℂ × ℂ)
  let C : Set (LSCMetric × W) :=
    {p | Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ p ∧
      ∀ i ∈ Z, ∃ q : unitInterval, p.2.1 q ∈ O i}
  have hHit : MeasurableSet
      {p : LSCMetric × W |
        ∀ i ∈ Z, ∃ q : unitInterval, p.2.1 q ∈ O i} := by
    have hAll := Z.measurableSet_biInter (fun i hi =>
      ((setGeoCode_hit_open (O i) (hO i hi)).measurableSet).preimage
        ((measurable_fst.comp measurable_snd) :
          Measurable (fun p : LSCMetric × W => p.2.1)))
    convert hAll using 1
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
    rfl
  have hC : MeasurableSet C :=
    (Measurability.ClauseEvents.setGeoCandidate_measurable K₁ K₂ hK₁ hK₂).inter hHit
  have hExist : LQGMetric.UMeasurableSet
      {g : DistC | ∃ w : W, (D g, w) ∈ C} :=
    Measurability.GeodesicCodes.witnessProjection_um D hD hC
  have hUnique := uniqueSetGeoCandidateEvent_um D hD K₁ K₂ hK₁ hK₂
  have hAll := hUnique.inter hExist
  convert hAll using 1
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨hu, R, u, v, hR, hHits⟩
    exact ⟨hu, ⟨(R, (u, v)), hR, hHits⟩⟩
  · rintro ⟨hu, ⟨⟨R, ⟨u, v⟩⟩, hR, hHits⟩⟩
    exact ⟨hu, R, u, v, hR, hHits⟩

end SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes
