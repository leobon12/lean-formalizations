import SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes.UniqueHitsMeas




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory unitInterval
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes
open LQGMetric (DistC TestC)

theorem rawUniqueSetGeodesicHits_nullMeasurable
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    {ξ : Set.Ioi (0 : ℝ)} {Qpar : ℝ} {D : DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Qpar D)
    (K₁ K₂ : Set ℂ) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    {ι : Type} (Z : Finset ι) (O : ι → Set ℂ)
    (hO : ∀ i ∈ Z, IsOpen (O i)) :
    NullMeasurableSet
      {g : DistC | ∃ P' : ℝ → ℂ, ∃ T : ℝ,
        EndSaving.FiniteEvents.UniqueSetGeodesic (D g) K₁ K₂ P' T ∧
        ∀ i ∈ Z, ∃ t ∈ Icc 0 T, P' t ∈ O i}
      (P.map h) := by
  let E : Set DistC :=
    {g | (∃! w : Measurability.GeodesicCodes.Path × (ℂ × ℂ),
      Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (D g, w)) ∧
      ∃ R : Measurability.GeodesicCodes.Path, ∃ u v : ℂ,
        Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (D g, (R, (u, v))) ∧
        ∀ i ∈ Z, ∃ q : unitInterval, R q ∈ O i}
  have hE : LQGMetric.UMeasurableSet E :=
    uniqueSetGeoCandidateHitsEvent_um Z O hO D hD.1 K₁ K₂ hK₁ hK₂
  have hcanonical : IsNormalizedWholePlaneGFF
      (id : DistC → DistC) (P.map h) := normalizedGFF_id_map P h hh
  have hae :
      {g : DistC | ∃ P' : ℝ → ℂ, ∃ T : ℝ,
        EndSaving.FiniteEvents.UniqueSetGeodesic (D g) K₁ K₂ P' T ∧
        ∀ i ∈ Z, ∃ t ∈ Icc 0 T, P' t ∈ O i} =ᵐ[P.map h] E := by
    filter_upwards [Toolkit.WeylShift.ae_common_weyl_sample hD (P.map h) id hcanonical]
      with g hg
    exact propext (uniqueSetGeodesic_hits_iff_code Z O
      (D g) K₁ K₂ hg.1)
  exact (hE.nullMeasurableSet (P.map h)).congr hae.symm

theorem rawUniqueSetGeodesicHits_shifted_nullMeasurable
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    {ξ : Set.Ioi (0 : ℝ)} {Qpar : ℝ} {D : DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Qpar D)
    (K₁ K₂ : Set ℂ) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    {ι : Type} (Z : Finset ι) (O : ι → Set ℂ)
    (hO : ∀ i ∈ Z, IsOpen (O i)) (φ : TestC) :
    NullMeasurableSet
      {g : DistC | ∃ P' : ℝ → ℂ, ∃ T : ℝ,
        EndSaving.FiniteEvents.UniqueSetGeodesic
          (D (LQGMetric.GM.subTest g φ)) K₁ K₂ P' T ∧
        ∀ i ∈ Z, ∃ t ∈ Icc 0 T, P' t ∈ O i}
      (P.map h) := by
  let E : Set DistC :=
    {g | (∃! w : Measurability.GeodesicCodes.Path × (ℂ × ℂ),
      Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (D g, w)) ∧
      ∃ R : Measurability.GeodesicCodes.Path, ∃ u v : ℂ,
        Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (D g, (R, (u, v))) ∧
        ∀ i ∈ Z, ∃ q : unitInterval, R q ∈ O i}
  have hE : LQGMetric.UMeasurableSet E :=
    uniqueSetGeoCandidateHitsEvent_um Z O hO D hD.1 K₁ K₂ hK₁ hK₂
  have hShift : Measurable (fun g : DistC => LQGMetric.GM.subTest g φ) := by
    change Measurable (fun g : DistC =>
      LQGMetric.addFun g (-LQGMetric.testCont φ))
    exact LQGMetric.measurable_addFun_left _
  have hcode : NullMeasurableSet
      ((fun g : DistC => LQGMetric.GM.subTest g φ) ⁻¹' E) (P.map h) :=
    (hE.preimage hShift).nullMeasurableSet (P.map h)
  have hcanonical : IsNormalizedWholePlaneGFF
      (id : DistC → DistC) (P.map h) := normalizedGFF_id_map P h hh
  have hae :
      {g : DistC | ∃ P' : ℝ → ℂ, ∃ T : ℝ,
        EndSaving.FiniteEvents.UniqueSetGeodesic
          (D (LQGMetric.GM.subTest g φ)) K₁ K₂ P' T ∧
        ∀ i ∈ Z, ∃ t ∈ Icc 0 T, P' t ∈ O i} =ᵐ[P.map h]
        ((fun g : DistC => LQGMetric.GM.subTest g φ) ⁻¹' E) := by
    filter_upwards [Toolkit.WeylShift.ae_all_shift_curves hD (P.map h) id hcanonical]
      with g hg
    have hcont := (hg (-LQGMetric.testCont φ)).1
    change Continuous (euclidForget
      (D (LQGMetric.GM.subTest g φ))) at hcont
    exact propext (uniqueSetGeodesic_hits_iff_code Z O
      (D (LQGMetric.GM.subTest g φ)) K₁ K₂ hcont)
  exact hcode.congr hae.symm

end SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes
