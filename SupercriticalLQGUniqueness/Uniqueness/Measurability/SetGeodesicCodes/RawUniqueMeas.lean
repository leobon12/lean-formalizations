import SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes.UniqueCandidateMeas




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes
open LQGMetric (DistC TestC)

theorem normalizedGFF_id_map
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P) :
    IsNormalizedWholePlaneGFF (id : DistC → DistC) (P.map h) := by
  let r : Set.Ioi (0 : ℝ) := ⟨1, Set.mem_Ioi.mpr one_pos⟩
  have hAvg : MeasurableSet
      {g : DistC | IsCircleAverage g r 0 0} := by
    have hp : Measurable (fun g : DistC => (g, (0 : ℝ))) :=
      measurable_id.prodMk measurable_const
    exact (Measurability.AttainedEvents.circleAverageGraph_measurable r 0).preimage hp
  exact ⟨LQGMetric.GM.isWholePlaneGFF_id_map hh.1,
    (ae_map_iff hh.1.measurable.aemeasurable hAvg).2 hh.2⟩

theorem rawUniqueSetGeodesic_nullMeasurable
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    {ξ : Set.Ioi (0 : ℝ)} {Qpar : ℝ} {D : DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Qpar D)
    (K₁ K₂ : Set ℂ) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) :
    NullMeasurableSet
      {g : DistC | ∃ P' : ℝ → ℂ, ∃ T : ℝ,
        EndSaving.FiniteEvents.UniqueSetGeodesic (D g) K₁ K₂ P' T}
      (P.map h) := by
  let E : Set DistC :=
    {g | ∃! w : Measurability.GeodesicCodes.Path × (ℂ × ℂ),
      Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (D g, w)}
  have hE : LQGMetric.UMeasurableSet E :=
    uniqueSetGeoCandidateEvent_um D hD.1 K₁ K₂ hK₁ hK₂
  have hcode : NullMeasurableSet E (P.map h) :=
    hE.nullMeasurableSet (P.map h)
  have hcanonical : IsNormalizedWholePlaneGFF
      (id : DistC → DistC) (P.map h) := normalizedGFF_id_map P h hh
  have hae :
      {g : DistC | ∃ P' : ℝ → ℂ, ∃ T : ℝ,
        EndSaving.FiniteEvents.UniqueSetGeodesic (D g) K₁ K₂ P' T} =ᵐ[P.map h] E := by
    filter_upwards [ae_original_and_all_test_shift_uniqueSetGeodesic_iff_code
      hD (P.map h) id hcanonical] with g hg
    exact propext (hg.1 K₁ K₂)
  exact hcode.congr hae.symm

 


theorem rawUniqueSetGeodesic_shifted_nullMeasurable
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    {ξ : Set.Ioi (0 : ℝ)} {Qpar : ℝ} {D : DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Qpar D)
    (K₁ K₂ : Set ℂ) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (φ : TestC) :
    NullMeasurableSet
      {g : DistC | ∃ P' : ℝ → ℂ, ∃ T : ℝ,
        EndSaving.FiniteEvents.UniqueSetGeodesic
          (D (LQGMetric.GM.subTest g φ)) K₁ K₂ P' T}
      (P.map h) := by
  let E : Set DistC :=
    {g | ∃! w : Measurability.GeodesicCodes.Path × (ℂ × ℂ),
      Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (D g, w)}
  have hE : LQGMetric.UMeasurableSet E :=
    uniqueSetGeoCandidateEvent_um D hD.1 K₁ K₂ hK₁ hK₂
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
          (D (LQGMetric.GM.subTest g φ)) K₁ K₂ P' T} =ᵐ[P.map h]
        ((fun g : DistC => LQGMetric.GM.subTest g φ) ⁻¹' E) := by
    filter_upwards [ae_original_and_all_test_shift_uniqueSetGeodesic_iff_code
      hD (P.map h) id hcanonical] with g hg
    exact propext (hg.2 φ K₁ K₂)
  exact hcode.congr hae.symm

end SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes
