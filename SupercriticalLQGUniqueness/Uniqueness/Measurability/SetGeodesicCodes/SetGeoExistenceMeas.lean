import SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes.SetGeoCodeBridge




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes
open LQGMetric (DistC)

 

theorem setGeoCandidateEvent_um
    (D : DistC → LSCMetric) (hD : Measurable D)
    (K₁ K₂ : Set ℂ) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) :
    LQGMetric.UMeasurableSet
      {g : DistC | ∃ R : Measurability.GeodesicCodes.Path, ∃ u v : ℂ,
        Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (D g, (R, (u, v)))} := by
  have hProj := Measurability.GeodesicCodes.witnessProjection_um D hD
    (Measurability.ClauseEvents.setGeoCandidate_measurable K₁ K₂ hK₁ hK₂)
  convert hProj using 1
  ext g
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨R, u, v, hR⟩
    exact ⟨(R, (u, v)), hR⟩
  · rintro ⟨⟨R, u, v⟩, hR⟩
    exact ⟨R, u, v, hR⟩

 

theorem setGeodesicExistence_sample_nullMeasurable
    {ξ : Set.Ioi (0 : ℝ)} {Qpar : ℝ} {D : DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Qpar D)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h μ)
    (K₁ K₂ : Set ℂ) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) :
    NullMeasurableSet
      {ω : Ω | ∃ P : ℝ → ℂ, ∃ T : ℝ,
        EndSaving.FiniteEvents.SetGeodesic (D (h ω)) K₁ K₂ P T} μ := by
  let E : Set DistC :=
    {g | ∃ R : Measurability.GeodesicCodes.Path, ∃ u v : ℂ,
      Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (D g, (R, (u, v)))}
  have hE : LQGMetric.UMeasurableSet E :=
    setGeoCandidateEvent_um D hD.1 K₁ K₂ hK₁ hK₂
  have hcode : NullMeasurableSet (h ⁻¹' E) μ :=
    hE.nullMeasurableSet_preimage hh.1.measurable.aemeasurable
  have hae :
      {ω : Ω | ∃ P : ℝ → ℂ, ∃ T : ℝ,
        EndSaving.FiniteEvents.SetGeodesic (D (h ω)) K₁ K₂ P T} =ᵐ[μ] h ⁻¹' E := by
    filter_upwards [Toolkit.WeylShift.ae_common_weyl_sample hD μ h hh] with ω hω
    exact propext (exists_setGeodesic_iff_candidate
      (D (h ω)) K₁ K₂ hω.1)
  exact hcode.congr hae.symm

end SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes
