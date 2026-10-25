import SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness.CountableUnique




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness

open LQGMetric (DistC)

theorem ae_unique_set_geodesic_of_finite_set_distance
    {ξ : Set.Ioi (0 : ℝ)} {Qpar : ℝ}
    {D : DistC → LSCMetric} (hD : IsWeakLQGMetric ξ Qpar D)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h μ)
    (K₁ K₂ : Set ℂ) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hne₁ : K₁.Nonempty) (hne₂ : K₂.Nonempty)
    (hK : Disjoint K₁ K₂) :
    ∀ᵐ ω ∂μ,
      OptimalConstants.Ratios.setDist (D (h ω)) K₁ K₂ < ⊤ →
      ∃ P : ℝ → ℂ, ∃ T : ℝ,
        EndSaving.FiniteEvents.UniqueSetGeodesic (D (h ω)) K₁ K₂ P T := by
  filter_upwards [ae_unique_set_geodesic_if_exists hD μ h hh K₁ K₂
    hK₁ hK₂ hK, EndSaving.Choices.ae_regularAt_self hD μ h hh] with ω huniq hreg hfin
  obtain ⟨P, T, hgeo⟩ := Geodesics.SetGeodesics.exists_setGeodesic_of_finite
    (D (h ω)) K₁ K₂ hK₁ hK₂ hne₁ hne₂ hreg.barrier hreg.length hfin
  exact ⟨P, T, huniq P T hgeo⟩

end SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness
