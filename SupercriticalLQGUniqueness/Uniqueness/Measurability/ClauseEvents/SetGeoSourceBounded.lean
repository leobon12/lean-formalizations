import SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents.SetGeoCandidate
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.FiniteEvents.FiniteEventsV2




set_option autoImplicit false
noncomputable section
open Set
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents

 

theorem setGeodesic_has_candidate_of_bounded_trace
    (D : LSCMetric) (K₁ K₂ : Set ℂ) (P : ℝ → ℂ) (T : ℝ)
    (hSet : EndSaving.FiniteEvents.SetGeodesic D K₁ K₂ P T)
    (hBounded : Bornology.IsBounded (P '' Icc (0 : ℝ) T)) :
    ∃ Q : Measurability.GeodesicCodes.Path,
      SetGeoCandidate K₁ K₂ (D, (Q, (P 0, P T))) := by
  have hB := hSet.1
  have hT : 0 ≤ T := hB.1.1
  have hLen : D.len P 0 T = ENNReal.ofReal T := by
    simpa only [LSCMetric.len, LQGMetric.MetricGeometry.curveLength, sub_zero] using
      (LQGMetric.MetricGeometry.curveLength_of_hasUnitSpeedOn hB.2.1
        ⟨le_refl _, hT⟩ ⟨hT, le_refl _⟩)
  have hCost : D (P 0, P T) = OptimalConstants.Ratios.setDist D K₁ K₂ := by
    calc
      D (P 0, P T) = D.len P 0 T := hB.2.2.1.symm
      _ = ENNReal.ofReal T := hLen
      _ = OptimalConstants.Ratios.setDist D K₁ K₂ := hSet.2.2.2
  have hGeo : OptimalConstants.Ratios.Geodesic D P 0 T (P 0) (P T) :=
    ⟨hB.1, rfl, rfl, hB.2.2.1, hB.2.2.2⟩
  have hCont : ContinuousOn P (Icc (0 : ℝ) T) :=
    Toolkit.PathInfimum.continuousOn_euclidean_of_bounded D P hB.1 hBounded
  have hCompact : IsCompact (P '' Icc (0 : ℝ) T) :=
    isCompact_Icc.image_of_continuousOn hCont
  obtain ⟨Q, hQCode, _⟩ :=
    Measurability.AttainedEvents.exists_geoCode_of_compact_geodesic D (P '' Icc 0 T)
      hCompact P 0 T (P 0) (P T) hGeo Subset.rfl
  refine ⟨Q, ?_⟩
  exact ⟨hQCode, hSet.2.1, hSet.2.2.1, hCost⟩

end SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents
