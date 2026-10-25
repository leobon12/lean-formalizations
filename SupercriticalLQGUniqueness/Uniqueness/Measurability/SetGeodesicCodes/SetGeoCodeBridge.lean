import SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes.SetGeoRegular




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes

theorem setGeoCandidate_has_source
    (D : LSCMetric) (K₁ K₂ : Set ℂ) (R : Measurability.GeodesicCodes.Path) (u v : ℂ)
    (h : Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (D, (R, (u, v)))) :
    ∃ P : ℝ → ℂ, ∃ T : ℝ,
      EndSaving.FiniteEvents.SetGeodesic D K₁ K₂ P T := by
  rcases h with ⟨hcode, hu, hv, hdist⟩
  let γ : ℝ → ℂ := Measurability.GeodesicCodes.pathReal R
  let P : ℝ → D.Space := LQGMetric.MetricGeometry.lengthParam (D.pt ∘ γ) 0 1
  let T : ℝ := (D.len γ 0 1).toReal
  have hgeo := Measurability.AttainedEvents.geoCode_isGeodesic D R u v hcode
  have hfin : D.len γ 0 1 ≠ ∞ := by
    rw [hgeo.2.2.2.1]
    exact hgeo.2.2.2.2.ne
  have hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T) := by
    change HasUnitSpeedOn
      (LQGMetric.MetricGeometry.lengthParam (D.pt ∘ γ) 0 1)
      (Icc 0 (LQGMetric.MetricGeometry.curveLength (D.pt ∘ γ) 0 1).toReal)
    exact LQGMetric.MetricGeometry.hasUnitSpeedOn_lengthParam
      zero_le_one hgeo.1.2 hfin
  have hcurve : D.IsCurve P 0 T := by
    exact ⟨ENNReal.toReal_nonneg,
      LQGMetric.MetricGeometry.continuousOn_of_hasUnitSpeedOn hunit⟩
  have hP0 : P 0 = u := by
    have h0 := LQGMetric.MetricGeometry.lengthParam_variationOnFromTo
      hfin (t := 0) (⟨le_rfl, zero_le_one⟩ : (0 : ℝ) ∈ Icc 0 1)
    rw [variationOnFromTo.self] at h0
    exact h0.trans hgeo.2.1
  have hPT : P T = v := by
    have h1 := LQGMetric.MetricGeometry.lengthParam_variationOnFromTo
      hfin (t := 1) (⟨zero_le_one, le_rfl⟩ : (1 : ℝ) ∈ Icc 0 1)
    rw [variationOnFromTo.eq_of_le _ _ zero_le_one, Set.inter_self] at h1
    exact h1.trans hgeo.2.2.1
  have hlen : D.len P 0 T = D (P 0, P T) := by
    calc
      D.len P 0 T = D.len γ 0 1 :=
        LQGMetric.MetricGeometry.curveLength_lengthParam
          zero_le_one hgeo.1.2 hfin
      _ = D (u, v) := hgeo.2.2.2.1
      _ = D (P 0, P T) := by rw [hP0, hPT]
  refine ⟨P, T, ⟨⟨hcurve, hunit, hlen, ?_⟩, ?_, ?_, ?_⟩⟩
  · rw [hP0, hPT]
    exact hgeo.2.2.2.2
  · rw [hP0]
    exact hu
  · rw [hPT]
    exact hv
  · change ENNReal.ofReal (D.len γ 0 1).toReal = OptimalConstants.Ratios.setDist D K₁ K₂
    rw [ENNReal.ofReal_toReal hfin, hgeo.2.2.2.1]
    exact hdist

 

theorem exists_setGeodesic_iff_candidate
    (D : LSCMetric) (K₁ K₂ : Set ℂ)
    (hforget : Continuous (euclidForget D)) :
    (∃ P : ℝ → ℂ, ∃ T : ℝ, EndSaving.FiniteEvents.SetGeodesic D K₁ K₂ P T) ↔
      ∃ R : Measurability.GeodesicCodes.Path, ∃ u v : ℂ,
        Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (D, (R, (u, v))) := by
  constructor
  · rintro ⟨P, T, hP⟩
    obtain ⟨R, hR⟩ :=
      setGeodesic_has_candidate_of_continuous_forget
        D K₁ K₂ P T hforget hP
    exact ⟨R, P 0, P T, hR⟩
  · rintro ⟨R, u, v, hR⟩
    exact setGeoCandidate_has_source D K₁ K₂ R u v hR

 

theorem ae_all_shift_exists_setGeodesic_iff_candidate
    {ξ : Set.Ioi (0 : ℝ)} {Qpar : ℝ}
    {D : LQGMetric.DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Qpar D)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (h : Ω → LQGMetric.DistC)
    (hh : IsNormalizedWholePlaneGFF h μ) :
    ∀ᵐ ω ∂μ, ∀ g : C(ℂ, ℝ), ∀ K₁ K₂ : Set ℂ,
      (∃ P : ℝ → ℂ, ∃ T : ℝ,
        EndSaving.FiniteEvents.SetGeodesic (D (LQGMetric.addFun (h ω) g)) K₁ K₂ P T) ↔
      ∃ R : Measurability.GeodesicCodes.Path, ∃ u v : ℂ,
        Measurability.ClauseEvents.SetGeoCandidate K₁ K₂
          (D (LQGMetric.addFun (h ω) g), (R, (u, v))) := by
  filter_upwards [Toolkit.WeylShift.ae_all_shift_curves hD μ h hh] with ω hω
  intro g K₁ K₂
  exact exists_setGeodesic_iff_candidate _ K₁ K₂ (hω g).1

end SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes
