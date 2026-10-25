import SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents.FbarStatic




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents
open LQGMetric (DistC)

theorem fbarV2_iff_static_and_hits {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ) (cPlus : ℝ≥0∞)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z : Finset (ℤ × ℤ)) (g : DistC) :
    EndSaving.FiniteEvents.FbarV2 μ h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z g ↔
    FbarStaticV2 μ h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z g ∧
      ∃ P : ℝ → ℂ, ∃ T : ℝ,
        EndSaving.FiniteEvents.UniqueSetGeodesic (D g) K₁ K₂ P T ∧
        ∀ i ∈ Z, ∃ t ∈ Icc 0 T,
          P t ∈ Metric.ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r := by
  constructor
  · rintro ⟨hne, hconfig, hbr, havg, hbad, hlocal, P, T, hU, hHits⟩
    have hbrEq := Measurability.ClauseEvents.circleValue_eq_of_IsCircleAverage b 0 g hbr havg
    have hbad' : OptimalConstants.Ratios.setDist (D' g) K₁ K₂ ≥
        cPlus * OptimalConstants.Ratios.setDist (D g) K₁ K₂ -
          ENNReal.ofReal ((q : ℝ) * (b : ℝ) ^ ((ξ : ℝ) * Q) *
            Real.exp ((ξ : ℝ) * Measurability.ClauseEvents.circleValue b 0 g)) := by
      rw [hbrEq]
      exact hbad
    have hlocal' : ∀ i ∈ Z,
        g ∈ (obj i).E ∧
        IsCircleAverage g r (LQGMetric.GM.gridPt ((r : ℝ) / 100) i)
          (Measurability.ClauseEvents.circleValue r (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) g) ∧
        EndSaving.FiniteEvents.LocalSizeBin ξ Q r b q
          (Measurability.ClauseEvents.circleValue r (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) g)
          (Measurability.ClauseEvents.circleValue b 0 g) := by
      intro i hi
      obtain ⟨hE, hrz, havgz, hsize⟩ := hlocal i hi
      have hrzEq := Measurability.ClauseEvents.circleValue_eq_of_IsCircleAverage r
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) g hrz havgz
      refine ⟨hE, ?_, ?_⟩
      · rw [hrzEq]
        exact havgz
      · rw [hrzEq, hbrEq]
        exact hsize
    exact ⟨⟨hne, hconfig, by rw [hbrEq]; exact havg,
      hbad', hlocal'⟩, P, T, hU, hHits⟩
  · rintro ⟨⟨hne, hconfig, havg, hbad, hlocal⟩, P, T, hU, hHits⟩
    refine ⟨hne, hconfig, Measurability.ClauseEvents.circleValue b 0 g, havg,
      hbad, ?_, P, T, hU, hHits⟩
    intro i hi
    obtain ⟨hE, havgz, hsize⟩ := hlocal i hi
    exact ⟨hE, Measurability.ClauseEvents.circleValue r
      (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) g, havgz, hsize⟩

theorem fbarV2_nullMeasurable {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (D D' : DistC → LSCMetric)
    {ξ : Set.Ioi (0 : ℝ)} {Qpar : ℝ}
    (hD : IsWeakLQGMetric ξ Qpar D)
    (hD' : IsWeakLQGMetric ξ Qpar D')
    (cMid : ℝ) (cPlus : ℝ≥0∞)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 P h D D' ξ Qpar cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z : Finset (ℤ × ℤ)) :
    NullMeasurableSet
      {g : DistC | EndSaving.FiniteEvents.FbarV2 P h D D' ξ Qpar cMid cPlus par pbar
        r b q K₁ K₂ obj Z g} (P.map h) := by
  have hStatic := fbarStaticV2_measurable P h D D' hD.1 hD'.1
    ξ Qpar cMid cPlus par pbar r b q K₁ K₂ hK₁ hK₂ obj Z
  have hHits := Measurability.SetGeodesicCodes.rawUniqueSetGeodesicHits_nullMeasurable
    P h hh hD K₁ K₂ hK₁ hK₂ Z
    (fun i => Metric.ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (fun _ _ => Metric.isOpen_ball)
  have hEq :
      {g : DistC | EndSaving.FiniteEvents.FbarV2 P h D D' ξ Qpar cMid cPlus par pbar
        r b q K₁ K₂ obj Z g} =
      {g : DistC | FbarStaticV2 P h D D' ξ Qpar cMid cPlus par pbar
        r b q K₁ K₂ obj Z g} ∩
      {g : DistC | ∃ P' : ℝ → ℂ, ∃ T : ℝ,
        EndSaving.FiniteEvents.UniqueSetGeodesic (D g) K₁ K₂ P' T ∧
        ∀ i ∈ Z, ∃ t ∈ Icc 0 T,
          P' t ∈ Metric.ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r} := by
    ext g
    exact fbarV2_iff_static_and_hits P h D D' ξ Qpar cMid cPlus
      par pbar r b q K₁ K₂ obj Z g
  rw [hEq]
  exact hStatic.nullMeasurableSet.inter hHits

end SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents
