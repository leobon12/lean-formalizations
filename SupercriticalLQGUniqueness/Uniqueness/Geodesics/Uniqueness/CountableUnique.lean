import SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness.RationalNull




 

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness

open LQGMetric (DistC)

theorem ae_unique_set_geodesic_if_exists
    {ξ : Set.Ioi (0 : ℝ)} {Qpar : ℝ}
    {D : DistC → LSCMetric} (hD : IsWeakLQGMetric ξ Qpar D)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h μ)
    (K₁ K₂ : Set ℂ) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hK : Disjoint K₁ K₂) :
    ∀ᵐ ω ∂μ, ∀ P : ℝ → ℂ, ∀ T : ℝ,
      EndSaving.FiniteEvents.SetGeodesic (D (h ω)) K₁ K₂ P T →
      EndSaving.FiniteEvents.UniqueSetGeodesic (D (h ω)) K₁ K₂ P T := by
  have hall : ∀ᵐ ω ∂μ, ∀ i : ℚ × ℚ × ℚ,
      (0 : ℝ) < i.2.2 →
      Disjoint (Metric.ball (⟨i.1, i.2.1⟩ : ℂ) (2 * (i.2.2 : ℝ))) K₁ →
      Disjoint (Metric.ball (⟨i.1, i.2.1⟩ : ℂ) (2 * (i.2.2 : ℝ))) K₂ →
      ¬ Geodesics.SetGeodesics.BadSetGeodesic (D (h ω)) K₁ K₂
        (Metric.ball (⟨i.1, i.2.1⟩ : ℂ) (3 * (i.2.2 : ℝ)))
        (Metric.ball (⟨i.1, i.2.1⟩ : ℂ) (2 * (i.2.2 : ℝ))) := by
    rw [ae_all_iff]
    intro i
    by_cases hρ : (0 : ℝ) < i.2.2
    · by_cases hV₁ : Disjoint
          (Metric.ball (⟨i.1, i.2.1⟩ : ℂ) (2 * (i.2.2 : ℝ))) K₁
      · by_cases hV₂ : Disjoint
            (Metric.ball (⟨i.1, i.2.1⟩ : ℂ) (2 * (i.2.2 : ℝ))) K₂
        · filter_upwards [ae_not_bad_rational_bump hD μ h hh K₁ K₂
            hK₁ hK₂ i.1 i.2.1 i.2.2 hρ hV₁ hV₂] with ω hω _ _ _
          exact hω
        · exact Filter.Eventually.of_forall (fun _ _ _ h₂ => (hV₂ h₂).elim)
      · exact Filter.Eventually.of_forall (fun _ _ h₁ => (hV₁ h₁).elim)
    · exact Filter.Eventually.of_forall (fun _ hpos => (hρ hpos).elim)
  filter_upwards [hall, EndSaving.Choices.ae_regularAt_self hD μ h hh] with ω hω hreg P T hP
  refine ⟨hP, ?_⟩
  intro Q S hQ
  have htime : S = T := by
    have heq : ENNReal.ofReal S = ENNReal.ofReal T :=
      hQ.2.2.2.trans hP.2.2.2.symm
    exact (ENNReal.ofReal_eq_ofReal_iff hQ.1.1.1 hP.1.1.1).mp heq
  have hpath : Set.EqOn Q P (Icc 0 T) := by
    by_contra hdiff
    have hdiff' : ¬ Set.EqOn P Q (Icc 0 T) := by
      intro hEq
      exact hdiff (by simpa only [htime] using hEq.symm)
    obtain ⟨a, b, ρ, hρ, hbad, hV₁, hV₂⟩ :=
      SetGeodesic.exists_rational_bad_bump (D (h ω)) K₁ K₂
        hK₁ hK₂ hK P Q T S hP hQ hreg.forget hdiff'
    exact (hω (a, b, ρ) hρ hV₁ hV₂) hbad
  exact ⟨htime, hpath⟩

end SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness
