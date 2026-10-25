import SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness.CMCodeTransferReverse




 

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness

open LQGMetric (DistC TestC)

theorem ae_not_bad_rational_bump_shift
    {ξ : Set.Ioi (0 : ℝ)} {Qpar : ℝ}
    {D : DistC → LSCMetric} (hD : IsWeakLQGMetric ξ Qpar D)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h μ)
    (ψ : TestC)
    (K₁ K₂ : Set ℂ) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (a b ρ : ℚ) (hρ : (0 : ℝ) < ρ)
    (hV₁ : Disjoint (Metric.ball (⟨a, b⟩ : ℂ) (2 * (ρ : ℝ))) K₁)
    (hV₂ : Disjoint (Metric.ball (⟨a, b⟩ : ℂ) (2 * (ρ : ℝ))) K₂) :
    ∀ᵐ ω ∂μ,
      ¬ Geodesics.SetGeodesics.BadSetGeodesic
        (D (LQGMetric.addFun (h ω) (LQGMetric.testCont ψ))) K₁ K₂
        (Metric.ball (⟨a, b⟩ : ℂ) (3 * (ρ : ℝ)))
        (Metric.ball (⟨a, b⟩ : ℂ) (2 * (ρ : ℝ))) := by
  have hcode0 := badSetGeoCode_null_rational hD μ h hh K₁ K₂
    hK₁ hK₂ a b ρ hρ hV₁ hV₂
  have hshift0 := badSetGeoCode_shift_null_of_null hD μ h hh K₁ K₂
    (Metric.ball (⟨a, b⟩ : ℂ) (3 * (ρ : ℝ)))
    (Metric.ball (⟨a, b⟩ : ℂ) (2 * (ρ : ℝ)))
    hK₁ hK₂ Metric.isOpen_ball Metric.isOpen_ball ψ hcode0
  filter_upwards [EndSaving.Choices.ae_regularAt_shift hD μ h hh ψ,
    measure_eq_zero_iff_ae_notMem.mp hshift0] with ω hreg hnot hbad
  have hiff := Geodesics.SetGeodesics.badSetGeodesic_iff_code
    (D (LQGMetric.addFun (h ω) (LQGMetric.testCont ψ))) K₁ K₂
    (Metric.ball (⟨a, b⟩ : ℂ) (3 * (ρ : ℝ)))
    (Metric.ball (⟨a, b⟩ : ℂ) (2 * (ρ : ℝ))) hreg.forget
  exact hnot (hiff.mp hbad)

theorem ae_unique_set_geodesic_if_exists_shift
    {ξ : Set.Ioi (0 : ℝ)} {Qpar : ℝ}
    {D : DistC → LSCMetric} (hD : IsWeakLQGMetric ξ Qpar D)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h μ)
    (ψ : TestC)
    (K₁ K₂ : Set ℂ) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hK : Disjoint K₁ K₂) :
    ∀ᵐ ω ∂μ, ∀ P : ℝ → ℂ, ∀ T : ℝ,
      EndSaving.FiniteEvents.SetGeodesic
        (D (LQGMetric.addFun (h ω) (LQGMetric.testCont ψ))) K₁ K₂ P T →
      EndSaving.FiniteEvents.UniqueSetGeodesic
        (D (LQGMetric.addFun (h ω) (LQGMetric.testCont ψ))) K₁ K₂ P T := by
  have hall : ∀ᵐ ω ∂μ, ∀ i : ℚ × ℚ × ℚ,
      (0 : ℝ) < i.2.2 →
      Disjoint (Metric.ball (⟨i.1, i.2.1⟩ : ℂ) (2 * (i.2.2 : ℝ))) K₁ →
      Disjoint (Metric.ball (⟨i.1, i.2.1⟩ : ℂ) (2 * (i.2.2 : ℝ))) K₂ →
      ¬ Geodesics.SetGeodesics.BadSetGeodesic
        (D (LQGMetric.addFun (h ω) (LQGMetric.testCont ψ))) K₁ K₂
        (Metric.ball (⟨i.1, i.2.1⟩ : ℂ) (3 * (i.2.2 : ℝ)))
        (Metric.ball (⟨i.1, i.2.1⟩ : ℂ) (2 * (i.2.2 : ℝ))) := by
    rw [ae_all_iff]
    intro i
    by_cases hρ : (0 : ℝ) < i.2.2
    · by_cases hV₁ : Disjoint
          (Metric.ball (⟨i.1, i.2.1⟩ : ℂ) (2 * (i.2.2 : ℝ))) K₁
      · by_cases hV₂ : Disjoint
            (Metric.ball (⟨i.1, i.2.1⟩ : ℂ) (2 * (i.2.2 : ℝ))) K₂
        · filter_upwards [ae_not_bad_rational_bump_shift hD μ h hh ψ K₁ K₂
            hK₁ hK₂ i.1 i.2.1 i.2.2 hρ hV₁ hV₂] with ω hω _ _ _
          exact hω
        · exact Filter.Eventually.of_forall (fun _ _ _ h₂ => (hV₂ h₂).elim)
      · exact Filter.Eventually.of_forall (fun _ _ h₁ => (hV₁ h₁).elim)
    · exact Filter.Eventually.of_forall (fun _ hpos => (hρ hpos).elim)
  filter_upwards [hall, EndSaving.Choices.ae_regularAt_shift hD μ h hh ψ] with ω hω hreg P T hP
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
      SetGeodesic.exists_rational_bad_bump
        (D (LQGMetric.addFun (h ω) (LQGMetric.testCont ψ)))
        K₁ K₂ hK₁ hK₂ hK P Q T S hP hQ hreg.forget hdiff'
    exact (hω (a, b, ρ) hρ hV₁ hV₂) hbad
  exact ⟨htime, hpath⟩

theorem ae_unique_set_geodesic_if_exists_shift_family
    {ξ : Set.Ioi (0 : ℝ)} {Qpar : ℝ}
    {D : DistC → LSCMetric} (hD : IsWeakLQGMetric ξ Qpar D)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h μ)
    {ι : Type} [Countable ι] (ψ : ι → TestC)
    (K₁ K₂ : Set ℂ) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hK : Disjoint K₁ K₂) :
    ∀ᵐ ω ∂μ, ∀ i : ι, ∀ P : ℝ → ℂ, ∀ T : ℝ,
      EndSaving.FiniteEvents.SetGeodesic
        (D (LQGMetric.addFun (h ω) (LQGMetric.testCont (ψ i)))) K₁ K₂ P T →
      EndSaving.FiniteEvents.UniqueSetGeodesic
        (D (LQGMetric.addFun (h ω) (LQGMetric.testCont (ψ i)))) K₁ K₂ P T := by
  rw [ae_all_iff]
  intro i
  exact ae_unique_set_geodesic_if_exists_shift hD μ h hh (ψ i)
    K₁ K₂ hK₁ hK₂ hK

theorem ae_unique_set_geodesic_of_finite_set_distance_shift_family
    {ξ : Set.Ioi (0 : ℝ)} {Qpar : ℝ}
    {D : DistC → LSCMetric} (hD : IsWeakLQGMetric ξ Qpar D)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h μ)
    {ι : Type} [Countable ι] (ψ : ι → TestC)
    (K₁ K₂ : Set ℂ) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hne₁ : K₁.Nonempty) (hne₂ : K₂.Nonempty)
    (hK : Disjoint K₁ K₂) :
    ∀ᵐ ω ∂μ, ∀ i : ι,
      OptimalConstants.Ratios.setDist
        (D (LQGMetric.addFun (h ω) (LQGMetric.testCont (ψ i)))) K₁ K₂ < ⊤ →
      ∃ P : ℝ → ℂ, ∃ T : ℝ,
        EndSaving.FiniteEvents.UniqueSetGeodesic
          (D (LQGMetric.addFun (h ω) (LQGMetric.testCont (ψ i)))) K₁ K₂ P T := by
  have hu := ae_unique_set_geodesic_if_exists_shift_family hD μ h hh ψ
    K₁ K₂ hK₁ hK₂ hK
  have hr : ∀ᵐ ω ∂μ, ∀ i : ι,
      EndSaving.Choices.RegularAt D (ξ : ℝ)
        (LQGMetric.addFun (h ω) (LQGMetric.testCont (ψ i))) := by
    rw [ae_all_iff]
    intro i
    exact EndSaving.Choices.ae_regularAt_shift hD μ h hh (ψ i)
  filter_upwards [hu, hr] with ω huω hrω i hfin
  obtain ⟨P, T, hgeo⟩ := Geodesics.SetGeodesics.exists_setGeodesic_of_finite
    (D (LQGMetric.addFun (h ω) (LQGMetric.testCont (ψ i)))) K₁ K₂
    hK₁ hK₂ hne₁ hne₂ (hrω i).barrier (hrω i).length hfin
  exact ⟨P, T, huω i P T hgeo⟩

end SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness
