import SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness.SetGeoSeparate




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness

open LQGMetric (DistC)

theorem ae_volume_bad_rational_bump
    {ξ : Set.Ioi (0 : ℝ)} {Qpar : ℝ}
    {D : DistC → LSCMetric} (hD : IsWeakLQGMetric ξ Qpar D)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h μ)
    (K₁ K₂ : Set ℂ) (a b ρ : ℚ) (hρ : (0 : ℝ) < ρ)
    (hV₁ : Disjoint (Metric.ball (⟨a, b⟩ : ℂ) (2 * (ρ : ℝ))) K₁)
    (hV₂ : Disjoint (Metric.ball (⟨a, b⟩ : ℂ) (2 * (ρ : ℝ))) K₂) :
    ∀ᵐ ω ∂μ,
      volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧
        Geodesics.SetGeodesics.BadSetGeodesic
          (D (LQGMetric.addFun (h ω)
            (t • LQGMetric.testCont
              (LQGMetric.MQ.mqBump (⟨a, b⟩ : ℂ) ρ hρ))))
          K₁ K₂
          (Metric.ball (⟨a, b⟩ : ℂ) (3 * (ρ : ℝ)))
          (Metric.ball (⟨a, b⟩ : ℂ) (2 * (ρ : ℝ)))} = 0 := by
  let q : ℂ := ⟨a, b⟩
  let φ := LQGMetric.MQ.mqBump q ρ hρ
  let f : C(ℂ, ℝ) := LQGMetric.testCont φ
  have hf : ∀ z : ℂ, 0 ≤ f z ∧ f z ≤ 1 := by
    intro z
    exact ⟨LQGMetric.MQ.mqBump_nonneg q ρ hρ z,
      (LQGMetric.MQ.mqBumpFun q ρ hρ).le_one⟩
  have hfU : ∀ z ∉ Metric.ball q (3 * (ρ : ℝ)), f z = 0 := by
    intro z hz
    apply LQGMetric.MQ.mqBump_eq_zero hρ
    simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using hz
  have hfV : ∀ z ∈ Metric.ball q (2 * (ρ : ℝ)), f z = 1 := by
    intro z hz
    apply LQGMetric.MQ.mqBump_eq_one hρ
    simpa only [Metric.mem_ball, dist_eq_norm] using hz
  exact ae_volume_bad_amplitudes_eq_zero hD μ h hh f hf K₁ K₂
    (Metric.ball q (3 * (ρ : ℝ))) (Metric.ball q (2 * (ρ : ℝ)))
    Metric.isOpen_ball hV₁ hV₂ hfU hfV

end SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness
