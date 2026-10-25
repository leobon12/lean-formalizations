import SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness.CMCodeTransfer




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness

open LQGMetric (DistC TestC)

theorem badSetGeoCode_null_of_bump
    {ξ : Set.Ioi (0 : ℝ)} {Qpar : ℝ}
    {D : DistC → LSCMetric} (hD : IsWeakLQGMetric ξ Qpar D)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h μ)
    (φ : TestC) (hf : ∀ z : ℂ,
      0 ≤ LQGMetric.testCont φ z ∧ LQGMetric.testCont φ z ≤ 1)
    (K₁ K₂ U V : Set ℂ)
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hU : IsOpen U) (hV : IsOpen V)
    (hV₁ : Disjoint V K₁) (hV₂ : Disjoint V K₂)
    (hfU : ∀ z ∉ U, LQGMetric.testCont φ z = 0)
    (hfV : ∀ z ∈ V, LQGMetric.testCont φ z = 1) :
    μ {ω | Geodesics.SetGeodesics.BadSetGeoCode (D (h ω)) K₁ K₂ U V} = 0 := by
  obtain ⟨a, _, hshift0⟩ := exists_amplitude_null_code hD μ h hh
    (LQGMetric.testCont φ) hf K₁ K₂ U V hK₁ hK₂ hU hV
    hV₁ hV₂ hfU hfV
  apply badSetGeoCode_null_of_shift_null hD μ h hh K₁ K₂ U V
    hK₁ hK₂ hU hV (a • φ)
  simpa only [LQGMetric.MQ.testCont_smul] using hshift0

theorem badSetGeoCode_null_rational
    {ξ : Set.Ioi (0 : ℝ)} {Qpar : ℝ}
    {D : DistC → LSCMetric} (hD : IsWeakLQGMetric ξ Qpar D)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h μ)
    (K₁ K₂ : Set ℂ) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (a b ρ : ℚ) (hρ : (0 : ℝ) < ρ)
    (hV₁ : Disjoint (Metric.ball (⟨a, b⟩ : ℂ) (2 * (ρ : ℝ))) K₁)
    (hV₂ : Disjoint (Metric.ball (⟨a, b⟩ : ℂ) (2 * (ρ : ℝ))) K₂) :
    μ {ω | Geodesics.SetGeodesics.BadSetGeoCode (D (h ω)) K₁ K₂
      (Metric.ball (⟨a, b⟩ : ℂ) (3 * (ρ : ℝ)))
      (Metric.ball (⟨a, b⟩ : ℂ) (2 * (ρ : ℝ)))} = 0 := by
  let q : ℂ := ⟨a, b⟩
  let φ := LQGMetric.MQ.mqBump q ρ hρ
  have hf : ∀ z : ℂ,
      0 ≤ LQGMetric.testCont φ z ∧ LQGMetric.testCont φ z ≤ 1 := by
    intro z
    exact ⟨LQGMetric.MQ.mqBump_nonneg q ρ hρ z,
      (LQGMetric.MQ.mqBumpFun q ρ hρ).le_one⟩
  have hfU : ∀ z ∉ Metric.ball q (3 * (ρ : ℝ)),
      LQGMetric.testCont φ z = 0 := by
    intro z hz
    apply LQGMetric.MQ.mqBump_eq_zero hρ
    simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using hz
  have hfV : ∀ z ∈ Metric.ball q (2 * (ρ : ℝ)),
      LQGMetric.testCont φ z = 1 := by
    intro z hz
    apply LQGMetric.MQ.mqBump_eq_one hρ
    simpa only [Metric.mem_ball, dist_eq_norm] using hz
  exact badSetGeoCode_null_of_bump hD μ h hh φ hf
    K₁ K₂ (Metric.ball q (3 * (ρ : ℝ)))
    (Metric.ball q (2 * (ρ : ℝ))) hK₁ hK₂
    Metric.isOpen_ball Metric.isOpen_ball hV₁ hV₂ hfU hfV

theorem ae_not_bad_rational_bump
    {ξ : Set.Ioi (0 : ℝ)} {Qpar : ℝ}
    {D : DistC → LSCMetric} (hD : IsWeakLQGMetric ξ Qpar D)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h μ)
    (K₁ K₂ : Set ℂ) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (a b ρ : ℚ) (hρ : (0 : ℝ) < ρ)
    (hV₁ : Disjoint (Metric.ball (⟨a, b⟩ : ℂ) (2 * (ρ : ℝ))) K₁)
    (hV₂ : Disjoint (Metric.ball (⟨a, b⟩ : ℂ) (2 * (ρ : ℝ))) K₂) :
    ∀ᵐ ω ∂μ,
      ¬ Geodesics.SetGeodesics.BadSetGeodesic (D (h ω)) K₁ K₂
        (Metric.ball (⟨a, b⟩ : ℂ) (3 * (ρ : ℝ)))
        (Metric.ball (⟨a, b⟩ : ℂ) (2 * (ρ : ℝ))) := by
  have hcode0 := badSetGeoCode_null_rational hD μ h hh K₁ K₂
    hK₁ hK₂ a b ρ hρ hV₁ hV₂
  filter_upwards [Geodesics.SetGeodesics.ae_badSetGeodesic_iff_code_all_shifts hD μ h hh,
    measure_eq_zero_iff_ae_notMem.mp hcode0] with ω hiff hnot hbad
  exact hnot ((hiff.1 K₁ K₂ _ _).mp hbad)

end SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness
