import SupercriticalLQGUniqueness.B2.Median.UpperBound
import SupercriticalLQGUniqueness.B2.Median.SurgeryParts
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.WeylBump
import HigherDimLQGMetric.Metric.Reparam

 















set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Median

theorem barrier_crossing_eventually_lt_of_sep
    (ξ : Set.Ioi (0 : ℝ)) (ε a : ℕ → Set.Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (φ : ℕ → C(ℂ, ℝ)) (N : Set ℂ) (ρ : Set.Ioi (0 : ℝ)) (R : ℝ) (hR : 0 < R)
    (hKball : {z : ℂ | Metric.infDist z N ≤ (ρ : ℝ)} ⊆ closedBall 0 R)
    (hstrip : ∀ z : ℂ, Metric.infDist z N ≤ (ρ : ℝ) → 0 ≤ z.im ∧ z.im ≤ 1)
    (μ : ℝ≥0∞)
    (hsep : ∀ᶠ n in atTop, ∀ p : ℂ × ℂ,
      p.1 ∈ {z : ℂ | Metric.infDist z N ≤ (ρ : ℝ)} →
      p.2 ∈ {z : ℂ | Metric.infDist z N ≤ (ρ : ℝ)} →
      (ρ : ℝ) / 2 ≤ dist p.1 p.2 → μ ≤ lfppMetric (ξ : ℝ) (a n) (φ n) p)
    (M : ℝ) (hM : 0 < M)
    (O₁ O₂ : Set ℂ) (hO₁N : O₁ ⊆ N)
    (hO₁left : ∀ z ∈ O₁, z.re ≤ 0) (hO₂right : ∀ w ∈ O₂, 1 ≤ w.re)
    (W L : ℝ≥0∞)
    (hlim : Tendsto (fun n => ENNReal.ofReal ((a n : ℝ)⁻¹) *
          B2.Iface.setDistance
            (lfppDistance (ξ : ℝ)
              (φ n + LQGMetric.LFPP.mollCont (ε n : ℝ)
                (ε n).property.ne' (penaltyField N ρ M) M
                (penaltyField_abs_le N ρ hM.le))) O₁ O₂) atTop (𝓝 W))
    (hWL : W < L) (hLT : L ≤ ENNReal.ofReal (Real.exp ((ξ : ℝ) * (M / 4))) * μ) :
    ∀ᶠ n in atTop,
      ENNReal.ofReal ((a n : ℝ)⁻¹) * lfppCrossingLength (ξ : ℝ) (φ n) < L := by
  have hheat := eventually_penaltyField_heatMollify_ge ε hε N ρ M hM R hR
  let F : ℕ → C(ℂ, ℝ) := fun n => φ n +
    LQGMetric.LFPP.mollCont (ε n : ℝ) (ε n).property.ne'
      (penaltyField N ρ M) M (penaltyField_abs_le N ρ hM.le)
  have hbar : ∀ᶠ n in atTop, ∀ (P : ℝ → ℂ) (z w : ℂ),
      LQGMetric.IsPiecewiseC1Path P z w → z ∈ O₁ → w ∈ O₂ →
      ENNReal.ofReal ((a n : ℝ)⁻¹) *
        LQGMetric.lfppLen (ξ : ℝ) (F n) P <
          ENNReal.ofReal (Real.exp ((ξ : ℝ) * (M / 4))) * μ →
      ENNReal.ofReal ((a n : ℝ)⁻¹) *
        lfppCrossingLength (ξ : ℝ) (φ n) ≤
      ENNReal.ofReal ((a n : ℝ)⁻¹) *
        LQGMetric.lfppLen (ξ : ℝ) (F n) P := by
    filter_upwards [hsep, hheat] with n hn hhn P z w hP hz hw hcost
    let ψ : C(ℂ, ℝ) := LQGMetric.LFPP.mollCont (ε n : ℝ) (ε n).property.ne'
      (penaltyField N ρ M) M (penaltyField_abs_le N ρ hM.le)
    have hψ : ∀ u ∈ Icc (0 : ℝ) 1,
        1 / 2 ≤ distanceRatio N ρ (P u) →
        distanceRatio N ρ (P u) ≤ 1 → M / 4 ≤ ψ (P u) := by
      intro u _ hu huone
      have hthick : Metric.infDist (P u) N ≤ (ρ : ℝ) := by
        simpa only [one_mul] using (div_le_iff₀ ρ.property).mp huone
      exact hhn (P u) (hKball hthick) hu
    have hψnonneg : ∀ u : ℂ, 0 ≤ ψ u := by
      intro u
      exact heatMollify_nonneg_of_nonneg (penaltyField N ρ M) M
        (penaltyField_abs_le N ρ hM.le)
        (penaltyField_nonneg N ρ hM.le) (ε n) u
    have hmetric : ∀ u v : ℂ,
        Metric.infDist u N ≤ (ρ : ℝ) →
        Metric.infDist v N ≤ (ρ : ℝ) →
        (ρ : ℝ) / 2 ≤ dist u v →
        μ ≤ lfppMetric (ξ : ℝ) (a n) (φ n) (u, v) := by
      intro u v hu hv huv
      exact hn (u, v) hu hv huv
    have hpathstrip : ∀ u ∈ Icc (0 : ℝ) 1,
        distanceRatio N ρ (P u) < 1 →
          0 ≤ (P u).im ∧ (P u).im ≤ 1 := by
      intro u _ hu
      apply hstrip
      have hu' : Metric.infDist (P u) N < (ρ : ℝ) := by
        simpa only [one_mul] using (div_lt_iff₀ ρ.property).mp hu
      exact hu'.le
    exact crossing_le_shifted_path_of_barrier ξ.property.le (a n)
      (φ n) ψ N ρ μ hP (hO₁N hz) (hO₁left z hz) (hO₂right w hw) hmetric hψ hψnonneg
      hpathstrip hcost
  exact eventually_crossing_lt_of_barrier (ξ : ℝ) a φ F O₁ O₂
    (ENNReal.ofReal (Real.exp ((ξ : ℝ) * (M / 4))) * μ) W L hbar hlim hWL hLT

 
theorem weylScale_le_len_of_zero_on_trace (ξ : ℝ) (f : C(ℂ, ℝ)) (d : LSCMetric)
    {π : ℝ → ℂ} {a b : ℝ} (hπ : d.IsCurve π a b) (hfin : d.len π a b ≠ ∞)
    (hf : ∀ t ∈ Icc a b, f (π t) = 0) :
    weylScale ξ f d (π a, π b) ≤ d.len π a b := by
  have hL : LQGMetric.MetricGeometry.curveLength (d.pt ∘ π) a b ≠ ⊤ := hfin
  obtain ⟨hu, hc, h0, hT, hmaps⟩ := HigherDimLQGMetric.lengthParam_props hπ.1 hπ.2 hL
    (S := {x : d.Space | f x = 0}) (fun t ht => hf t ht)
  have hQf : ∀ t ∈ Icc 0 (LQGMetric.MetricGeometry.curveLength (d.pt ∘ π) a b).toReal,
      f ((fun t => (@LQGMetric.MetricGeometry.lengthParam d.Space _ (d.pt ∘ π) a b t : ℂ)) t) = 0 := by
    intro t ht
    have h := hmaps ht
    simp only [Set.mem_setOf_eq] at h
    exact h
  have hc' : ContinuousOn (d.pt ∘ (fun t => (@LQGMetric.MetricGeometry.lengthParam d.Space _ (d.pt ∘ π) a b t : ℂ)))
      (Icc 0 (LQGMetric.MetricGeometry.curveLength (d.pt ∘ π) a b).toReal) := hc
  have hu' : HasUnitSpeedOn (d.pt ∘ (fun t => (@LQGMetric.MetricGeometry.lengthParam d.Space _ (d.pt ∘ π) a b t : ℂ)))
      (Icc 0 (LQGMetric.MetricGeometry.curveLength (d.pt ∘ π) a b).toReal) := hu
  have hle := Uniqueness.TwoScale.S36.weylScale_le_of_const_on ξ f d (c := 0) hc' hu' hQf
    le_rfl ENNReal.toReal_nonneg le_rfl
  have hQ0 : (@LQGMetric.MetricGeometry.lengthParam d.Space _ (d.pt ∘ π) a b 0 : ℂ) = π a := h0
  have hQT : (@LQGMetric.MetricGeometry.lengthParam d.Space _ (d.pt ∘ π) a b
      (LQGMetric.MetricGeometry.curveLength (d.pt ∘ π) a b).toReal : ℂ) = π b := hT
  rw [hQ0, hQT] at hle
  calc weylScale ξ f d (π a, π b) ≤ _ := hle
    _ = d.len π a b := by
      rw [mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul, sub_zero]
      exact ENNReal.ofReal_toReal hL

end SupercriticalLQGUniqueness.B2.Median
