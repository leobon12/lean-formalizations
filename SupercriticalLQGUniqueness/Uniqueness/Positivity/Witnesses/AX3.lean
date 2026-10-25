import SLUFieldSupport
import SLUMetricAPI
import LQGMetric.Metric.WeylScaling




 



set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses

open LQGMetric (DistC IsGFFPlusCont addFun)
open SupercriticalLQGUniqueness

 
theorem len_eq_mul_of_dist_scale (D E : LSCMetric) (c : ℝ≥0∞)
    (hscale : ∀ x y : ℂ, E (x, y) = c * D (x, y))
    (P : ℝ → ℂ) (a b : ℝ) : E.len P a b = c * D.len P a b := by
  have h := @LQGMetric.MetricGeometry.eVariationOn_eq_mul_of_edist
    ℂ ℂ
    (@EMetricSpace.toPseudoEMetricSpace ℂ (E.instEMetricSpace))
    (@EMetricSpace.toPseudoEMetricSpace ℂ (D.instEMetricSpace))
    P P c (fun s t => hscale (P s) (P t)) (Icc a b)
  exact h

theorem isCurve_of_dist_scale (D E : LSCMetric) (c : ℝ≥0∞) (hc : c ≠ ∞)
    (hscale : ∀ x y : ℂ, E (x, y) = c * D (x, y))
    (P : ℝ → ℂ) (a b : ℝ) (hP : D.IsCurve P a b) : E.IsCurve P a b := by
  refine ⟨hP.1, ?_⟩
  intro t ht
  have hDt := hP.2 t ht
  have hDlim := tendsto_iff_edist_tendsto_0.mp hDt
  change Filter.Tendsto (fun s => D (P s, P t)) (𝓝[Icc a b] t) (𝓝 0) at hDlim
  apply tendsto_iff_edist_tendsto_0.mpr
  change Filter.Tendsto (fun s => E (P s, P t)) (𝓝[Icc a b] t) (𝓝 0)
  simpa only [hscale, mul_zero] using
    ENNReal.Tendsto.mul (tendsto_const_nhds (x := c)) (Or.inr (by simp))
      hDlim (Or.inr hc)

 
theorem isCurve_iff_of_dist_scale (D E : LSCMetric) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hcTop : c ≠ ∞)
    (hscale : ∀ x y : ℂ, E (x, y) = c * D (x, y))
    (P : ℝ → ℂ) (a b : ℝ) : E.IsCurve P a b ↔ D.IsCurve P a b := by
  have hInv : ∀ x y : ℂ, D (x, y) = c⁻¹ * E (x, y) := by
    intro x y
    rw [hscale, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hcTop, one_mul]
  constructor
  · exact isCurve_of_dist_scale E D c⁻¹ (ENNReal.inv_ne_top.mpr hc0) hInv P a b
  · exact isCurve_of_dist_scale D E c hcTop hscale P a b

 
theorem internal_eq_mul_of_dist_scale (D E : LSCMetric) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hcTop : c ≠ ∞)
    (hscale : ∀ x y : ℂ, E (x, y) = c * D (x, y))
    (U : Set ℂ) (p : U × U) : E.internal U p = c * D.internal U p := by
  unfold LSCMetric.internal
  simp only [isCurve_iff_of_dist_scale D E c hc0 hcTop hscale,
    len_eq_mul_of_dist_scale D E c hscale]
  simp only [ENNReal.mul_iInf_of_ne hc0 hcTop]

 
theorem acrossDist_eq_mul_of_dist_scale (D E : LSCMetric) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hcTop : c ≠ ∞)
    (hscale : ∀ x y : ℂ, E (x, y) = c * D (x, y))
    (A : EuclideanAnnulus) : acrossDist E A = c * acrossDist D A := by
  unfold acrossDist
  simp only [hscale, ENNReal.mul_iInf_of_ne hc0 hcTop]

 
theorem aroundDist_eq_mul_of_dist_scale (D E : LSCMetric) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hcTop : c ≠ ∞)
    (hscale : ∀ x y : ℂ, E (x, y) = c * D (x, y))
    (A : EuclideanAnnulus) : aroundDist E A = c * aroundDist D A := by
  unfold aroundDist
  simp only [isCurve_iff_of_dist_scale D E c hc0 hcTop hscale,
    len_eq_mul_of_dist_scale D E c hscale]
  simp only [ENNReal.mul_iInf_of_ne hc0 hcTop]

theorem weylScale_const (ξ t : ℝ) (D : LSCMetric) (hD : D.IsLengthSpace)
    (p : ℂ × ℂ) :
    weylScale ξ (ContinuousMap.const ℂ t) D p =
      ENNReal.ofReal (Real.exp (ξ * t)) * D p :=
  SupercriticalLQGUniqueness.weylScale_const ξ t D hD p

 
theorem ae_addConst_eq_mul {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsGFFPlusCont h P)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (c : Ω → ℝ) :
    ∀ᵐ ω ∂P, ∀ q : ℂ × ℂ,
      D (LQGMetric.addConst (h ω) (c ω)) q =
        ENNReal.ofReal (Real.exp ((ξ : ℝ) * c ω)) * D (h ω) q := by
  filter_upwards [hD.weyl P h hh, hD.length P h hh] with ω hw hl
  intro q
  have hqw := congrFun (hw (ContinuousMap.const ℂ (c ω))) q
  change weylScale (ξ : ℝ) (ContinuousMap.const ℂ (c ω)) (D (h ω)) q =
    D (LQGMetric.addConst (h ω) (c ω)) q at hqw
  exact hqw.symm.trans (weylScale_const (ξ : ℝ) (c ω) (D (h ω)) hl q)

 
theorem ae_internal_addConst_eq_mul {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsGFFPlusCont h P)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (c : Ω → ℝ) :
    ∀ᵐ ω ∂P, ∀ (U : Set ℂ) (p : U × U),
      (D (LQGMetric.addConst (h ω) (c ω))).internal U p =
        ENNReal.ofReal (Real.exp ((ξ : ℝ) * c ω)) * (D (h ω)).internal U p := by
  filter_upwards [ae_addConst_eq_mul P h hh ξ Q D hD c] with ω hw
  intro U p
  let k : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((ξ : ℝ) * c ω))
  have hk0 : k ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hkTop : k ≠ ∞ := ENNReal.ofReal_ne_top
  exact internal_eq_mul_of_dist_scale (D (h ω))
    (D (LQGMetric.addConst (h ω) (c ω))) k hk0 hkTop
    (fun x y => hw (x, y)) U p

 
theorem ae_annulus_addConst_eq_mul {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsGFFPlusCont h P)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (c : Ω → ℝ) :
    ∀ᵐ ω ∂P, ∀ A : EuclideanAnnulus,
      acrossDist (D (LQGMetric.addConst (h ω) (c ω))) A =
        ENNReal.ofReal (Real.exp ((ξ : ℝ) * c ω)) * acrossDist (D (h ω)) A ∧
      aroundDist (D (LQGMetric.addConst (h ω) (c ω))) A =
        ENNReal.ofReal (Real.exp ((ξ : ℝ) * c ω)) * aroundDist (D (h ω)) A := by
  filter_upwards [ae_addConst_eq_mul P h hh ξ Q D hD c] with ω hw
  intro A
  let k : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((ξ : ℝ) * c ω))
  have hk0 : k ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hkTop : k ≠ ∞ := ENNReal.ofReal_ne_top
  exact ⟨acrossDist_eq_mul_of_dist_scale (D (h ω))
      (D (LQGMetric.addConst (h ω) (c ω))) k hk0 hkTop
      (fun x y => hw (x, y)) A,
    aroundDist_eq_mul_of_dist_scale (D (h ω))
      (D (LQGMetric.addConst (h ω) (c ω))) k hk0 hkTop
      (fun x y => hw (x, y)) A⟩


end SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses
