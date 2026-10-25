import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionMoments.CircleMgf
import Mathlib.Probability.Distributions.Gaussian.Real




 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate

theorem lintegral_exp_circleAvg_increment_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistC} (hh : LQGMetric.IsWholePlaneGFF h P)
    {a s R : ℝ} (ha : 0 < a) (has : a ≤ s) (hR : 0 ≤ R)
    (w y : ℂ) (hwy : ‖w - y‖ ≤ R * s) (t : ℝ) :
    (∫⁻ ω, ENNReal.ofReal
      (Real.exp (t * LQGMetric.CircleAvg.cInc h a w s y ω)) ∂P) ≤
      ENNReal.ofReal
        (Real.exp (t ^ 2 * (Real.log (s / a) + 2 * Real.log (R + 1)) / 2)) := by
  let V := LQGMetric.CircleAvg.incCov w a y s w a y s
  have hmap := (LQGMetric.CircleAvg.map_cInc hh ha (ha.trans_le has) w y).1
  have hmeas := LQGMetric.CircleAvg.measurable_cInc hh a w s y
  have hlaw : HasLaw (LQGMetric.CircleAvg.cInc h a w s y)
      (gaussianReal 0 V.toNNReal) P := ⟨hmeas.aemeasurable, hmap⟩
  have hint : Integrable
      (fun ω => Real.exp (t * LQGMetric.CircleAvg.cInc h a w s y ω)) P := by
    exact hlaw.integrable_comp (integrable_exp_mul_gaussianReal t)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)]
  exact ENNReal.ofReal_le_ofReal
    (Objects.BoundaryUnionMoments.mgf_circleAvg_increment_le hh ha has hR w y hwy t)


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate
