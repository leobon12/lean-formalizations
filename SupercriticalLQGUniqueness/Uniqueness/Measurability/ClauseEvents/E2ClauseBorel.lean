import SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents.OpenClosedSetDist
import SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents.AttainedClause4Borel




 


set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents

private def outerAnnulus (z : ℂ) (r : Ioi (0 : ℝ)) : EuclideanAnnulus :=
  ⟨(z, (3 * r / 2, 2 * r)), by
    have hr : 0 < (r : ℝ) := r.2
    constructor <;> nlinarith⟩

private theorem eventMiddle_open (z : ℂ) (r : ℝ) :
    IsOpen (TwoScale.S36Events.eventMiddle z r) := by
  unfold TwoScale.S36Events.eventMiddle
  exact Metric.isOpen_ball.sdiff Metric.isClosed_closedBall

private theorem eventBoundary_closed (z : ℂ) (r : ℝ) :
    IsClosed (TwoScale.S36Events.eventBoundary z r) := by
  unfold TwoScale.S36Events.eventBoundary
  exact Metric.isClosed_sphere.union Metric.isClosed_sphere

 
theorem attainedClause2_measurable (ξ Qpar : ℝ) (z : ℂ)
    (r : Ioi (0 : ℝ)) (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (θ : Ioi (0 : ℝ))
    (Cminus Cplus : ℝ) :
    MeasurableSet {p : LSCMetric × ℝ |
      aroundDist p.1 (outerAnnulus z r) ≤
        min (ENNReal.ofReal ((1 - (a : ℝ))⁻¹ * (r : ℝ) ^ (ξ * Qpar) *
          Real.exp (ξ * p.2)))
          (ENNReal.ofReal (Cminus / (2 * Cplus) * (q : ℝ) ^ (-(θ : ℝ))) *
            OptimalConstants.Ratios.setDist p.1 (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r))} := by
  have hAround : Measurable (fun p : LSCMetric × ℝ =>
      aroundDist p.1 (outerAnnulus z r)) :=
    (Toolkit.CountableBase.aroundBoundedAnnulus_borel (outerAnnulus z r)).comp measurable_fst
  have hExp : Measurable (fun p : LSCMetric × ℝ =>
      ENNReal.ofReal ((1 - (a : ℝ))⁻¹ * (r : ℝ) ^ (ξ * Qpar) *
        Real.exp (ξ * p.2))) := by
    have hc : Continuous (fun c : ℝ =>
        (1 - (a : ℝ))⁻¹ * (r : ℝ) ^ (ξ * Qpar) *
          Real.exp (ξ * c)) := by fun_prop
    exact (ENNReal.continuous_ofReal.comp hc).measurable.comp measurable_snd
  have hDist : Measurable (fun p : LSCMetric × ℝ =>
      OptimalConstants.Ratios.setDist p.1 (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r)) :=
    (measurable_setDist_open_closed _ _
      (eventMiddle_open z r) (eventBoundary_closed z r)).comp measurable_fst
  have hMin : Measurable (fun p : LSCMetric × ℝ =>
      min (ENNReal.ofReal ((1 - (a : ℝ))⁻¹ * (r : ℝ) ^ (ξ * Qpar) *
        Real.exp (ξ * p.2)))
          (ENNReal.ofReal (Cminus / (2 * Cplus) * (q : ℝ) ^ (-(θ : ℝ))) *
            OptimalConstants.Ratios.setDist p.1 (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r))) :=
    hExp.min (measurable_const.mul hDist)
  exact measurableSet_le hAround hMin

end SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents
