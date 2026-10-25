import SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents.E5EndpointLoop
import SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents.E1PointBorel




 


set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents

 
def e5Annulus (r : Ioi (0 : ℝ))
    (q : Ioo (0 : ℝ) (1 / 100)) (x : ℂ) : EuclideanAnnulus :=
  ⟨(x, ((q : ℝ) * r, Real.sqrt (q : ℝ) * r)), by
    have hq1 : (q : ℝ) < 1 := by linarith [q.2.2]
    exact TwoScale.Consolidated.loop_annulus_valid r.2 q.2.1 hq1⟩

private theorem loopF_eq_e5Annulus (D : LSCMetric) (x : ℂ)
    (r : Ioi (0 : ℝ)) (q : Ioo (0 : ℝ) (1 / 100)) :
    TwoScale.Consolidated.loopF D x r q = aroundDist D (e5Annulus r q x) := by
  have hv := (e5Annulus r q x).property
  change TwoScale.Consolidated.aroundAt D x ((q : ℝ) * r) (Real.sqrt (q : ℝ) * r) =
    aroundDist D ⟨(x, ((q : ℝ) * r, Real.sqrt (q : ℝ) * r)), hv⟩
  exact TwoScale.Consolidated.aroundAt_eq D x _ _ hv

 
theorem e5LoopCost_measurable (r : Ioi (0 : ℝ))
    (q : Ioo (0 : ℝ) (1 / 100)) :
    Measurable (fun p : LSCMetric × ℂ => TwoScale.Consolidated.loopF p.1 p.2 r q) := by
  let f : LSCMetric × ℂ → LSCMetric × (ℂ × ℝ × ℝ) :=
    fun p => (p.1, (p.2, (q : ℝ) * r, Real.sqrt (q : ℝ) * r))
  have hf : Measurable f :=
    measurable_fst.prodMk (measurable_snd.prodMk
      (measurable_const.prodMk measurable_const))
  have hcomp : Measurable (TwoScale.Consolidated.aroundRat ∘ f) :=
    TwoScale.Consolidated.measurable_aroundRat.comp hf
  have heq : (fun p : LSCMetric × ℂ => TwoScale.Consolidated.loopF p.1 p.2 r q) =
      TwoScale.Consolidated.aroundRat ∘ f := by
    funext p
    rw [loopF_eq_e5Annulus, TwoScale.Consolidated.aroundDist_eq_aroundRat]
    rfl
  exact heq.symm ▸ hcomp

 
theorem e5Annulus_exists_iff (D : LSCMetric) (x z : ℂ)
    (r : Ioi (0 : ℝ)) (q : Ioo (0 : ℝ) (1 / 100))
    (Cminus Cplus : ℝ) :
    (∃ A : EuclideanAnnulus,
      A.center = x ∧ A.innerRadius = (q : ℝ) * r ∧
      A.outerRadius = Real.sqrt (q : ℝ) * r ∧
      aroundDist D A ≤ ENNReal.ofReal (Cminus / (2 * Cplus)) *
        OptimalConstants.Ratios.setDist D (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r)) ↔
      TwoScale.Consolidated.loopF D x r q ≤ ENNReal.ofReal (Cminus / (2 * Cplus)) *
        OptimalConstants.Ratios.setDist D (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r) := by
  rw [loopF_eq_e5Annulus]
  constructor
  · rintro ⟨A, hc, hi, ho, hcost⟩
    have hA : A = e5Annulus r q x := by
      apply Subtype.ext
      have hc' : A.1.1 = x := hc
      have hi' : A.1.2.1 = (q : ℝ) * r := hi
      have ho' : A.1.2.2 = Real.sqrt (q : ℝ) * r := ho
      exact Prod.ext hc' (Prod.ext hi' ho')
    exact hA ▸ hcost
  · intro hcost
    exact ⟨e5Annulus r q x, rfl, rfl, rfl, hcost⟩

 
theorem e5AnnulusCondition_measurable (z : ℂ) (r : Ioi (0 : ℝ))
    (q : Ioo (0 : ℝ) (1 / 100)) (Cminus Cplus : ℝ) :
    MeasurableSet {p : LSCMetric × ℂ |
      TwoScale.Consolidated.loopF p.1 p.2 r q ≤ ENNReal.ofReal (Cminus / (2 * Cplus)) *
        OptimalConstants.Ratios.setDist p.1 (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r)} := by
  have hOpen : IsOpen (TwoScale.S36Events.eventMiddle z r) := by
    unfold TwoScale.S36Events.eventMiddle
    exact Metric.isOpen_ball.sdiff Metric.isClosed_closedBall
  have hClosed : IsClosed (TwoScale.S36Events.eventBoundary z r) := by
    unfold TwoScale.S36Events.eventBoundary
    exact Metric.isClosed_sphere.union Metric.isClosed_sphere
  have hDistBase : Measurable (fun D : LSCMetric =>
      OptimalConstants.Ratios.setDist D (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r)) :=
    measurable_setDist_open_closed _ _ hOpen hClosed
  have hDist : Measurable (fun p : LSCMetric × ℂ =>
      OptimalConstants.Ratios.setDist p.1 (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r)) :=
    hDistBase.comp measurable_fst
  exact measurableSet_le (e5LoopCost_measurable r q) (measurable_const.mul hDist)

end SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents
