import SupercriticalLQGUniqueness.Uniqueness.EndSaving.FiniteEvents.NormalizedRNWindow




 




set_option autoImplicit false
noncomputable section
open Filter Topology
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling
open LQGMetric (DistC)

theorem isCircleAverage_addConst (g : DistC)
    (r : Set.Ioi (0 : ℝ)) (z : ℂ) (a c : ℝ)
    (ha : IsCircleAverage g r z a) :
    IsCircleAverage (LQGMetric.addConst g c) r z (a + c) := by
  unfold IsCircleAverage at ha ⊢
  simp only [LQGMetric.CircleAvg.circleAverage_addConst]
  exact ha.add (tendsto_const_nhds (x := c))

theorem isCircleAverage_addConst_iff (g : DistC)
    (r : Set.Ioi (0 : ℝ)) (z : ℂ) (a c : ℝ) :
    IsCircleAverage (LQGMetric.addConst g c) r z (a + c) ↔
      IsCircleAverage g r z a := by
  constructor
  · intro ha
    have h := isCircleAverage_addConst
      (LQGMetric.addConst g c) r z (a + c) (-c) ha
    rw [LQGMetric.GFFLaw.addConst_addConst] at h
    simpa only [add_neg_cancel, LQGMetric.GFFLaw.addConst_zero',
      add_assoc, add_zero] using h
  · exact isCircleAverage_addConst g r z a c

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling
