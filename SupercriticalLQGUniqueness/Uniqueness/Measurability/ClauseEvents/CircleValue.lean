import SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents.CircleAverageBorel




set_option autoImplicit false
noncomputable section
open Filter
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents

 

def circleValue (r : Set.Ioi (0 : ℝ)) (z : ℂ)
    (g : LQGMetric.DistC) : ℝ :=
  liminf (fun n : ℕ =>
    Real.circleAverage (fun x => g (LQGMetric.bumpTest n x)) z r) atTop

theorem circleValue_measurable (r : Set.Ioi (0 : ℝ)) (z : ℂ) :
    Measurable (circleValue r z) := by
  have hm : ∀ n : ℕ, Measurable (fun g : LQGMetric.DistC =>
      Real.circleAverage (fun x => g (LQGMetric.bumpTest n x)) z r) := by
    intro n
    have heq : (fun g : LQGMetric.DistC =>
        Real.circleAverage (fun x => g (LQGMetric.bumpTest n x)) z r) =
        (fun g : LQGMetric.DistC => g (LQGMetric.CircleAvg.circBump n z r)) := by
      funext g
      exact LQGMetric.CircleAvg.mollAvg_eq g n z r
    rw [heq]
    exact LQGMetric.GFFInv.measurable_pair _
  exact Measurable.liminf hm

theorem circleValue_eq_of_IsCircleAverage (r : Set.Ioi (0 : ℝ))
    (z : ℂ) (g : LQGMetric.DistC) (c : ℝ)
    (h : IsCircleAverage g r z c) : circleValue r z g = c := by
  exact Filter.Tendsto.liminf_eq h

theorem circleValue_graph_measurable (r : Set.Ioi (0 : ℝ)) (z : ℂ) :
    MeasurableSet {g : LQGMetric.DistC |
      IsCircleAverage g r z (circleValue r z g)} := by
  have hf : Measurable (fun g : LQGMetric.DistC => (g, circleValue r z g)) :=
    measurable_id.prodMk (circleValue_measurable r z)
  exact (Measurability.AttainedEvents.circleAverageGraph_measurable r z).preimage hf

end SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents
