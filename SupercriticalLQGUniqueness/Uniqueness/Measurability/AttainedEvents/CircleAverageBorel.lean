import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.Section3
import LQGMetric.Field.CircleAvgGauss
import LQGMetric.Field.MeasurableAvg




 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter

namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents

private theorem mollifiedAverage_measurable (n : ℕ)
    (r : Set.Ioi (0 : ℝ)) (z : ℂ) :
    Measurable (fun g : LQGMetric.DistC =>
      Real.circleAverage (fun x => g (LQGMetric.bumpTest n x)) z r) := by
  have heq : (fun g : LQGMetric.DistC =>
      Real.circleAverage (fun x => g (LQGMetric.bumpTest n x)) z r) =
      (fun g : LQGMetric.DistC => g (LQGMetric.CircleAvg.circBump n z r)) := by
    funext g
    exact LQGMetric.CircleAvg.mollAvg_eq g n z r
  rw [heq]
  exact LQGMetric.GFFInv.measurable_pair _

 

theorem circleAverageGraph_measurable (r : Set.Ioi (0 : ℝ)) (z : ℂ) :
    MeasurableSet {p : LQGMetric.DistC × ℝ |
      IsCircleAverage p.1 r z p.2} := by
  have hm : ∀ n : ℕ, Measurable (fun p : LQGMetric.DistC × ℝ =>
      Real.circleAverage (fun x => p.1 (LQGMetric.bumpTest n x)) z r) := by
    intro n
    exact (mollifiedAverage_measurable n r z).comp measurable_fst
  have hg : Measurable (fun p : LQGMetric.DistC × ℝ => p.2) := measurable_snd
  exact MeasureTheory.measurableSet_tendsto_fun hm hg

end SupercriticalLQGUniqueness.Uniqueness.Measurability.AttainedEvents
