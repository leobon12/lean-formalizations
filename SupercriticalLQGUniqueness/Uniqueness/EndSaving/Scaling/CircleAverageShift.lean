import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling.ShiftedLocalTransfer
import BR1Bridges




set_option autoImplicit false
noncomputable section
open Filter Topology
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling
open LQGMetric (DistC)

 

theorem isCircleAverage_addFun (g : DistC) (f : C(ℂ, ℝ))
    (r : Set.Ioi (0 : ℝ)) (z : ℂ) (a : ℝ)
    (ha : IsCircleAverage g r z a) :
    IsCircleAverage (LQGMetric.addFun g f) r z
      (a + Real.circleAverage f z (r : ℝ)) := by
  unfold IsCircleAverage at ha ⊢
  have hseq : ∀ n : ℕ,
      Real.circleAverage
        (fun x => LQGMetric.addFun g f (LQGMetric.bumpTest n x)) z (r : ℝ) =
      Real.circleAverage
        (fun x => g (LQGMetric.bumpTest n x)) z (r : ℝ) +
      Real.circleAverage
        (fun x => LQGMetric.ofCont f (LQGMetric.bumpTest n x)) z (r : ℝ) := by
    intro n
    rw [LQGMetric.CircleAvg.circleAverage_pairing,
      LQGMetric.CircleAvg.circleAverage_pairing,
      LQGMetric.CircleAvg.circleAverage_pairing]
    simp only [LQGMetric.addFun, add_apply]
  simp_rw [hseq]
  exact ha.add (LQGMetric.CircleAvg.tendsto_mollAvg_ofCont f r z)

 

theorem isCircleAverage_addFun_of_zero_sphere (g : DistC) (f : C(ℂ, ℝ))
    (r : Set.Ioi (0 : ℝ)) (z : ℂ) (a : ℝ)
    (ha : IsCircleAverage g r z a)
    (hf : ∀ x ∈ Metric.sphere z (r : ℝ), f x = 0) :
    IsCircleAverage (LQGMetric.addFun g f) r z a := by
  have hfavg : Real.circleAverage f z (r : ℝ) = 0 := by
    rw [Real.circleAverage_congr_sphere (f₂ := fun _ => 0)]
    · simp [Real.circleAverage_def]
    · intro x hx
      have hr : (0 : ℝ) < (r : ℝ) := r.property
      exact hf x (by simpa only [abs_of_pos hr] using hx)
  simpa only [hfavg, add_zero] using isCircleAverage_addFun g f r z a ha

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling
