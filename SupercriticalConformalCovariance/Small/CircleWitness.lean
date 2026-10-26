import SupercriticalConformalCovariance.Small.Normalization
import SupercriticalLQGUniqueness.Frozen.IsCircleAverage

set_option autoImplicit false
noncomputable section
open Set Filter Topology
namespace SupercriticalConformalCovariance.Small
open LQGMetric

/-- The paper's existential circle-average witness equals the library's canonical value. -/
theorem circleAvg_eq_of_IsCircleAverage (g : DistC) (r : Ioi (0 : ℝ))
    (z : ℂ) (c : ℝ)
    (hc : SupercriticalLQGUniqueness.IsCircleAverage g r z c) :
    circleAvg g (r : ℝ) z = c := by
  have hlim : Tendsto (fun n => CircleAvg.mollAvg g n z (r : ℝ)) atTop (𝓝 c) := by
    have heq : (fun n => CircleAvg.mollAvg g n z (r : ℝ)) =
        (fun n => Real.circleAverage (fun x => g (bumpTest n x)) z (r : ℝ)) := by
      funext n
      rfl
    rw [heq]
    exact hc
  exact CircleAvg.circleAvg_eq_of_tendsto hlim

end SupercriticalConformalCovariance.Small
