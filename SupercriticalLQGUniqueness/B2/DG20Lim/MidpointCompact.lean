import SupercriticalLQGUniqueness.B2.DG20Lim.RemoteCircleCrossing
import SupercriticalLQGUniqueness.B2.DG20Lim.Recovery

 


set_option autoImplicit false
noncomputable section

open Set Metric Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem eventually_mem_outerDisk_of_short_left_leg
    (R : RData) (D : ℕ → LQGMetric.ContMetric)
    (hlen : ∀ n, (D n).IsLength)
    (O P : RatCircle) (hOP : P.SurroundsCircle O)
    {u v : ℂ} (hu : u ∈ O.openDisk)
    (zn wn xn : ℕ → ℂ)
    (hzn : Tendsto zn atTop (𝓝 u))
    (hdist : Tendsto (fun n => ENNReal.ofReal ((D n).1 (zn n, wn n)))
      atTop (𝓝 (R.DfromR u v)))
    (hcircle : Tendsto (fun n => LQGMetric.Blueprint.setDist
      (D n) O.toSet P.toSet) atTop (𝓝 (R.across O P)))
    (hshort : ∀ᶠ n in atTop,
      ENNReal.ofReal ((D n).1 (zn n, xn n)) ≤
        ENNReal.ofReal ((D n).1 (zn n, wn n)) + 1)
    (hgap : R.DfromR u v + 1 < R.across O P) :
    ∀ᶠ n in atTop, xn n ∈ P.closedDisk := by
  have hznO : ∀ᶠ n in atTop, zn n ∈ O.openDisk :=
    hzn (isOpen_ball.mem_nhds hu)
  have hcost : ∀ᶠ n in atTop,
      ENNReal.ofReal ((D n).1 (zn n, wn n)) + 1 <
        LQGMetric.Blueprint.setDist (D n) O.toSet P.toSet :=
    (hdist.add tendsto_const_nhds).eventually_lt hcircle hgap
  filter_upwards [hznO, hshort, hcost] with n hnO hnShort hnCost
  by_contra hnP
  have hcross := setDist_nested_circles_le_pointDist
    (D n) (hlen n) O P hOP hnO (by simpa using hnP)
  exact (not_lt_of_ge hcross) (lt_of_le_of_lt hnShort hnCost)

end SupercriticalLQGUniqueness.B2.DG20Lim
