import SupercriticalLQGUniqueness.B2.DG20Lim.NestedGoodCostConv
import Mathlib.Analysis.Normed.Module.Basic

 

set_option autoImplicit false
noncomputable section

open Set Metric Filter Topology

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem RatAnnulus.inner_radius_le_outer_radius (A : RatAnnulus) :
    (A.inner.radius : ℝ) ≤ (A.outer.radius : ℝ) := by
  have hs : A.inner.closedDisk ⊆ A.outer.closedDisk :=
    A.nested.2.trans A.outer.openDisk_subset_closedDisk
  have hd := Metric.diam_mono hs isBounded_closedBall
  rw [RatCircle.closedDisk, Metric.diam_closedBall_eq _
    (by exact_mod_cast A.inner.radius_nonneg),
    RatCircle.closedDisk, Metric.diam_closedBall_eq _
      (by exact_mod_cast A.outer.radius_nonneg)] at hd
  linarith

theorem inner_radius_tendsto_zero_of_outer
    (B : ℕ → RatAnnulus)
    (houter : Tendsto (fun n => ((B n).outer.radius : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => ((B n).inner.radius : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero
    (fun n => by exact_mod_cast (B n).inner.radius_nonneg)
    (fun n => (B n).inner_radius_le_outer_radius)
    houter

end SupercriticalLQGUniqueness.B2.DG20Lim
