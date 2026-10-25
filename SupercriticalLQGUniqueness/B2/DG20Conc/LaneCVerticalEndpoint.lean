import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCLargeKRightVertical
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCLargeKLeftVertical

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF

 

theorem laneC_left_endpoint_outer_of_center_buffer
    {c x : ℂ} {r : ℝ}
    (hbuf : 2 * r ≤ c.re)
    (hx : x ∈ (rectAB 1 1).side₁) :
    2 * r ≤ dist x c := by
  have hxre : x.re = 0 := (mem_rectAB_side₁.mp hx).1
  have hcoord : c.re ≤ |(x - c).re| := by
    have h := neg_le_abs (x - c).re
    simp only [Complex.sub_re, hxre] at h ⊢
    linarith
  exact hbuf.trans (hcoord.trans (Complex.abs_re_le_norm (x - c) |>.trans_eq
    (dist_eq_norm x c).symm))

 

theorem laneC_right_endpoint_outer_of_center_buffer
    {c x : ℂ} {r : ℝ}
    (hbuf : c.re + 2 * r ≤ 1)
    (hx : x ∈ (rectAB 1 1).side₂) :
    2 * r ≤ dist x c := by
  have hxre : x.re = 1 := (mem_rectAB_side₂.mp hx).1
  have hcoord : 1 - c.re ≤ |(x - c).re| := by
    have h := le_abs_self (x - c).re
    simp only [Complex.sub_re, hxre] at h ⊢
    linarith
  have hbuf' : 2 * r ≤ 1 - c.re := by linarith
  exact hbuf'.trans (hcoord.trans (Complex.abs_re_le_norm (x - c) |>.trans_eq
    (dist_eq_norm x c).symm))

end SupercriticalLQGUniqueness.B2.DG20Conc
