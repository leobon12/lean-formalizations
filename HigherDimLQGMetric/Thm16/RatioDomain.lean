import HigherDimLQGMetric.Thm16.RatioSample
import Mathlib.Analysis.Normed.Module.Connected

/-! A fixed bounded connected domain containing the relevant sphere annulus. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

theorem l9c_ann_subset_ball_three {d : ℕ} {r : ℝ} (hr : 0 < r) :
    ann (0 : Rd d) (r / 2) (2 * r) ⊆ ball 0 (3 * r) := by
  intro x hx
  rw [mem_ball, dist_eq_norm, sub_zero]
  dsimp [ann] at hx
  simp only [sub_zero] at hx
  linarith [hx.2]

theorem l9c_sphere_point_mem_ball_three {d : ℕ} (hd : 0 < d)
    {r : ℝ} (hr : 0 < r) :
    r • e₁ d ∈ ball (0 : Rd d) (3 * r) ∧
      -(r • e₁ d) ∈ ball 0 (3 * r) := by
  have hn : ‖r • e₁ d‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, HigherDimLFPP.norm_e₁ hd]
    ring
  constructor
  · rw [mem_ball, dist_eq_norm, sub_zero, hn]
    linarith
  · rw [mem_ball, dist_eq_norm, sub_zero, norm_neg, hn]
    linarith

end HigherDimLQGMetric
