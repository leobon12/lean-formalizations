import HigherDimLQGMetric.LfppTight.CoupledShellTail

/-! The unit shell crossing is a lower bound for the point distance. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

theorem l6a_shell_le_point {d : ℕ} (hd : 2 ≤ d) (ξ : ℝ)
    (φ : Rd d → ℝ) (hφ : Continuous φ) :
    DGZ.lfppSetDist ξ φ univ (sphere (0 : Rd d) (1 / 2)) (sphere 0 1) ≤
      DGZ.lfppMetric ξ φ 0 (e₁ d) := by
  apply DGZ.lfppSetDist_sphere_le_lfppDistOn hφ (by norm_num)
    (mem_closedBall_self (by norm_num))
  · rw [mem_ball, dist_zero_right, HigherDimLFPP.norm_e₁ (by omega : 0 < d)]
    exact not_lt.2 le_rfl
  · exact HigherDimLFPP.PcwJoined.of_convex convex_univ (mem_univ _) (mem_univ _)

end HigherDimLQGMetric
