import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteAnnulusInternalCompare

 


set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem centered_shell_subset_buffered
    (x y r : ℚ) (hr : 0 < r) (w : ℂ)
    (hinner : (r : ℝ) ≤ ‖w - Complex.mk (x : ℝ) (y : ℝ)‖)
    (houter : ‖w - Complex.mk (x : ℝ) (y : ℝ)‖ ≤ 2 * (r : ℝ)) :
    w ∈ bufferedCenteredAnnulus x y r := by
  change (r : ℝ) / 2 < ‖w - Complex.mk (x : ℝ) (y : ℝ)‖ ∧
    ‖w - Complex.mk (x : ℝ) (y : ℝ)‖ < 4 * (r : ℝ)
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  constructor <;> linarith

theorem centeredRatAnnulus_subset_buffered
    (x y r : ℚ) (hr : 0 < r) :
    (centeredRatAnnulus x y r hr).toSet ⊆ bufferedCenteredAnnulus x y r := by
  intro w hw
  rw [centeredRatAnnulus_eq_closedAnn] at hw
  exact centered_shell_subset_buffered x y r hr w hw.1 hw.2

end SupercriticalLQGUniqueness.B2.DG20Lim
