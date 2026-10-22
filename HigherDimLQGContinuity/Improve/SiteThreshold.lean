import HigherDimLQGContinuity.Core.Interfaces

/-!
# The rounded-up site count meets the forcing threshold
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

theorem q11_site_threshold (V : ℝ) :
    (Real.exp (-V)) ^ (-(1 / 2 : ℝ)) ≤
      (⌈Real.exp (V / 2)⌉₊ : ℝ) := by
  have heq : (Real.exp (-V)) ^ (-(1 / 2 : ℝ)) = Real.exp (V / 2) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  rw [heq]
  exact Nat.le_ceil _

end HigherDimLQGContinuity
