import HigherDimLQGContinuity.Improve.SeedDepth

/-!
# A common exponential scale below fixed mesh powers
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

/-- A fixed multiplier of the depth can make its exponential smaller than
any prescribed fixed prefactor times a power of the mesh. -/
theorem q11_exp_below_power {V z B γ : ℝ}
    (hV : 1 ≤ V) (hz : 0 < z)
    (hB : γ + max 0 (-Real.log z) ≤ B) :
    Real.exp (-(B * V)) ≤ z * (Real.exp (-V)) ^ γ := by
  have hBγ : 0 ≤ B - γ := by linarith [le_max_left (0 : ℝ) (-Real.log z)]
  have hmul : -Real.log z ≤ (B - γ) * V := by
    have hh : max 0 (-Real.log z) ≤ B - γ := by linarith
    exact (le_mul_of_one_le_right (by linarith : 0 ≤ B - γ) hV).trans'
      (le_trans (le_max_right _ _) hh)
  have hlog : -(B * V) ≤ Real.log z - γ * V := by linarith
  have hpow : (Real.exp (-V)) ^ γ = Real.exp (-(γ * V)) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  rw [hpow]
  have heq : z * Real.exp (-(γ * V)) = Real.exp (Real.log z - γ * V) := by
    calc
      z * Real.exp (-(γ * V)) =
          Real.exp (Real.log z) * Real.exp (-(γ * V)) := by rw [Real.exp_log hz]
      _ = Real.exp (Real.log z + -(γ * V)) := (Real.exp_add _ _).symm
      _ = Real.exp (Real.log z - γ * V) := by congr 1
  rw [heq]
  exact Real.exp_le_exp.mpr hlog

end HigherDimLQGContinuity
