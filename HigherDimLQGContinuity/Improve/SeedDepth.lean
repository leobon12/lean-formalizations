import HigherDimLQGContinuity.Improve.StepDepth

/-!
# The mesh lies below the tolerance times the seed gain
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

/-- The polynomial lower bound on the site-certificate parameter controls
the additional depth needed for the net-count estimate. -/
theorem q11_depth_below_seed {θ d0 v P V : ℝ}
    (hθ : 0 < θ) (hd0 : 0 < d0) (hv : 0 < v)
    (hθlo : Real.exp (-P) ≤ θ)
    (hV : P + Real.log v⁻¹ + Real.log (2 / d0) ≤ V) :
    Real.exp (-V) ≤ v * (θ * d0 / 2) := by
  have hlogθ : -P ≤ Real.log θ := by
    have hh := Real.log_le_log (Real.exp_pos _) hθlo
    simpa only [Real.log_exp] using hh
  have hlogv : Real.log v⁻¹ = -Real.log v := by
    rw [Real.log_inv]
  have hd02 : 0 < d0 / 2 := by positivity
  have hlogd : Real.log (2 / d0) = -Real.log (d0 / 2) := by
    have heq : 2 / d0 = (d0 / 2)⁻¹ := by field_simp
    rw [heq, Real.log_inv]
  have hlogprod : Real.log (v * (θ * d0 / 2)) =
      Real.log v + Real.log θ + Real.log (d0 / 2) := by
    have heq : v * (θ * d0 / 2) = v * θ * (d0 / 2) := by ring
    rw [heq, Real.log_mul (mul_pos hv hθ).ne' hd02.ne', Real.log_mul hv.ne' hθ.ne']
  have hlogle : -V ≤ Real.log (v * (θ * d0 / 2)) := by
    rw [hlogprod]
    rw [hlogv, hlogd] at hV
    linarith only [hθlo, hV, hlogθ]
  have hh := Real.exp_le_exp.mpr hlogle
  rwa [Real.exp_log (by positivity : 0 < v * (θ * d0 / 2))] at hh

end HigherDimLQGContinuity
