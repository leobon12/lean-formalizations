import SupercriticalLQGUniqueness.Uniqueness.Objects.Shield.ShieldCM




set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shield

theorem gradEnergy_shieldAnnBump (K : ℝ) :
    LQGMetric.gradEnergy (shieldAnnBump K) =
      K ^ 2 * LQGMetric.gradEnergy (shieldAnnBump 1) := by
  have hfun : (shieldAnnBump K : ℂ → ℝ) =
      fun y => K • (shieldAnnBump 1 y) := by
    funext y
    change K * (shieldBumpIn y - shieldBumpOut y) =
      K • (1 * (shieldBumpIn y - shieldBumpOut y))
    simp [smul_eq_mul]
  have hfderiv (z : ℂ) :
      fderiv ℝ (shieldAnnBump K : ℂ → ℝ) z =
        K • fderiv ℝ (shieldAnnBump 1 : ℂ → ℝ) z := by
    rw [hfun]
    exact fderiv_fun_const_smul
      ((shieldAnnBump 1).contDiff.differentiable (by norm_num) z) K
  unfold LQGMetric.gradEnergy
  simp_rw [hfderiv, norm_smul, Real.norm_eq_abs]
  have hpoint (z : ℂ) :
      (|K| * ‖fderiv ℝ (shieldAnnBump 1 : ℂ → ℝ) z‖) ^ 2 =
        K ^ 2 * ‖fderiv ℝ (shieldAnnBump 1 : ℂ → ℝ) z‖ ^ 2 := by
    rw [mul_pow, sq_abs]
  simp_rw [hpoint, integral_const_mul]
  ring

end SupercriticalLQGUniqueness.Uniqueness.Objects.Shield
