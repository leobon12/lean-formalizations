import HigherDimLQGMetric.LfppTight.SphereLogCorr
import HigherDimLQGMetric.Kernel.CovKernelMoment
import HigherDimLQGMetric.ConvField.ContBound

/-! Uniform logarithmic absolute moment of the convolution kernel. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_integral_abs_logKernelEps_le {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : ε ∈ Set.Ioc (0 : ℝ) 1) :
    (∫ x : Rd d, |convKernelEps κ ε x| * Real.log (2 + ‖x‖)) ≤
      ∫ x : Rd d, |convKernel κ x| * Real.log (2 + ‖x‖) := by
  let F : Rd d → ℝ := fun u => |convKernel κ u| * Real.log (2 + ε * ‖u‖)
  let G : Rd d → ℝ := fun u => |convKernel κ u| * Real.log (2 + ‖u‖)
  have hG : Integrable G := by
    have hi := (integrable_logMoment_convKernel hd hκ).abs
    convert hi using 1
    funext x
    dsimp [G]
    rw [abs_mul, abs_of_nonneg (Real.log_nonneg (by linarith [norm_nonneg x] : 1 ≤ 2 + ‖x‖))]
    ring
  have hF : Integrable F := by
    apply hG.mono'
    · have hfc : Continuous F := by
        apply Continuous.mul
        · exact (convKernel_contDiff (by omega : 0 < d) hκ).continuous.abs
        · apply Continuous.log
          · fun_prop
          · intro u
            have hn := mul_nonneg hε.1.le (norm_nonneg u)
            linarith
      exact hfc.aestronglyMeasurable
    · apply ae_of_all
      intro u
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · have hle : 2 + ε * ‖u‖ ≤ 2 + ‖u‖ := by
          nlinarith [mul_le_mul_of_nonneg_right hε.2 (norm_nonneg u)]
        exact mul_le_mul_of_nonneg_left
          (Real.log_le_log (by nlinarith [mul_nonneg hε.1.le (norm_nonneg u)]) hle) (abs_nonneg _)
      · exact mul_nonneg (abs_nonneg _)
          (Real.log_nonneg (by nlinarith [mul_nonneg hε.1.le (norm_nonneg u)]))
  have hs := integral_comp_affinePt F (inv_pos.mpr hε.1) (0 : Rd d)
  simp only [add_zero, inv_pow, inv_inv] at hs
  have hp : ε ^ (-(d : ℝ)) * ε ^ d = 1 := by
    rw [Real.rpow_neg hε.1.le, Real.rpow_natCast]
    exact inv_mul_cancel₀ (pow_ne_zero _ hε.1.ne')
  have heq : (∫ x : Rd d, |convKernelEps κ ε x| * Real.log (2 + ‖x‖)) =
      ∫ u : Rd d, F u := by
    calc
      (∫ x : Rd d, |convKernelEps κ ε x| * Real.log (2 + ‖x‖)) =
          ε ^ (-(d : ℝ)) * ∫ x : Rd d, F (ε⁻¹ • x) := by
            rw [← integral_const_mul]
            apply integral_congr_ae
            apply ae_of_all
            intro x
            dsimp [F, convKernelEps]
            rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hε.1.le _),
              norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε.1)]
            have he : ε * (ε⁻¹ * ‖x‖) = ‖x‖ := by
              rw [← mul_assoc, mul_inv_cancel₀ hε.1.ne', one_mul]
            rw [he]
            ring
      _ = ε ^ (-(d : ℝ)) * (ε ^ d * ∫ u : Rd d, F u) := by rw [hs]
      _ = ∫ u : Rd d, F u := by rw [← mul_assoc, hp, one_mul]
  rw [heq]
  exact integral_mono hF hG fun u => by
    dsimp [F, G]
    have hle : 2 + ε * ‖u‖ ≤ 2 + ‖u‖ := by
      nlinarith [mul_le_mul_of_nonneg_right hε.2 (norm_nonneg u)]
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (by nlinarith [mul_nonneg hε.1.le (norm_nonneg u)]) hle) (abs_nonneg _)

end HigherDimLQGMetric
