import HigherDimLQGMetric.Kernel.CovDefs
import HigherDimLQGMetric.Kernel.ConvKernelMain
import HigherDimLQGMetric.Field.Affine

/-!
# Scaled convolution kernel

Positive dilation preserves the unit mass of the inverse Fourier kernel and
translates its symbol to `ζ ↦ kernelSymbol κ (εζ)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory FourierTransform
open scoped FourierTransform RealInnerProductSpace

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {κ : Rd d → ℝ}

theorem integrable_convKernelEps (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (convKernelEps κ ε) := by
  unfold convKernelEps
  exact ((integrable_convKernel hd hκ).comp_smul (inv_ne_zero hε.ne')).const_mul _

theorem integral_convKernelEps_eq_one (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε) :
    ∫ x : Rd d, convKernelEps κ ε x = 1 := by
  unfold convKernelEps
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg volume (convKernel κ) hε.le,
    finrank_rd, smul_eq_mul,
    convKernel_integral_eq_one (by omega) hκ (integrable_convKernel hd hκ)]
  rw [mul_one, Real.rpow_neg (le_of_lt hε), Real.rpow_natCast]
  exact inv_mul_cancel₀ (pow_ne_zero _ hε.ne')

private theorem fourier_comp_inv_smul (f : Rd d → ℂ) {ε : ℝ}
    (hε : 0 < ε) (ζ : Rd d) :
    𝓕 (fun x => f (ε⁻¹ • x)) ζ = (ε ^ d : ℝ) • 𝓕 f (ε • ζ) := by
  have h := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (Rd d))
    (fun u => 𝐞 (-inner ℝ u (ε • ζ)) • f u) hε.le
  rw [finrank_rd] at h
  rw [Real.fourier_eq, Real.fourier_eq]
  have hi (x : Rd d) : inner ℝ (ε⁻¹ • x) (ε • ζ) = inner ℝ x ζ := by
    rw [real_inner_smul_left, real_inner_smul_right]
    field_simp
  simp_rw [hi] at h
  exact h

theorem convKernelEps_fourier_eq (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (ζ : Rd d) :
    𝓕 (fun x : Rd d => (convKernelEps κ ε x : ℂ)) ζ =
      (kernelSymbol κ (ε • ζ) : ℂ) := by
  have he : (fun x : Rd d => (convKernelEps κ ε x : ℂ)) =
      fun x => ((ε ^ (-(d : ℝ)) : ℝ) : ℂ) *
        (convKernel κ (ε⁻¹ • x) : ℂ) := by
    funext x
    simp only [convKernelEps, Complex.ofReal_mul]
  rw [he]
  have hs : 𝓕 (fun x : Rd d => ((ε ^ (-(d : ℝ)) : ℝ) : ℂ) *
      (convKernel κ (ε⁻¹ • x) : ℂ)) ζ =
      ((ε ^ (-(d : ℝ)) : ℝ) : ℂ) *
        𝓕 (fun x : Rd d => (convKernel κ (ε⁻¹ • x) : ℂ)) ζ := by
    have h := congrArg (fun g : Rd d → ℂ => g ζ)
      (VectorFourier.fourierIntegral_const_smul 𝐞 (volume : Measure (Rd d))
        (innerₗ (Rd d)) (fun x : Rd d => (convKernel κ (ε⁻¹ • x) : ℂ))
        ((ε ^ (-(d : ℝ)) : ℝ) : ℂ))
    change 𝓕 (((ε ^ (-(d : ℝ)) : ℝ) : ℂ) •
      (fun x : Rd d => (convKernel κ (ε⁻¹ • x) : ℂ))) ζ =
      (((ε ^ (-(d : ℝ)) : ℝ) : ℂ) •
        𝓕 (fun x : Rd d => (convKernel κ (ε⁻¹ • x) : ℂ)) ζ) at h
    have heq : (((ε ^ (-(d : ℝ)) : ℝ) : ℂ) •
        (fun x : Rd d => (convKernel κ (ε⁻¹ • x) : ℂ))) =
        (fun x : Rd d => ((ε ^ (-(d : ℝ)) : ℝ) : ℂ) *
          (convKernel κ (ε⁻¹ • x) : ℂ)) := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
    rw [heq] at h
    simpa only [smul_eq_mul] using h
  rw [hs, fourier_comp_inv_smul (fun x : Rd d => (convKernel κ x : ℂ)) hε ζ]
  rw [convKernel_fourier_eq (by omega) hκ (integrable_convKernel hd hκ)]
  simp only [Complex.real_smul]
  have hp : ε ^ (-(d : ℝ)) * ε ^ d = 1 := by
    rw [Real.rpow_neg hε.le, Real.rpow_natCast]
    exact inv_mul_cancel₀ (pow_ne_zero _ hε.ne')
  rw [← mul_assoc, ← Complex.ofReal_mul, hp]
  simp

end HigherDimLQGMetric
