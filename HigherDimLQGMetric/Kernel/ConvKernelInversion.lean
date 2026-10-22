import HigherDimLQGMetric.Kernel.ConvKernelSmooth
import Mathlib.Analysis.Fourier.Inversion

/-!
# Fourier inversion and mass of the convolution kernel

These implications use the spatial integrability supplied by the A2.5 decay estimate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped FourierTransform
namespace HigherDimLQGMetric
open HigherDimLFPP (Rd)
variable {d : ℕ} {κ : Rd d → ℝ}

/-- Fourier inversion for the kernel, given spatial integrability. -/
theorem convKernel_fourier_eq (hd : 0 < d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hK : Integrable (convKernel κ)) :
    𝓕 (fun x : Rd d => (convKernel κ x : ℂ)) =
      fun ζ => (kernelSymbol κ ζ : ℂ) := by
  let o : Rd d → ℂ := fun ζ => (kernelSymbol κ ζ : ℂ)
  have hcont : Continuous o :=
    Complex.continuous_ofReal.comp (kernelSymbol_continuous hd hκ)
  have ho : Integrable o := by
    apply (integrable_norm_iff hcont.aestronglyMeasurable).mp
    simpa [o] using integrable_kernelSymbol_complex_moment hd hκ 0
  have hFour : Integrable (𝓕 o) := by
    have hkc : Integrable (fun x : Rd d => (convKernel κ x : ℂ)) := hK.ofReal
    have hneg := hkc.comp_neg
    convert hneg using 1
    funext x
    have h := Real.fourierInv_eq_fourier_neg o (-x)
    simp only [neg_neg] at h
    rw [← h]
    exact (convKernel_complex_eq_fourierInv (κ := κ) (-x)).symm
  have h := hcont.fourier_fourierInv_eq ho hFour
  have heq : (fun x : Rd d => (convKernel κ x : ℂ)) = 𝓕⁻ o := by
    funext x
    exact convKernel_complex_eq_fourierInv x
  rw [heq]
  exact h

/-- The integral of the kernel is one, given spatial integrability. -/
theorem convKernel_integral_eq_one (hd : 0 < d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hK : Integrable (convKernel κ)) :
    ∫ x : Rd d, convKernel κ x = 1 := by
  have h0 := congrFun (convKernel_fourier_eq hd hκ hK) (0 : Rd d)
  have hm : (∫ x : Rd d, (convKernel κ x : ℂ)) = 1 := by
    simpa [Real.fourier_eq, kernelSymbol_zero hd hκ] using h0
  rw [integral_complex_ofReal] at hm
  exact_mod_cast hm

end HigherDimLQGMetric
