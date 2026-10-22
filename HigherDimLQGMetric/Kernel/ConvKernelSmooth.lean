import HigherDimLQGMetric.Kernel.ConvKernelSymbol
import HigherDimLQGMetric.Frozen.ConvKernel
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Smoothness of the convolution kernel

The symbol has moments of every order, so its inverse Fourier transform is smooth.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped FourierTransform ComplexConjugate

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {κ : Rd d → ℝ}

/-- All natural moments of the complex embedding of `kernelSymbol` are integrable. -/
theorem integrable_kernelSymbol_complex_moment (hd : 0 < d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (n : ℕ) :
    Integrable (fun ζ : Rd d => ‖ζ‖ ^ n * ‖(kernelSymbol κ ζ : ℂ)‖) := by
  simpa only [Complex.norm_real, Real.norm_eq_abs] using
    integrable_kernelSymbol_moment hd hκ n

/-- The inverse Fourier kernel is smooth. -/
theorem convKernel_contDiff (hd : 0 < d) (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ) := by
  let o : Rd d → ℂ := fun ζ => (kernelSymbol κ ζ : ℂ)
  have hfour : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (𝓕 o) :=
    Real.contDiff_fourier (fun n _ => integrable_kernelSymbol_complex_moment hd hκ n)
  have hinv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (𝓕⁻ o) := by
    have h := hfour.comp (contDiff_id.neg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Rd d => -x))
    convert h using 1
    funext x
    exact Real.fourierInv_eq_fourier_neg o x
  change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (𝓕⁻ o x).re)
  exact Complex.reCLM.contDiff.comp hinv

/-- The real inverse Fourier kernel depends only on the Euclidean norm. -/
theorem convKernel_radial {x y : Rd d} (h : ‖x‖ = ‖y‖) :
    convKernel κ x = convKernel κ y := by
  set A : Rd d ≃ₗᵢ[ℝ] Rd d := Submodule.reflection (Submodule.span ℝ {x - y})ᗮ
  have hA : A x = y := Submodule.reflection_sub h
  have hcomp : (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) ∘ A =
      fun ζ : Rd d => (kernelSymbol κ ζ : ℂ) := by
    funext ζ
    simp only [Function.comp_apply]
    rw [kernelSymbol_eq_sqrt_symbolSq, kernelSymbol_eq_sqrt_symbolSq, A.norm_map]
  unfold convKernel
  rw [← hA, ← Real.fourierInv_comp_linearIsometry A, hcomp]

/-- The complex inverse Fourier transform of this real even symbol is even. -/
theorem kernelSymbol_fourierInv_even (x : Rd d) :
    𝓕⁻ (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) (-x) =
      𝓕⁻ (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) x := by
  let A : Rd d ≃ₗᵢ[ℝ] Rd d := LinearIsometryEquiv.neg ℝ
  have hcomp : (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) ∘ A =
      (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) := by
    funext ζ
    have hneg : A ζ = -ζ := rfl
    simp only [Function.comp_apply, hneg, kernelSymbol_eq_sqrt_symbolSq, norm_neg]
  have h := Real.fourierInv_comp_linearIsometry A
    (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) x
  rw [hcomp] at h
  have hneg : A x = -x := rfl
  simpa only [hneg] using h.symm

/-- Conjugation of the inverse transform reverses the spatial argument. -/
theorem kernelSymbol_fourierInv_conj (x : Rd d) :
    conj (𝓕⁻ (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) x) =
      𝓕⁻ (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) (-x) := by
  rw [Real.fourierInv_eq', Real.fourierInv_eq', ← integral_conj]
  congr 1
  funext ζ
  simp only [smul_eq_mul, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 1
  simp

/-- The real-valued frozen kernel is the full complex inverse Fourier transform. -/
theorem convKernel_complex_eq_fourierInv (x : Rd d) :
    (convKernel κ x : ℂ) =
      𝓕⁻ (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) x := by
  have heq : conj (𝓕⁻ (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) x) =
      𝓕⁻ (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) x :=
    (kernelSymbol_fourierInv_conj x).trans (kernelSymbol_fourierInv_even x)
  have him := Complex.conj_eq_iff_im.mp heq
  apply Complex.ext
  · rfl
  · simp [convKernel, him]

/-- The inverse transform is bounded by the `L¹` norm of its symbol. -/
theorem convKernel_abs_le_integral_symbol (x : Rd d) :
    |convKernel κ x| ≤ ∫ ζ : Rd d, |kernelSymbol κ ζ| := by
  unfold convKernel
  apply (Complex.abs_re_le_norm _).trans
  rw [Real.fourierInv_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext ζ
  simp only [Circle.norm_smul, Complex.norm_real, Real.norm_eq_abs]

end HigherDimLQGMetric
