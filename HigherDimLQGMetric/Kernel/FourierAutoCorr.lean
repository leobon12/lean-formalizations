import HigherDimLQGMetric.Kernel.OneVarFourier
import HigherDimLFPP.Field.Kernel
import Mathlib.Analysis.Fourier.Convolution

/-!
# Fourier transform of the band autocorrelation

The autocorrelation of an admissible radial kernel is its Schwartz convolution
with itself.  Its spectral density is the squared Fourier modulus.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory FourierTransform Complex
open scoped FourierTransform RealInnerProductSpace Convolution SchwartzMap ComplexConjugate

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {κ : Rd d → ℝ}

/-- The complex autocorrelation as a Schwartz function. -/
def autoCorrSchwartz (hκ : HigherDimLFPP.IsLFPPKernel κ) : 𝓢(Rd d, ℂ) :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (kernelSchwartz hκ)
    (kernelSchwartz hκ)

theorem autoCorrSchwartz_apply (hκ : HigherDimLFPP.IsLFPPKernel κ) (x : Rd d) :
    autoCorrSchwartz hκ x = (HigherDimLFPP.autoCorr κ x : ℂ) := by
  have heq : (∫ y : Rd d, κ y * κ (x - y)) = HigherDimLFPP.autoCorr κ x := by
    unfold HigherDimLFPP.autoCorr
    rw [← integral_neg_eq_self (fun y : Rd d => κ y * κ (y + x)) volume]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    dsimp only
    rw [hκ.neg]
    congr 1
    abel_nf
  rw [autoCorrSchwartz, SchwartzMap.convolution_apply]
  unfold MeasureTheory.convolution
  simp only [kernelSchwartz_apply, ContinuousLinearMap.mul_apply', ← Complex.ofReal_mul]
  rw [integral_complex_ofReal, heq]

theorem autoCorrSchwartz_fourier (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ζ : Rd d) :
    𝓕 (autoCorrSchwartz hκ) ζ =
      (𝓕 (fun x : Rd d => (κ x : ℂ)) ζ) ^ 2 := by
  rw [autoCorrSchwartz, SchwartzMap.fourier_convolution,
    SchwartzMap.pairing_apply_apply, ContinuousLinearMap.mul_apply',
    coe_fourier_kernelSchwartz hκ]
  ring

theorem fourier_kernel_even (hκ : HigherDimLFPP.IsLFPPKernel κ) (ζ : Rd d) :
    𝓕 (fun x : Rd d => (κ x : ℂ)) (-ζ) =
      𝓕 (fun x : Rd d => (κ x : ℂ)) ζ := by
  let R : Rd d ≃ₗᵢ[ℝ] Rd d := LinearIsometryEquiv.neg ℝ
  have hf : (fun x : Rd d => (κ x : ℂ)) ∘ R =
      (fun x : Rd d => (κ x : ℂ)) := by
    funext x
    change (κ (-x) : ℂ) = (κ x : ℂ)
    rw [hκ.neg]
  have h := Real.fourier_comp_linearIsometry R
    (fun x : Rd d => (κ x : ℂ)) ζ
  rw [hf] at h
  simpa only [show R ζ = -ζ from rfl] using h.symm

theorem fourier_kernel_conj (ζ : Rd d) :
    conj (𝓕 (fun x : Rd d => (κ x : ℂ)) ζ) =
      𝓕 (fun x : Rd d => (κ x : ℂ)) (-ζ) := by
  rw [Real.fourier_eq, Real.fourier_eq, ← integral_conj]
  congr 1
  funext x
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, map_mul,
    Complex.conj_ofReal, ← Complex.exp_conj]
  congr 1
  simp

theorem fourier_kernel_real (hκ : HigherDimLFPP.IsLFPPKernel κ) (ζ : Rd d) :
    conj (𝓕 (fun x : Rd d => (κ x : ℂ)) ζ) =
      𝓕 (fun x : Rd d => (κ x : ℂ)) ζ :=
  (fourier_kernel_conj ζ).trans (fourier_kernel_even hκ ζ)

theorem autoCorrSchwartz_fourier_normSq (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ζ : Rd d) :
    𝓕 (autoCorrSchwartz hκ) ζ =
      ((‖𝓕 (fun x : Rd d => (κ x : ℂ)) ζ‖ ^ 2 : ℝ) : ℂ) := by
  rw [autoCorrSchwartz_fourier hκ ζ]
  let z := 𝓕 (fun x : Rd d => (κ x : ℂ)) ζ
  change z ^ 2 = ((‖z‖ ^ 2 : ℝ) : ℂ)
  calc
    z ^ 2 = z * conj z := by rw [fourier_kernel_real hκ ζ]; ring
    _ = ((‖z‖ ^ 2 : ℝ) : ℂ) := by simpa only [Complex.ofReal_pow] using Complex.mul_conj' z

/-- Pointwise Fourier inversion for the real autocorrelation. -/
theorem autoCorr_eq_integral_fourier (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (x : Rd d) :
    (HigherDimLFPP.autoCorr κ x : ℂ) =
      ∫ ζ : Rd d, 𝐞 (inner ℝ ζ x) •
        ((‖𝓕 (fun y : Rd d => (κ y : ℂ)) ζ‖ ^ 2 : ℝ) : ℂ) := by
  rw [← autoCorrSchwartz_apply hκ x]
  have hi := congrArg (fun f : 𝓢(Rd d, ℂ) => f x)
    (show 𝓕⁻ (𝓕 (autoCorrSchwartz hκ)) = autoCorrSchwartz hκ from
      FourierPair.fourierInv_fourier_eq (autoCorrSchwartz hκ))
  rw [← hi, SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
  refine integral_congr_ae (ae_of_all _ fun ζ => ?_)
  rw [SchwartzMap.fourier_coe]
  exact congrArg (fun z : ℂ => 𝐞 (inner ℝ ζ x) • z)
    (autoCorrSchwartz_fourier_normSq hκ ζ)

/-- Fourier inversion of the fixed-scale covariance kernel. -/
theorem scaleAutoCorr_eq_integral_fourier (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {t : ℝ} (ht : 0 < t) (v : Rd d) :
    ((HigherDimLFPP.autoCorr κ (t⁻¹ • v) / t : ℝ) : ℂ) =
      ∫ ξ : Rd d, 𝐞 (inner ℝ ξ v) •
        ((t ^ ((d : ℝ) - 1) *
          ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • ξ)‖ ^ 2 : ℝ) : ℂ) := by
  let f : Rd d → ℂ := fun ζ => 𝐞 (inner ℝ ζ (t⁻¹ • v)) •
    ((‖𝓕 (fun y : Rd d => (κ y : ℂ)) ζ‖ ^ 2 : ℝ) : ℂ)
  have hscale := Measure.integral_comp_smul_of_nonneg (volume : Measure (Rd d)) f t
    (hR := ht.le)
  rw [finrank_euclideanSpace_fin] at hscale
  have hinner (ξ : Rd d) : inner ℝ (t • ξ) (t⁻¹ • v) = inner ℝ ξ v := by
    rw [real_inner_smul_left, real_inner_smul_right]
    field_simp
  have hexp :
      (fun ξ : Rd d => 𝐞 (inner ℝ ξ v) •
        ((t ^ ((d : ℝ) - 1) *
          ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • ξ)‖ ^ 2 : ℝ) : ℂ)) =
      fun ξ => (t ^ ((d : ℝ) - 1) : ℝ) • f (t • ξ) := by
    funext ξ
    simp only [f, hinner, Complex.ofReal_mul, Complex.real_smul, Circle.smul_def,
      smul_eq_mul]
    ring
  rw [hexp, integral_smul, hscale]
  rw [← autoCorr_eq_integral_fourier hκ (t⁻¹ • v)]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow,
    Complex.ofReal_div]
  have hpow : t ^ ((d : ℝ) - 1) * (t ^ d)⁻¹ = t⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg ht.le, ← Real.rpow_add ht]
    convert Real.rpow_neg_one t using 1
    ring_nf
  have hpowC : ((t ^ ((d : ℝ) - 1) : ℝ) : ℂ) * ((t ^ d : ℝ) : ℂ)⁻¹ =
      (t : ℂ)⁻¹ := by exact_mod_cast hpow
  rw [Complex.ofReal_pow] at hpowC
  rw [← mul_assoc, hpowC]
  ring

/-- The frequency density at a positive white-noise scale is integrable. -/
theorem integrable_scaleSpectral (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun ξ : Rd d => t ^ ((d : ℝ) - 1) *
      ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • ξ)‖ ^ 2) := by
  have hbase : Integrable (fun ξ : Rd d =>
      ‖𝓕 (fun y : Rd d => (κ y : ℂ)) ξ‖ ^ 2) := by
    convert ((𝓕 (kernelSchwartz hκ)).memLp 2 volume).integrable_norm_pow
      (by norm_num) using 1
    ext ξ
    rw [coe_fourier_kernelSchwartz hκ]
  exact (hbase.comp_smul ht.ne').const_mul _

end HigherDimLQGMetric
