import HigherDimLQGMetric.Kernel.CovSmoothed
import HigherDimLQGMetric.Kernel.FourierSymbol

/-!
# Fourier transform of a finite-measure convolution
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory FourierTransform
open scoped FourierTransform RealInnerProductSpace ComplexConjugate

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {κ : Rd d → ℝ}

private theorem integrable_phase_prod_convKernelEps (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Rd d)) [IsFiniteMeasure μ] (ζ : Rd d) :
    Integrable (fun p : Rd d × Rd d =>
      𝐞 (-inner ℝ p.1 ζ) •
        (convKernelEps κ ε (p.1 - p.2) : ℂ)) (volume.prod μ) := by
  have hbase : Integrable (fun p : Rd d × Rd d =>
      (convKernelEps κ ε (p.1 - p.2) : ℂ)) (volume.prod μ) :=
    (integrable_prod_convKernelEps hd hκ hε μ).ofReal
  apply hbase.norm.mono'
  · have hm : Measurable (fun p : Rd d × Rd d =>
        𝐞 (-inner ℝ p.1 ζ) •
          (convKernelEps κ ε (p.1 - p.2) : ℂ)) := by
      have hc : Continuous (convKernelEps κ ε) :=
        continuous_const.mul
          ((convKernel_contDiff (by omega) hκ).continuous.comp
            (continuous_const_smul _))
      have hp : Measurable (fun p : Rd d × Rd d =>
          (𝐞 (-inner ℝ p.1 ζ) : ℂ)) := by fun_prop
      have hk : Measurable (fun p : Rd d × Rd d =>
          (convKernelEps κ ε (p.1 - p.2) : ℂ)) :=
        Complex.measurable_ofReal.comp
          (hc.measurable.comp (measurable_fst.sub measurable_snd))
      change Measurable (fun p : Rd d × Rd d =>
        (𝐞 (-inner ℝ p.1 ζ) : ℂ) *
          (convKernelEps κ ε (p.1 - p.2) : ℂ))
      exact hp.mul hk
    exact hm.aestronglyMeasurable
  · exact ae_of_all _ fun p => by simp

private theorem fourier_translate_convKernelEps (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (z ζ : Rd d) :
    𝓕 (fun x : Rd d => (convKernelEps κ ε (x - z) : ℂ)) ζ =
      (𝐞 (-inner ℝ z ζ) : ℂ) * (kernelSymbol κ (ε • ζ) : ℂ) := by
  have h := congrArg (fun F : Rd d → ℂ => F ζ)
    (VectorFourier.fourierIntegral_comp_add_right 𝐞 volume
      (innerₗ (Rd d)) (fun x : Rd d => (convKernelEps κ ε x : ℂ)) (-z))
  change 𝓕 (fun x : Rd d => (convKernelEps κ ε (x + -z) : ℂ)) ζ =
    𝐞 (inner ℝ (-z) ζ) •
      𝓕 (fun x : Rd d => (convKernelEps κ ε x : ℂ)) ζ at h
  simpa only [sub_eq_add_neg, inner_neg_left, Circle.smul_def,
    smul_eq_mul, convKernelEps_fourier_eq hd hκ hε ζ] using h

theorem fourier_measConv_eq (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Rd d)) [IsFiniteMeasure μ] (ζ : Rd d) :
    𝓕 (fun x : Rd d => (measConv κ ε μ x : ℂ)) ζ =
      (kernelSymbol κ (ε • ζ) : ℂ) * measureFourier μ ζ := by
  have hF := integrable_phase_prod_convKernelEps hd hκ hε μ ζ
  have he (x : Rd d) :
      (measConv κ ε μ x : ℂ) =
        ∫ z, (convKernelEps κ ε (x - z) : ℂ) ∂μ := by
    rw [measConv, integral_complex_ofReal]
  calc
    𝓕 (fun x : Rd d => (measConv κ ε μ x : ℂ)) ζ =
        ∫ x : Rd d, 𝐞 (-inner ℝ x ζ) •
          (measConv κ ε μ x : ℂ) := by rw [Real.fourier_eq]
    _ = ∫ x : Rd d, ∫ z : Rd d,
          𝐞 (-inner ℝ x ζ) •
            (convKernelEps κ ε (x - z) : ℂ) ∂μ := by
        congr 1
        funext x
        rw [he]
        simp only [Circle.smul_def, smul_eq_mul, integral_const_mul]
    _ = ∫ z : Rd d, ∫ x : Rd d,
          𝐞 (-inner ℝ x ζ) •
            (convKernelEps κ ε (x - z) : ℂ) ∂volume ∂μ :=
        integral_integral_swap hF
    _ = ∫ z : Rd d,
          (𝐞 (-inner ℝ z ζ) : ℂ) * (kernelSymbol κ (ε • ζ) : ℂ) ∂μ := by
        apply integral_congr_ae
        exact ae_of_all _ fun z => by
          change (∫ x : Rd d, 𝐞 (-inner ℝ x ζ) •
              (convKernelEps κ ε (x - z) : ℂ)) =
            (𝐞 (-inner ℝ z ζ) : ℂ) * (kernelSymbol κ (ε • ζ) : ℂ)
          simpa only [Real.fourier_eq] using
            fourier_translate_convKernelEps hd hκ hε z ζ
    _ = _ := by
        rw [integral_mul_const]
        unfold measureFourier
        rw [mul_comm]

end HigherDimLQGMetric
