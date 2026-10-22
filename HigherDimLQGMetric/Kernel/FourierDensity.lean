import HigherDimLQGMetric.Kernel.CovDensity

/-!
# Fourier transforms of positive and negative density measures
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory FourierTransform
open scoped FourierTransform RealInnerProductSpace

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {f : Rd d → ℝ}

theorem measureFourier_posM_eq (hf : Measurable f) (ζ : Rd d) :
    measureFourier (posM f) ζ =
      ∫ z : Rd d, (𝐞 (-inner ℝ z ζ) : ℂ) * ((max (f z) 0 : ℝ) : ℂ) := by
  rw [measureFourier, posM,
    integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    change (ENNReal.ofReal (f z)).toReal • (𝐞 (-inner ℝ z ζ) : ℂ) =
      (𝐞 (-inner ℝ z ζ) : ℂ) * ((max (f z) 0 : ℝ) : ℂ)
    rw [ENNReal.toReal_ofReal', Complex.real_smul]
    ring

theorem measureFourier_posM_sub_eq_fourier (hf : Integrable f)
    (hmeas : Measurable f) (ζ : Rd d) :
    measureFourier (posM f) ζ - measureFourier (posM (-f)) ζ =
      𝓕 (fun z : Rd d => (f z : ℂ)) ζ := by
  haveI : IsFiniteMeasure (posM f) := isFiniteMeasure_posM_of_integrable hf
  haveI : IsFiniteMeasure (posM (-f)) := isFiniteMeasure_posM_of_integrable hf.neg
  have hp : Integrable (fun z : Rd d =>
      (𝐞 (-inner ℝ z ζ) : ℂ) * ((max (f z) 0 : ℝ) : ℂ)) := by
    apply hf.pos_part.mono'
    · fun_prop
    · exact ae_of_all _ fun z => by
        change ‖(𝐞 (-inner ℝ z ζ) : ℂ) * ((max (f z) 0 : ℝ) : ℂ)‖ ≤
          max (f z) 0
        have hphase : ‖(𝐞 (-inner ℝ z ζ) : ℂ)‖ = 1 := by simp
        rw [norm_mul, hphase, one_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (le_max_right (f z) 0)]
  have hn : Integrable (fun z : Rd d =>
      (𝐞 (-inner ℝ z ζ) : ℂ) * ((max (-f z) 0 : ℝ) : ℂ)) := by
    apply hf.neg_part.mono'
    · fun_prop
    · exact ae_of_all _ fun z => by
        change ‖(𝐞 (-inner ℝ z ζ) : ℂ) * ((max (-f z) 0 : ℝ) : ℂ)‖ ≤
          max (-f z) 0
        have hphase : ‖(𝐞 (-inner ℝ z ζ) : ℂ)‖ = 1 := by simp
        rw [norm_mul, hphase, one_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (le_max_right (-f z) 0)]
  rw [measureFourier_posM_eq hmeas, measureFourier_posM_eq hmeas.neg]
  simp only [Pi.neg_apply]
  rw [← integral_sub hp hn, Real.fourier_eq]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    simp only [Circle.smul_def, smul_eq_mul]
    rw [← mul_sub]
    congr 1
    rw [← Complex.ofReal_sub, max_zero_sub_max_neg_zero_eq_self]

theorem measureFourier_smoothed_sub (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : 0 < ε)
    (μ ν : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ζ : Rd d) :
    measureFourier
      (posM (fun x => measConv κ ε μ x - measConv κ ε ν x)) ζ -
      measureFourier
        (posM (fun x => -(measConv κ ε μ x - measConv κ ε ν x))) ζ =
      (kernelSymbol κ (ε • ζ) : ℂ) *
        (measureFourier μ ζ - measureFourier ν ζ) := by
  let f : Rd d → ℝ := fun x => measConv κ ε μ x - measConv κ ε ν x
  have hf : Integrable f :=
    (integrable_measConv hd hκ hε μ).sub (integrable_measConv hd hκ hε ν)
  have hmf : Measurable f :=
    (measurable_measConv hd hκ ε μ).sub (measurable_measConv hd hκ ε ν)
  change measureFourier (posM f) ζ - measureFourier (posM (-f)) ζ = _
  rw [measureFourier_posM_sub_eq_fourier hf hmf]
  have he : (fun x : Rd d => (f x : ℂ)) =
      (fun x : Rd d => (measConv κ ε μ x : ℂ)) -
        (fun x : Rd d => (measConv κ ε ν x : ℂ)) := by
    funext x
    dsimp [f]
    rw [Complex.ofReal_sub]
  rw [he]
  have hμ : Integrable (fun x : Rd d => (measConv κ ε μ x : ℂ)) :=
    (integrable_measConv hd hκ hε μ).ofReal
  have hν : Integrable (fun x : Rd d => (measConv κ ε ν x : ℂ)) :=
    (integrable_measConv hd hκ hε ν).ofReal
  have hiμ := (Real.fourierIntegral_convergent_iff ζ).mpr hμ
  have hiν := (Real.fourierIntegral_convergent_iff ζ).mpr hν
  rw [Real.fourier_eq]
  simp_rw [Pi.sub_apply, smul_sub]
  rw [integral_sub hiμ hiν]
  change 𝓕 (fun x : Rd d => (measConv κ ε μ x : ℂ)) ζ -
      𝓕 (fun x : Rd d => (measConv κ ε ν x : ℂ)) ζ = _
  rw [fourier_measConv_eq hd hκ hε μ ζ,
    fourier_measConv_eq hd hκ hε ν ζ]
  ring

end HigherDimLQGMetric
