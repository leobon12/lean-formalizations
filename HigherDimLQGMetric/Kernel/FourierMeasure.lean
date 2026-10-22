import HigherDimLQGMetric.Kernel.FourierAutoCorr
import HigherDimLFPP.Field.Measures

/-!
# Fourier transforms of finite measures and fixed-scale covariance

The spectral representation is obtained by inverting the compactly supported
autocorrelation and then applying Fubini to finite measures.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory FourierTransform Complex Set
open scoped FourierTransform RealInnerProductSpace ComplexConjugate

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- Fourier transform of a finite measure in Mathlib's `-2πi` convention. -/
def measureFourier (μ : Measure (Rd d)) (ζ : Rd d) : ℂ :=
  ∫ z, (𝐞 (-inner ℝ z ζ) : ℂ) ∂μ

theorem measurable_measureFourier (μ : Measure (Rd d)) [IsFiniteMeasure μ] :
    Measurable (measureFourier μ) := by
  have hm : Measurable (fun p : Rd d × Rd d =>
      (𝐞 (-inner ℝ p.2 p.1) : ℂ)) := by fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem integrable_measureFourier_phase (μ : Measure (Rd d)) [IsFiniteMeasure μ]
    (ζ : Rd d) : Integrable (fun z : Rd d => (𝐞 (-inner ℝ z ζ) : ℂ)) μ := by
  refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun z => ?_)
  simp

theorem measureFourier_conj (μ : Measure (Rd d)) [IsFiniteMeasure μ]
    (ζ : Rd d) :
    conj (measureFourier μ ζ) = ∫ z, (𝐞 (inner ℝ z ζ) : ℂ) ∂μ := by
  rw [measureFourier, ← integral_conj]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp

theorem measureFourier_norm_le (μ : Measure (Rd d)) [IsFiniteMeasure μ]
    (ζ : Rd d) : ‖measureFourier μ ζ‖ ≤ μ.real univ := by
  rw [measureFourier]
  calc
    ‖∫ z, (𝐞 (-inner ℝ z ζ) : ℂ) ∂μ‖ ≤
        ∫ z, ‖(𝐞 (-inner ℝ z ζ) : ℂ)‖ ∂μ := norm_integral_le_integral_norm _
    _ = μ.real univ := by simp

private theorem phase_sub_mul (ξ z w : Rd d) :
    (𝐞 (inner ℝ ξ (z - w)) : ℂ) =
      (𝐞 (inner ℝ ξ z) : ℂ) * (𝐞 (-inner ℝ ξ w) : ℂ) := by
  rw [inner_sub_right]
  simp only [Real.fourierChar_apply]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem integrable_scale_phase_prod
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {t : ℝ} (ht : 0 < t) (μ μ' : Measure (Rd d))
    [IsFiniteMeasure μ] [IsFiniteMeasure μ'] :
    Integrable (fun q : (Rd d × Rd d) × Rd d =>
      𝐞 (inner ℝ q.2 (q.1.1 - q.1.2)) •
        ((t ^ ((d : ℝ) - 1) *
          ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • q.2)‖ ^ 2 : ℝ) : ℂ))
      ((μ.prod μ').prod volume) := by
  have hs : Integrable (fun ξ : Rd d =>
      ((t ^ ((d : ℝ) - 1) *
        ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • ξ)‖ ^ 2 : ℝ) : ℂ)) :=
    (integrable_scaleSpectral hκ ht).ofReal
  have hs' := hs.comp_snd (μ.prod μ')
  apply Integrable.mono hs'
  · have hphase : Measurable (fun q : (Rd d × Rd d) × Rd d =>
        (𝐞 (inner ℝ q.2 (q.1.1 - q.1.2)) : ℂ)) := by fun_prop
    convert hphase.aestronglyMeasurable.mul hs'.aestronglyMeasurable using 1
    ext q
    rfl
  · exact ae_of_all _ fun q => by simp

theorem integrable_scaleSpectral_measureFourier
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {t : ℝ} (ht : 0 < t) (μ μ' : Measure (Rd d))
    [IsFiniteMeasure μ] [IsFiniteMeasure μ'] :
    Integrable (fun ξ : Rd d =>
      ((t ^ ((d : ℝ) - 1) *
        ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • ξ)‖ ^ 2 : ℝ) : ℂ) *
        conj (measureFourier μ ξ) * measureFourier μ' ξ) := by
  let B : ℝ := μ.real univ * μ'.real univ
  have hdom : Integrable (fun ξ : Rd d => B *
      (t ^ ((d : ℝ) - 1) *
        ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • ξ)‖ ^ 2)) :=
    (integrable_scaleSpectral hκ ht).const_mul B
  apply Integrable.mono' hdom
  · have hm : Measurable (fun ξ : Rd d =>
        ((t ^ ((d : ℝ) - 1) *
          ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • ξ)‖ ^ 2 : ℝ) : ℂ)) := by
      have hc := continuous_fourier_kernel hκ
      fun_prop
    have hconj : Measurable (fun ξ => conj (measureFourier μ ξ)) :=
      Complex.continuous_conj.measurable.comp (measurable_measureFourier μ)
    exact ((hm.mul hconj).mul
      (measurable_measureFourier μ')).aestronglyMeasurable
  · exact ae_of_all _ fun ξ => by
      have hμ := measureFourier_norm_le μ ξ
      have hμ' := measureFourier_norm_le μ' ξ
      have hs : 0 ≤ t ^ ((d : ℝ) - 1) *
          ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • ξ)‖ ^ 2 := by positivity
      simp only [norm_mul, norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg ht.le _),
        abs_of_nonneg (sq_nonneg
          (‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • ξ)‖))]
      dsimp [B]
      calc
        t ^ ((d : ℝ) - 1) * ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • ξ)‖ ^ 2 *
            ‖measureFourier μ ξ‖ * ‖measureFourier μ' ξ‖ =
          (‖measureFourier μ ξ‖ * ‖measureFourier μ' ξ‖) *
            (t ^ ((d : ℝ) - 1) *
              ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • ξ)‖ ^ 2) := by ring
        _ ≤ μ.real univ * μ'.real univ *
          (t ^ ((d : ℝ) - 1) *
              ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • ξ)‖ ^ 2) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hμ hμ' (norm_nonneg _) measureReal_nonneg) hs

/-- The fixed-scale autocorrelation pairing has the spectral representation. -/
theorem integral_scaleAutoCorr_eq_fourier
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {t : ℝ} (ht : 0 < t) (μ μ' : Measure (Rd d))
    [IsFiniteMeasure μ] [IsFiniteMeasure μ'] :
    ((∫ p : Rd d × Rd d,
      HigherDimLFPP.autoCorr κ (t⁻¹ • (p.1 - p.2)) / t
      ∂(μ.prod μ') : ℝ) : ℂ) =
      ∫ ξ : Rd d,
        ((t ^ ((d : ℝ) - 1) *
          ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • ξ)‖ ^ 2 : ℝ) : ℂ) *
          conj (measureFourier μ ξ) * measureFourier μ' ξ := by
  rw [← integral_complex_ofReal]
  simp_rw [scaleAutoCorr_eq_integral_fourier hκ ht]
  rw [integral_integral_swap (integrable_scale_phase_prod hκ ht μ μ')]
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  have hp (p : Rd d × Rd d) :
      𝐞 (inner ℝ ξ (p.1 - p.2)) •
        ((t ^ ((d : ℝ) - 1) *
          ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • ξ)‖ ^ 2 : ℝ) : ℂ) =
      ((t ^ ((d : ℝ) - 1) *
          ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • ξ)‖ ^ 2 : ℝ) : ℂ) *
        (𝐞 (inner ℝ ξ p.1) : ℂ) * (𝐞 (-inner ℝ ξ p.2) : ℂ) := by
    rw [Circle.smul_def, smul_eq_mul, phase_sub_mul]
    ring
  simp_rw [hp]
  let c : ℂ := ((t ^ ((d : ℝ) - 1) *
    ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • ξ)‖ ^ 2 : ℝ) : ℂ)
  have hplus : (∫ z : Rd d, (𝐞 (inner ℝ ξ z) : ℂ) ∂μ) =
      conj (measureFourier μ ξ) := by
    rw [measureFourier_conj]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    change (𝐞 (inner ℝ ξ z) : ℂ) = (𝐞 (inner ℝ z ξ) : ℂ)
    rw [real_inner_comm ξ z]
  have hminus : (∫ w : Rd d, (𝐞 (-inner ℝ ξ w) : ℂ) ∂μ') =
      measureFourier μ' ξ := by
    unfold measureFourier
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    change (𝐞 (-inner ℝ ξ w) : ℂ) = (𝐞 (-inner ℝ w ξ) : ℂ)
    rw [real_inner_comm ξ w]
  change (∫ p : Rd d × Rd d,
    c * (𝐞 (inner ℝ ξ p.1) : ℂ) * (𝐞 (-inner ℝ ξ p.2) : ℂ)
      ∂(μ.prod μ')) = c * conj (measureFourier μ ξ) * measureFourier μ' ξ
  calc
    (∫ p : Rd d × Rd d,
      c * (𝐞 (inner ℝ ξ p.1) : ℂ) * (𝐞 (-inner ℝ ξ p.2) : ℂ) ∂(μ.prod μ')) =
        ∫ p : Rd d × Rd d,
          c * ((𝐞 (inner ℝ ξ p.1) : ℂ) *
            (𝐞 (-inner ℝ ξ p.2) : ℂ)) ∂(μ.prod μ') := by
          refine integral_congr_ae (ae_of_all _ fun p => ?_)
          ring
    _ = c * ((∫ z : Rd d, (𝐞 (inner ℝ ξ z) : ℂ) ∂μ) *
      (∫ w : Rd d, (𝐞 (-inner ℝ ξ w) : ℂ) ∂μ')) := by
        rw [integral_const_mul]
        exact congrArg (fun a : ℂ => c * a)
          (integral_prod_mul
            (μ := μ) (ν := μ')
            (fun z : Rd d => (𝐞 (inner ℝ ξ z) : ℂ))
            (fun w : Rd d => (𝐞 (-inner ℝ ξ w) : ℂ)))
    _ = _ := by rw [hplus, hminus]; ring

private theorem integral_sub_sub_add_complex {α : Type*} [MeasurableSpace α]
    {m : Measure α} {F₁ F₂ F₃ F₄ : α → ℂ}
    (i₁ : Integrable F₁ m) (i₂ : Integrable F₂ m)
    (i₃ : Integrable F₃ m) (i₄ : Integrable F₄ m) :
    ∫ a, (F₁ a - F₂ a - F₃ a + F₄ a) ∂m =
      (∫ a, F₁ a ∂m) - (∫ a, F₂ a ∂m) -
        (∫ a, F₃ a ∂m) + ∫ a, F₄ a ∂m := by
  have i₁₂ : Integrable (fun a => F₁ a - F₂ a) m := i₁.sub i₂
  have i₁₂₃ : Integrable (fun a => F₁ a - F₂ a - F₃ a) m := i₁₂.sub i₃
  rw [integral_add i₁₂₃ i₄, integral_sub i₁₂ i₃, integral_sub i₁ i₂]

/-- Fixed-scale Fourier representation for two signed finite-measure pairs. -/
theorem scalePair_eq_fourier
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {t : ℝ} (ht : 0 < t) (μ ν μ' ν' : Measure (Rd d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure μ'] [IsFiniteMeasure ν'] :
    ((HigherDimLFPP.scalePair κ t μ ν μ' ν' : ℝ) : ℂ) =
      ∫ ξ : Rd d,
        ((t ^ ((d : ℝ) - 1) *
          ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • ξ)‖ ^ 2 : ℝ) : ℂ) *
          (conj (measureFourier μ ξ) - conj (measureFourier ν ξ)) *
          (measureFourier μ' ξ - measureFourier ν' ξ) := by
  let F (a b : Measure (Rd d)) (ξ : Rd d) : ℂ :=
    ((t ^ ((d : ℝ) - 1) *
      ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • ξ)‖ ^ 2 : ℝ) : ℂ) *
      conj (measureFourier a ξ) * measureFourier b ξ
  have i11 : Integrable (F μ μ') := integrable_scaleSpectral_measureFourier hκ ht μ μ'
  have i12 : Integrable (F μ ν') := integrable_scaleSpectral_measureFourier hκ ht μ ν'
  have i21 : Integrable (F ν μ') := integrable_scaleSpectral_measureFourier hκ ht ν μ'
  have i22 : Integrable (F ν ν') := integrable_scaleSpectral_measureFourier hκ ht ν ν'
  unfold HigherDimLFPP.scalePair HigherDimLFPP.mixInt
  simp only [Complex.ofReal_add, Complex.ofReal_sub]
  rw [integral_scaleAutoCorr_eq_fourier hκ ht μ μ',
    integral_scaleAutoCorr_eq_fourier hκ ht μ ν',
    integral_scaleAutoCorr_eq_fourier hκ ht ν μ',
    integral_scaleAutoCorr_eq_fourier hκ ht ν ν']
  change (∫ ξ, F μ μ' ξ) - (∫ ξ, F μ ν' ξ) -
      (∫ ξ, F ν μ' ξ) + (∫ ξ, F ν ν' ξ) = _
  rw [← integral_sub_sub_add_complex i11 i12 i21 i22]
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  dsimp [F]
  ring

end HigherDimLQGMetric
