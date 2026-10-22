import HigherDimLQGMetric.LogEnergy.Basic
import HigherDimLQGMetric.LGF.Density
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Fourier representation of logarithmic energy

We use the all-scale covariance identity from `HigherDimLFPP` and Plancherel
at each scale. The Fourier convention is `exp (-2πi⟨x, ζ⟩)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory FourierTransform Filter
open HigherDimLFPP (Rd)
open scoped SchwartzMap FourierTransform RealInnerProductSpace Topology

namespace HigherDimLQGMetric

variable {d : ℕ}

/-- A real test function viewed as a complex Schwartz function. -/
def testComplexSchwartz (φ : TestRd d) : 𝓢(Rd d, ℂ) :=
  (φ.hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp φ.contDiff)

@[simp] theorem testComplexSchwartz_apply (φ : TestRd d) (x : Rd d) :
    testComplexSchwartz φ x = (φ x : ℂ) := rfl

/-- Plancherel for the convolution of two complex Schwartz functions. -/
theorem integral_norm_sq_schwartzConvolution (f g : 𝓢(Rd d, ℂ)) :
    (∫ x, ‖SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) f g x‖ ^ 2) =
      ∫ ξ, ‖𝓕 f ξ‖ ^ 2 * ‖𝓕 g ξ‖ ^ 2 := by
  rw [← SchwartzMap.integral_norm_sq_fourier
    (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) f g)]
  simp only [SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply,
    ContinuousLinearMap.mul_apply', norm_mul, mul_pow]

/-- A scaled admissible kernel is a complex Schwartz function. -/
def scaleKernelComplexSchwartz {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {t : ℝ} (ht : 0 < t) : 𝓢(Rd d, ℂ) := by
  have hs : HasCompactSupport (fun x : Rd d => HigherDimLFPP.scaleKernel κ t x) := by
    have h₁ : HasCompactSupport (fun x : Rd d => κ (t⁻¹ • x)) :=
      hκ.hasCompactSupport.comp_smul (inv_ne_zero ht.ne')
    unfold HigherDimLFPP.scaleKernel
    exact h₁.mul_left
  have hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Rd d => HigherDimLFPP.scaleKernel κ t x) := by
    unfold HigherDimLFPP.scaleKernel
    exact contDiff_const.mul (hκ.contDiff.comp (contDiff_const_smul t⁻¹))
  exact (hs.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hd)

@[simp] theorem scaleKernelComplexSchwartz_apply {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {t : ℝ} (ht : 0 < t) (x : Rd d) :
    scaleKernelComplexSchwartz hκ ht x = (HigherDimLFPP.scaleKernel κ t x : ℂ) := rfl

/-- Fourier scaling for the inverse dilation `x ↦ t⁻¹x`. -/
private theorem fourier_comp_inv_smul (f : Rd d → ℂ) {t : ℝ} (ht : 0 < t) (ζ : Rd d) :
    𝓕 (fun x => f (t⁻¹ • x)) ζ = (t ^ d : ℝ) • 𝓕 f (t • ζ) := by
  have h := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (Rd d))
    (fun u => 𝐞 (-inner ℝ u (t • ζ)) • f u) ht.le
  rw [finrank_rd] at h
  rw [Real.fourier_eq, Real.fourier_eq]
  have hi (x : Rd d) : inner ℝ (t⁻¹ • x) (t • ζ) = inner ℝ x ζ := by
    rw [real_inner_smul_left, real_inner_smul_right]
    field_simp
  simp_rw [hi] at h
  exact h

/-- Fourier scaling of the LFPP kernel at one positive scale. -/
private theorem fourier_scaleKernel {κ : Rd d → ℝ} {t : ℝ} (ht : 0 < t) (ζ : Rd d) :
    𝓕 (fun x : Rd d => (HigherDimLFPP.scaleKernel κ t x : ℂ)) ζ =
      ((t ^ (-((d : ℝ) + 1) / 2) * t ^ d : ℝ) : ℂ) *
        𝓕 (fun x : Rd d => (κ x : ℂ)) (t • ζ) := by
  have he : (fun x : Rd d => (HigherDimLFPP.scaleKernel κ t x : ℂ)) =
      fun x => ((t ^ (-((d : ℝ) + 1) / 2) : ℝ) : ℂ) * (κ (t⁻¹ • x) : ℂ) := by
    funext x
    simp only [HigherDimLFPP.scaleKernel, Complex.ofReal_mul]
  rw [he]
  have hs : 𝓕 (fun x : Rd d => ((t ^ (-((d : ℝ) + 1) / 2) : ℝ) : ℂ) *
      (κ (t⁻¹ • x) : ℂ)) ζ = ((t ^ (-((d : ℝ) + 1) / 2) : ℝ) : ℂ) *
        𝓕 (fun x : Rd d => (κ (t⁻¹ • x) : ℂ)) ζ := by
    have h := congrArg (fun g : Rd d → ℂ => g ζ)
      (VectorFourier.fourierIntegral_const_smul 𝐞 (volume : Measure (Rd d))
        (innerₗ (Rd d)) (fun x : Rd d => (κ (t⁻¹ • x) : ℂ))
        ((t ^ (-((d : ℝ) + 1) / 2) : ℝ) : ℂ))
    change 𝓕 (((t ^ (-((d : ℝ) + 1) / 2) : ℝ) : ℂ) •
        (fun x : Rd d => (κ (t⁻¹ • x) : ℂ))) ζ =
      (((t ^ (-((d : ℝ) + 1) / 2) : ℝ) : ℂ) •
        𝓕 (fun x : Rd d => (κ (t⁻¹ • x) : ℂ)) ζ) at h
    have heq : (((t ^ (-((d : ℝ) + 1) / 2) : ℝ) : ℂ) •
        (fun x : Rd d => (κ (t⁻¹ • x) : ℂ))) =
        (fun x : Rd d => ((t ^ (-((d : ℝ) + 1) / 2) : ℝ) : ℂ) *
          (κ (t⁻¹ • x) : ℂ)) := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
    rw [heq] at h
    simpa only [smul_eq_mul] using h
  rw [hs, fourier_comp_inv_smul (fun x : Rd d => (κ x : ℂ)) ht ζ]
  simp only [Complex.real_smul, Complex.ofReal_mul, mul_assoc]

/-- The squared Fourier modulus of a scaled kernel. -/
private theorem norm_fourier_scaleKernel_sq {κ : Rd d → ℝ} {t : ℝ}
    (ht : 0 < t) (ζ : Rd d) :
    ‖𝓕 (fun x : Rd d => (HigherDimLFPP.scaleKernel κ t x : ℂ)) ζ‖ ^ 2 =
      t ^ ((d : ℝ) - 1) * ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • ζ)‖ ^ 2 := by
  have ha : t ^ (-((d : ℝ) + 1) / 2) * t ^ d = t ^ (((d : ℝ) - 1) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht]
    congr 1
    ring
  have hb : (t ^ (((d : ℝ) - 1) / 2)) ^ 2 = t ^ ((d : ℝ) - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 1
    ring
  rw [fourier_scaleKernel ht, ha, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht _), mul_pow, hb]

/-- Integration against a positive density is an ordinary weighted integral. -/
private theorem scaleConv_posM {κ f : Rd d → ℝ} (hf : Measurable f) (t : ℝ) (y : Rd d) :
    HigherDimLFPP.scaleConv κ t (posM f) y =
      ∫ z, max (f z) 0 * HigherDimLFPP.scaleKernel κ t (z - y) := by
  rw [HigherDimLFPP.scaleConv, posM,
    integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) _]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  change (ENNReal.ofReal (f z)).toReal • HigherDimLFPP.scaleKernel κ t (z - y) =
    max (f z) 0 * HigherDimLFPP.scaleKernel κ t (z - y)
  rw [ENNReal.toReal_ofReal', smul_eq_mul]

/-- The signed density `φ⁺-φ⁻` recovers the usual kernel pairing at one scale. -/
private theorem scaleConv_posM_sub (φ : TestRd d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (t : ℝ) (y : Rd d) :
    HigherDimLFPP.scaleConv κ t (posM fun z => φ z) y -
      HigherDimLFPP.scaleConv κ t (posM fun z => -φ z) y =
      ∫ z, φ z * HigherDimLFPP.scaleKernel κ t (z - y) := by
  have hp : Integrable (fun z => max (φ z) 0 * HigherDimLFPP.scaleKernel κ t (z - y)) := by
    have hc : Continuous (fun z : Rd d => max (φ z) 0 *
        HigherDimLFPP.scaleKernel κ t (z - y)) :=
      (φ.continuous.max continuous_const).mul
        ((HigherDimLFPP.continuous_scaleKernel hκ t).comp (continuous_id.sub continuous_const))
    have hs : HasCompactSupport (fun z : Rd d => max (φ z) 0) :=
      φ.hasCompactSupport.comp_left (g := fun a : ℝ => max a 0) (by norm_num)
    exact hc.integrable_of_hasCompactSupport hs.mul_right
  have hn : Integrable (fun z => max (-φ z) 0 * HigherDimLFPP.scaleKernel κ t (z - y)) := by
    have hc : Continuous (fun z : Rd d => max (-φ z) 0 *
        HigherDimLFPP.scaleKernel κ t (z - y)) :=
      (φ.continuous.neg.max continuous_const).mul
        ((HigherDimLFPP.continuous_scaleKernel hκ t).comp (continuous_id.sub continuous_const))
    have hs : HasCompactSupport (fun z : Rd d => max (-φ z) 0) :=
      φ.hasCompactSupport.comp_left (g := fun a : ℝ => max (-a) 0) (by norm_num)
    exact hc.integrable_of_hasCompactSupport hs.mul_right
  rw [scaleConv_posM (f := fun z => φ z) φ.continuous.measurable,
    scaleConv_posM (f := fun z => -φ z) φ.continuous.measurable.neg,
    ← integral_sub hp hn]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  change max (φ z) 0 * HigherDimLFPP.scaleKernel κ t (z - y) -
      max (-φ z) 0 * HigherDimLFPP.scaleKernel κ t (z - y) =
      φ z * HigherDimLFPP.scaleKernel κ t (z - y)
  rw [show max (φ z) 0 * HigherDimLFPP.scaleKernel κ t (z - y) -
      max (-φ z) 0 * HigherDimLFPP.scaleKernel κ t (z - y) =
      (max (φ z) 0 - max (-φ z) 0) * HigherDimLFPP.scaleKernel κ t (z - y) by ring,
    max_zero_sub_max_neg_zero_eq_self]

/-- The signed scale pairing is the Schwartz convolution with the scaled kernel. -/
private theorem scaleConv_posM_sub_eq_convolution (φ : TestRd d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {t : ℝ} (ht : 0 < t) (y : Rd d) :
    ((HigherDimLFPP.scaleConv κ t (posM fun z => φ z) y -
      HigherDimLFPP.scaleConv κ t (posM fun z => -φ z) y : ℝ) : ℂ) =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
        (testComplexSchwartz φ) (scaleKernelComplexSchwartz hκ ht) y := by
  rw [scaleConv_posM_sub φ hκ t y, SchwartzMap.convolution_apply]
  rw [← integral_complex_ofReal]
  unfold MeasureTheory.convolution
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  have heven : HigherDimLFPP.scaleKernel κ t (y - z) =
      HigherDimLFPP.scaleKernel κ t (z - y) := by
    unfold HigherDimLFPP.scaleKernel
    rw [show y - z = -(z - y) by abel, smul_neg, hκ.neg]
  simp only [testComplexSchwartz_apply, scaleKernelComplexSchwartz_apply,
    ContinuousLinearMap.mul_apply', Complex.ofReal_mul, heven]

/-- The scale covariance density has the expected spectral form. -/
private theorem scalePair_test_eq_fourier (φ : TestRd d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {t : ℝ} (ht : 0 < t) :
    HigherDimLFPP.scalePair κ t (posM fun z => φ z) (posM fun z => -φ z)
      (posM fun z => φ z) (posM fun z => -φ z) =
      ∫ ζ : Rd d, t ^ ((d : ℝ) - 1) *
        ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • ζ)‖ ^ 2 *
        ‖𝓕 (fun x : Rd d => (φ x : ℂ)) ζ‖ ^ 2 := by
  obtain ⟨M, D, hf⟩ := exists_isBddSupp_testOn φ
  haveI : IsFiniteMeasure (posM fun z => φ z) := isFiniteMeasure_posM hf
  haveI : IsFiniteMeasure (posM fun z => -φ z) := isFiniteMeasure_posM hf.neg
  rw [← HigherDimLFPP.integral_scaleConv_sub_mul hκ ht]
  have he (y : Rd d) :
      (HigherDimLFPP.scaleConv κ t (posM fun z => φ z) y -
        HigherDimLFPP.scaleConv κ t (posM fun z => -φ z) y) *
      (HigherDimLFPP.scaleConv κ t (posM fun z => φ z) y -
        HigherDimLFPP.scaleConv κ t (posM fun z => -φ z) y) =
      ‖SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
        (testComplexSchwartz φ) (scaleKernelComplexSchwartz hκ ht) y‖ ^ 2 := by
    rw [← pow_two, ← scaleConv_posM_sub_eq_convolution φ hκ ht y, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  simp_rw [he]
  rw [integral_norm_sq_schwartzConvolution]
  refine integral_congr_ae (ae_of_all _ fun ζ => ?_)
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  have hφ : (testComplexSchwartz φ : Rd d → ℂ) = fun x => (φ x : ℂ) := rfl
  have hscale : (scaleKernelComplexSchwartz hκ ht : Rd d → ℂ) =
      fun x => (HigherDimLFPP.scaleKernel κ t x : ℂ) := rfl
  rw [hφ, hscale]
  change ‖𝓕 (fun x : Rd d => (φ x : ℂ)) ζ‖ ^ 2 *
      ‖𝓕 (fun x : Rd d => (HigherDimLFPP.scaleKernel κ t x : ℂ)) ζ‖ ^ 2 =
      t ^ ((d : ℝ) - 1) * ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • ζ)‖ ^ 2 *
        ‖𝓕 (fun x : Rd d => (φ x : ℂ)) ζ‖ ^ 2
  rw [norm_fourier_scaleKernel_sq ht]
  ring

/-- Logarithmic covariance as an integral of spectral scale densities. -/
private theorem logCovRd_eq_integral_scale_fourier (hd : 1 ≤ d) (φ : TestRd0 d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    logCovRd φ.1 φ.1 =
      ∫ t in Set.Ioi (0 : ℝ), ∫ ζ : Rd d, t ^ ((d : ℝ) - 1) *
        ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • ζ)‖ ^ 2 *
        ‖𝓕 (fun x : Rd d => (φ.1 x : ℂ)) ζ‖ ^ 2 := by
  haveI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  obtain ⟨M, D, hf⟩ := exists_isBddSupp_testOn φ.1
  haveI : IsFiniteMeasure (posM fun z => φ.1 z) := isFiniteMeasure_posM hf
  haveI : IsFiniteMeasure (posM fun z => -φ.1 z) := isFiniteMeasure_posM hf.neg
  have hmass := posM_real_univ_eq hf φ.2
  have hlog := logPairable_posM hf hf
  obtain ⟨hp, _, hcov⟩ := HigherDimLFPP.scaleCov_eq_logCov hκ hmass hmass hlog
  calc
    logCovRd φ.1 φ.1 = logCovF φ.1 φ.1 := logCovRd_eq_logCovF hf hf
    _ = HigherDimLFPP.logCov (posM fun z => φ.1 z) (posM fun z => -φ.1 z)
        (posM fun z => φ.1 z) (posM fun z => -φ.1 z) := (logCov_posM hf hf).symm
    _ = HigherDimLFPP.scaleCov κ (Set.Ioi 0) (posM fun z => φ.1 z)
        (posM fun z => -φ.1 z) (posM fun z => φ.1 z) (posM fun z => -φ.1 z) := hcov.symm
    _ = ∫ t in Set.Ioi (0 : ℝ), HigherDimLFPP.scalePair κ t (posM fun z => φ.1 z)
        (posM fun z => -φ.1 z) (posM fun z => φ.1 z) (posM fun z => -φ.1 z) :=
      HigherDimLFPP.scaleCov_eq_integral hκ measurableSet_Ioi (fun _ h => h) hp hp
    _ = ∫ t in Set.Ioi (0 : ℝ), ∫ ζ : Rd d, t ^ ((d : ℝ) - 1) *
        ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • ζ)‖ ^ 2 *
        ‖𝓕 (fun x : Rd d => (φ.1 x : ℂ)) ζ‖ ^ 2 := by
      exact setIntegral_congr_fun measurableSet_Ioi fun t ht =>
        scalePair_test_eq_fourier φ.1 hκ ht

/-- Radiality of an LFPP kernel passes to its Fourier transform. -/
private theorem fourier_kernel_radial {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {v w : Rd d} (hvw : ‖v‖ = ‖w‖) :
    𝓕 (fun x : Rd d => (κ x : ℂ)) v =
      𝓕 (fun x : Rd d => (κ x : ℂ)) w := by
  let R : Rd d ≃ₗᵢ[ℝ] Rd d := Submodule.reflection (ℝ ∙ (v - w))ᗮ
  have hR : R v = w := Submodule.reflection_sub hvw
  have hκR : ((fun x : Rd d => (κ x : ℂ)) ∘ R) =
      (fun x : Rd d => (κ x : ℂ)) := by
    funext x
    exact congrArg Complex.ofReal (hκ.radial (R x) x (R.norm_map x))
  have h := Real.fourier_comp_linearIsometry R (fun x : Rd d => (κ x : ℂ)) v
  rw [hκR, hR] at h
  exact h

/-- The unscaled admissible kernel, considered as a Schwartz function. -/
private def kernelComplexSchwartz {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) : 𝓢(Rd d, ℂ) :=
  (hκ.hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hκ.contDiff)

private theorem kernelComplexSchwartz_apply {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (x : Rd d) :
    kernelComplexSchwartz hκ x = (κ x : ℂ) := rfl

/-- Normalization and nonnegativity force a strictly positive mass. -/
private theorem integral_kernel_pos {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) : 0 < ∫ x, κ x := by
  have hnonzero : ∃ x, κ x ≠ 0 := by
    by_contra h
    push Not at h
    have hz : ∫ x, κ x ^ 2 = 0 := by simp [h]
    linarith [hκ.integral_sq]
  obtain ⟨x, hx⟩ := hnonzero
  exact integral_pos_of_integrable_nonneg_nonzero hκ.continuous hκ.integrable hκ.nonneg hx

private theorem fourier_kernel_zero_pos {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    0 < ‖𝓕 (fun x : Rd d => (κ x : ℂ)) 0‖ := by
  have h := integral_kernel_pos hκ
  rw [Real.fourier_eq]
  simp only [inner_zero_right, neg_zero]
  simp
  rw [integral_complex_ofReal]
  exact_mod_cast h.ne'

/-- Restriction of the kernel Fourier transform to a unit radial line is Schwartz. -/
private def kernelFourierLine {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (e : Rd d) (he : ‖e‖ = 1) :
    𝓢(ℝ, ℂ) := by
  let L : ℝ →L[ℝ] Rd d := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) e
  have hL : ∀ t : ℝ, L t = t • e := fun t => by simp [L]
  have hi : Isometry (fun t : ℝ => t • e) := Isometry.of_dist_eq (by
    intro a b
    rw [dist_eq_norm, dist_eq_norm, ← sub_smul, norm_smul, he, mul_one]
    )
  have hLa : AntilipschitzWith 1 L := by
    simpa only [show (L : ℝ → Rd d) = (fun t : ℝ => t • e) from funext hL]
      using hi.antilipschitzWith
  exact SchwartzMap.compCLMOfAntilipschitz ℂ L.hasTemperateGrowth
    hLa (𝓕 (kernelComplexSchwartz hκ))

private theorem kernelFourierLine_apply {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (e : Rd d) (he : ‖e‖ = 1) (t : ℝ) :
    kernelFourierLine hκ e he t = 𝓕 (fun x : Rd d => (κ x : ℂ)) (t • e) := by
  change 𝓕 (kernelComplexSchwartz hκ) (t • e) = _
  rw [SchwartzMap.fourier_coe]
  rfl

/-- The spectral radial mass is finite in every positive dimension. -/
private theorem kernel_radial_integrable (hd : 1 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (e : Rd d) (he : ‖e‖ = 1) :
    IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - 1) *
      ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • e)‖ ^ 2) (Set.Ioi 0) := by
  let f := kernelFourierLine hκ e he
  have hf : IntegrableOn (fun t : ℝ => ‖t‖ ^ (d - 1) * ‖f t‖)
      (Set.Ioi 0) := (f.integrable_pow_mul volume (d - 1)).integrableOn
  have hM : ∀ t, ‖f t‖ ≤ SchwartzMap.seminorm ℂ 0 0 f :=
    SchwartzMap.norm_le_seminorm ℂ f
  have hfun : (fun t : ℝ => t ^ ((d : ℝ) - 1) *
      ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • e)‖ ^ 2) =
      fun t => t ^ ((d : ℝ) - 1) * ‖f t‖ ^ 2 := by
    funext t
    rw [kernelFourierLine_apply hκ e he t]
  have hbound : ∀ t ∈ Set.Ioi (0 : ℝ),
      ‖t ^ ((d : ℝ) - 1) * ‖f t‖ ^ 2‖ ≤
      SchwartzMap.seminorm ℂ 0 0 f * (‖t‖ ^ (d - 1) * ‖f t‖) := by
    intro t ht
    have ht0 : 0 < t := ht
    have hp : t ^ ((d : ℝ) - 1) = ‖t‖ ^ (d - 1) := by
      have hc : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
        norm_num [Nat.cast_sub hd]
      rw [← hc, Real.rpow_natCast, Real.norm_eq_abs, abs_of_pos ht0]
    rw [hp, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hfn : 0 ≤ ‖f t‖ := norm_nonneg _
    calc
      ‖t‖ ^ (d - 1) * ‖f t‖ ^ 2 = ‖f t‖ * (‖t‖ ^ (d - 1) * ‖f t‖) := by ring
      _ ≤ SchwartzMap.seminorm ℂ 0 0 f * (‖t‖ ^ (d - 1) * ‖f t‖) :=
        mul_le_mul_of_nonneg_right (hM t) (by positivity)
  rw [hfun]
  apply Integrable.mono' (hf.const_mul (SchwartzMap.seminorm ℂ 0 0 f))
  · fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hbound t ht

/-- The radial spectral mass is strictly positive. -/
private theorem kernel_radial_integral_pos (hd : 1 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (e : Rd d) (he : ‖e‖ = 1) :
    0 < ∫ t in Set.Ioi (0 : ℝ), t ^ ((d : ℝ) - 1) *
      ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • e)‖ ^ 2 := by
  let f := kernelFourierLine hκ e he
  have h0 : 0 < ‖f 0‖ := by
    rw [kernelFourierLine_apply hκ e he 0, zero_smul]
    exact fourier_kernel_zero_pos hκ
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < ‖f t‖ :=
    (f.continuous.norm.tendsto 0).eventually (isOpen_Ioi.mem_nhds h0)
  have hev' : ∀ᶠ t in 𝓝[Set.Ioi 0] (0 : ℝ), 0 < ‖f t‖ :=
    Filter.Eventually.filter_mono inf_le_left hev
  obtain ⟨t, ht, hft⟩ := (eventually_mem_nhdsWithin.and hev').exists
  let U : Set ℝ := Set.Ioi 0 ∩ {u | 0 < ‖f u‖}
  have hU : IsOpen U := isOpen_Ioi.inter (isOpen_Ioi.preimage f.continuous.norm)
  have hUp : 0 < volume U := hU.measure_pos volume ⟨t, ht, hft⟩
  have hUsub : U ⊆ Function.support (fun t : ℝ =>
      t ^ ((d : ℝ) - 1) * ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • e)‖ ^ 2) ∩
      Set.Ioi 0 := by
    intro u hu
    refine ⟨?_, hu.1⟩
    change u ^ ((d : ℝ) - 1) *
      ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (u • e)‖ ^ 2 ≠ 0
    rw [← kernelFourierLine_apply hκ e he u]
    exact ne_of_gt (mul_pos (Real.rpow_pos_of_pos hu.1 _) (sq_pos_of_pos hu.2))
  apply (setIntegral_pos_iff_support_of_nonneg_ae ?_ (kernel_radial_integrable hd hκ e he)).2
  · exact lt_of_lt_of_le hUp (measure_mono hUsub)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt hu) _) (sq_nonneg _)

/-- The Fourier scale density is integrable in frequency at each positive scale. -/
private theorem spectral_slice_integrable (φ : TestRd d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun ζ : Rd d => t ^ ((d : ℝ) - 1) *
      ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • ζ)‖ ^ 2 *
      ‖𝓕 (fun x : Rd d => (φ x : ℂ)) ζ‖ ^ 2) := by
  let q : 𝓢(Rd d, ℂ) := SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ)
    (𝓕 (scaleKernelComplexSchwartz hκ ht)) (𝓕 (testComplexSchwartz φ))
  have hq : Integrable (fun ζ : Rd d => ‖q ζ‖ ^ 2) :=
    (q.memLp 2 volume).integrable_norm_pow (by norm_num)
  convert hq using 1
  ext ζ
  dsimp [q]
  rw [norm_mul, mul_pow, SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  have hs : (scaleKernelComplexSchwartz hκ ht : Rd d → ℂ) =
      fun x => (HigherDimLFPP.scaleKernel κ t x : ℂ) := rfl
  have hφ : (testComplexSchwartz φ : Rd d → ℂ) = fun x => (φ x : ℂ) := rfl
  rw [hs, hφ, norm_fourier_scaleKernel_sq ht]

/-- The nonnegative spectral density is integrable on scale–frequency space. -/
private theorem spectral_product_integrable (hd : 1 ≤ d) (φ : TestRd0 d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    Integrable (fun p : ℝ × Rd d => p.1 ^ ((d : ℝ) - 1) *
      ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (p.1 • p.2)‖ ^ 2 *
      ‖𝓕 (fun x : Rd d => (φ.1 x : ℂ)) p.2‖ ^ 2)
      ((volume.restrict (Set.Ioi 0)).prod volume) := by
  haveI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  let kF : 𝓢(Rd d, ℂ) := 𝓕 (kernelComplexSchwartz hκ)
  let pF : 𝓢(Rd d, ℂ) := 𝓕 (testComplexSchwartz φ.1)
  let W : ℝ × Rd d → ℝ := fun p => p.1 ^ ((d : ℝ) - 1) *
    ‖kF (p.1 • p.2)‖ ^ 2 * ‖pF p.2‖ ^ 2
  have hW : W = (fun p : ℝ × Rd d => p.1 ^ ((d : ℝ) - 1) *
      ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (p.1 • p.2)‖ ^ 2 *
      ‖𝓕 (fun x : Rd d => (φ.1 x : ℂ)) p.2‖ ^ 2) := by
    funext p
    simp only [W, kF, pF, SchwartzMap.fourier_coe]
    rfl
  rw [← hW]
  have hWmeas : AEStronglyMeasurable W
      ((volume.restrict (Set.Ioi 0)).prod volume) := by
    have : Measurable W := by dsimp [W]; fun_prop
    exact this.aestronglyMeasurable
  apply (integrable_prod_iff hWmeas).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hs := spectral_slice_integrable φ.1 hκ ht
    convert hs using 1
    ext ζ
    exact congrFun hW (t, ζ) |>.symm
  · obtain ⟨M, D, hf⟩ := exists_isBddSupp_testOn φ.1
    haveI : IsFiniteMeasure (posM fun z => φ.1 z) := isFiniteMeasure_posM hf
    haveI : IsFiniteMeasure (posM fun z => -φ.1 z) := isFiniteMeasure_posM hf.neg
    have hmass := posM_real_univ_eq hf φ.2
    have hlog := logPairable_posM hf hf
    obtain ⟨hp, _, _⟩ := HigherDimLFPP.scaleCov_eq_logCov hκ hmass hmass hlog
    have hpair := HigherDimLFPP.integrableOn_scalePair hκ measurableSet_Ioi
      (fun _ h => h) hp hp
    apply hpair.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hw : ∀ ζ : Rd d, 0 ≤ W (t, ζ) := by
      intro ζ
      dsimp [W]
      have ht0 : 0 < t := ht
      positivity
    simp_rw [show ∀ ζ : Rd d, ‖W (t, ζ)‖ = W (t, ζ) from
      fun ζ => Real.norm_eq_abs _ |>.trans (abs_of_nonneg (hw ζ))]
    change HigherDimLFPP.scalePair κ t (posM fun z => φ.1 z)
      (posM fun z => -φ.1 z) (posM fun z => φ.1 z)
      (posM fun z => -φ.1 z) = ∫ y, W (t, y)
    rw [scalePair_test_eq_fourier φ.1 hκ ht]
    exact integral_congr_ae (ae_of_all _ (fun ζ => (congrFun hW (t, ζ)).symm))

/-- Fubini exchanges the frequency and scale integrals in logarithmic energy. -/
private theorem logCovRd_eq_integral_swapped (hd : 1 ≤ d) (φ : TestRd0 d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    logCovRd φ.1 φ.1 =
      ∫ ζ : Rd d, ∫ t in Set.Ioi (0 : ℝ), t ^ ((d : ℝ) - 1) *
        ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • ζ)‖ ^ 2 *
        ‖𝓕 (fun x : Rd d => (φ.1 x : ℂ)) ζ‖ ^ 2 := by
  rw [logCovRd_eq_integral_scale_fourier hd φ hκ]
  exact integral_integral_swap (spectral_product_integrable hd φ hκ)

/-- A radial spectral density scales as `‖ζ‖⁻ᵈ` after integrating over scales. -/
private theorem integral_kernel_scale (_hd : 1 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (e : Rd d) (he : ‖e‖ = 1)
    (ζ : Rd d) (hζ : ζ ≠ 0) :
    (∫ t in Set.Ioi (0 : ℝ), t ^ ((d : ℝ) - 1) *
      ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • ζ)‖ ^ 2) =
      ‖ζ‖ ^ (-(d : ℝ)) *
        (∫ s in Set.Ioi (0 : ℝ), s ^ ((d : ℝ) - 1) *
          ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (s • e)‖ ^ 2) := by
  let r : ℝ := ‖ζ‖
  have hr : 0 < r := norm_pos_iff.mpr hζ
  let g : ℝ → ℝ := fun s => s ^ ((d : ℝ) - 1) *
    ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (s • e)‖ ^ 2
  have hp : ∀ t ∈ Set.Ioi (0 : ℝ),
      t ^ ((d : ℝ) - 1) * ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • ζ)‖ ^ 2 =
        r ^ (-((d : ℝ) - 1)) * g (r * t) := by
    intro t ht
    have ht0 : 0 < t := ht
    have hnorm : ‖t • ζ‖ = ‖(r * t) • e‖ := by
      rw [norm_smul, norm_smul, he, mul_one, Real.norm_eq_abs,
        abs_of_pos ht0, Real.norm_eq_abs, abs_of_pos (mul_pos hr ht0)]
      dsimp [r]
      ring
    rw [fourier_kernel_radial hκ hnorm]
    dsimp [g]
    rw [Real.mul_rpow hr.le ht0.le, Real.rpow_neg (le_of_lt hr)]
    have hne : r ^ ((d : ℝ) - 1) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
    field_simp
  calc
    (∫ t in Set.Ioi (0 : ℝ), t ^ ((d : ℝ) - 1) *
      ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • ζ)‖ ^ 2) =
        ∫ t in Set.Ioi (0 : ℝ), r ^ (-((d : ℝ) - 1)) * g (r * t) :=
      setIntegral_congr_fun measurableSet_Ioi hp
    _ = r ^ (-((d : ℝ) - 1)) * (∫ t in Set.Ioi (0 : ℝ), g (r * t)) := by
      rw [integral_const_mul]
    _ = r ^ (-(d : ℝ)) * ∫ s in Set.Ioi (0 : ℝ), g s := by
      rw [integral_comp_mul_left_Ioi g 0 hr]
      simp only [mul_zero, smul_eq_mul]
      rw [← mul_assoc, ← Real.rpow_neg_one, ← Real.rpow_add hr]
      congr 1
      ring_nf
    _ = _ := rfl

/-- Fourier representation of the logarithmic covariance on mean-zero test functions. -/
theorem logCovRd_eq_fourier (hd : 1 ≤ d) :
    ∃ κd : ℝ, 0 < κd ∧ ∀ φ : TestRd0 d,
      logCovRd φ.1 φ.1 = κd * ∫ ζ : Rd d, ‖ζ‖ ^ (-(d : ℝ)) *
        ‖𝓕 (fun x : Rd d => (φ.1 x : ℂ)) ζ‖ ^ 2 := by
  haveI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  obtain ⟨κ, hκ⟩ := HigherDimLFPP.exists_isLFPPKernel d
  obtain ⟨e, he⟩ := exists_norm_eq (Rd d) zero_le_one
  let κd : ℝ := ∫ s in Set.Ioi (0 : ℝ), s ^ ((d : ℝ) - 1) *
    ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (s • e)‖ ^ 2
  refine ⟨κd, kernel_radial_integral_pos hd hκ e he, ?_⟩
  intro φ
  rw [logCovRd_eq_integral_swapped hd φ hκ]
  calc
    (∫ ζ : Rd d, ∫ t in Set.Ioi (0 : ℝ), t ^ ((d : ℝ) - 1) *
        ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • ζ)‖ ^ 2 *
        ‖𝓕 (fun x : Rd d => (φ.1 x : ℂ)) ζ‖ ^ 2) =
      ∫ ζ : Rd d, κd * (‖ζ‖ ^ (-(d : ℝ)) *
        ‖𝓕 (fun x : Rd d => (φ.1 x : ℂ)) ζ‖ ^ 2) := by
      apply integral_congr_ae
      filter_upwards [Measure.ae_ne volume (0 : Rd d)] with ζ hζ
      calc
        (∫ t in Set.Ioi (0 : ℝ), t ^ ((d : ℝ) - 1) *
            ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • ζ)‖ ^ 2 *
            ‖𝓕 (fun x : Rd d => (φ.1 x : ℂ)) ζ‖ ^ 2) =
          (∫ t in Set.Ioi (0 : ℝ), t ^ ((d : ℝ) - 1) *
            ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • ζ)‖ ^ 2) *
            ‖𝓕 (fun x : Rd d => (φ.1 x : ℂ)) ζ‖ ^ 2 := integral_mul_const _ _
        _ = κd * (‖ζ‖ ^ (-(d : ℝ)) *
            ‖𝓕 (fun x : Rd d => (φ.1 x : ℂ)) ζ‖ ^ 2) := by
          rw [integral_kernel_scale hd hκ e he ζ hζ]
          dsimp [κd]
          ring
    _ = κd * ∫ ζ : Rd d, ‖ζ‖ ^ (-(d : ℝ)) *
        ‖𝓕 (fun x : Rd d => (φ.1 x : ℂ)) ζ‖ ^ 2 := integral_const_mul κd _

/-- The singular spectral energy of a mean-zero test function is genuinely integrable. -/
theorem integrable_test_fourier_weight (hd : 1 ≤ d) (φ : TestRd0 d) :
    Integrable (fun ζ : Rd d => ‖ζ‖ ^ (-(d : ℝ)) *
      ‖𝓕 (fun x : Rd d => (φ.1 x : ℂ)) ζ‖ ^ 2) := by
  haveI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  obtain ⟨κ, hκ⟩ := HigherDimLFPP.exists_isLFPPKernel d
  obtain ⟨e, he⟩ := exists_norm_eq (Rd d) zero_le_one
  let C : ℝ := ∫ s in Set.Ioi (0 : ℝ), s ^ ((d : ℝ) - 1) *
    ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (s • e)‖ ^ 2
  have hC : 0 < C := kernel_radial_integral_pos hd hκ e he
  have hprod := spectral_product_integrable hd φ hκ
  have houter : Integrable (fun ζ : Rd d => ∫ t in Set.Ioi (0 : ℝ),
      t ^ ((d : ℝ) - 1) *
        ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • ζ)‖ ^ 2 *
        ‖𝓕 (fun x : Rd d => (φ.1 x : ℂ)) ζ‖ ^ 2) := hprod.integral_prod_right
  have heq : (fun ζ : Rd d => ∫ t in Set.Ioi (0 : ℝ),
      t ^ ((d : ℝ) - 1) *
        ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • ζ)‖ ^ 2 *
        ‖𝓕 (fun x : Rd d => (φ.1 x : ℂ)) ζ‖ ^ 2) =ᵐ[volume]
      (fun ζ => C * (‖ζ‖ ^ (-(d : ℝ)) *
        ‖𝓕 (fun x : Rd d => (φ.1 x : ℂ)) ζ‖ ^ 2)) := by
    filter_upwards [Measure.ae_ne volume (0 : Rd d)] with ζ hζ
    calc
      (∫ t in Set.Ioi (0 : ℝ), t ^ ((d : ℝ) - 1) *
          ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • ζ)‖ ^ 2 *
          ‖𝓕 (fun x : Rd d => (φ.1 x : ℂ)) ζ‖ ^ 2) =
        (∫ t in Set.Ioi (0 : ℝ), t ^ ((d : ℝ) - 1) *
          ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • ζ)‖ ^ 2) *
          ‖𝓕 (fun x : Rd d => (φ.1 x : ℂ)) ζ‖ ^ 2 := integral_mul_const _ _
      _ = C * (‖ζ‖ ^ (-(d : ℝ)) *
          ‖𝓕 (fun x : Rd d => (φ.1 x : ℂ)) ζ‖ ^ 2) := by
        rw [integral_kernel_scale hd hκ e he ζ hζ]
        dsimp [C]
        ring
  have hweighted : Integrable (fun ζ : Rd d => C * (‖ζ‖ ^ (-(d : ℝ)) *
      ‖𝓕 (fun x : Rd d => (φ.1 x : ℂ)) ζ‖ ^ 2)) := houter.congr heq
  convert hweighted.const_mul C⁻¹ using 1
  ext ζ
  rw [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul]

/-- The radial Fourier constant is independent of the normalized LFPP kernel. -/
theorem kernel_radial_constant_independent (hd : 1 ≤ d)
    {κ τ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hτ : HigherDimLFPP.IsLFPPKernel τ) (e : Rd d) (he : ‖e‖ = 1) :
    (∫ s in Set.Ioi (0 : ℝ), s ^ ((d : ℝ) - 1) *
      ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (s • e)‖ ^ 2) =
    (∫ s in Set.Ioi (0 : ℝ), s ^ ((d : ℝ) - 1) *
      ‖𝓕 (fun x : Rd d => (τ x : ℂ)) (s • e)‖ ^ 2) := by
  haveI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  let V : ℝ := (d : ℝ) * (volume : Measure (Rd d)).real (Metric.ball 0 1)
  have hV : 0 < V := by
    dsimp [V]
    apply mul_pos (Nat.cast_pos.mpr (by omega))
    rw [Measure.real_def]
    exact ENNReal.toReal_pos
      (Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr zero_lt_one)).ne'
      (by finiteness)
  have hmass {f : Rd d → ℝ} (hf : HigherDimLFPP.IsLFPPKernel f) :
      V * (∫ s in Set.Ioi (0 : ℝ), s ^ ((d : ℝ) - 1) *
        ‖𝓕 (fun x : Rd d => (f x : ℂ)) (s • e)‖ ^ 2) = 1 := by
    have hrad (ζ : Rd d) :
        ‖𝓕 (fun x : Rd d => (f x : ℂ)) ζ‖ ^ 2 =
        ‖𝓕 (fun x : Rd d => (f x : ℂ)) (‖ζ‖ • e)‖ ^ 2 := by
      have hn : ‖ζ‖ = ‖‖ζ‖ • e‖ := by
        simp [norm_smul, he]
      rw [fourier_kernel_radial hf hn]
    have hpolar := integral_fun_norm_addHaar (volume : Measure (Rd d))
      (fun r : ℝ => ‖𝓕 (fun x : Rd d => (f x : ℂ)) (r • e)‖ ^ 2)
    simp only [smul_eq_mul, finrank_rd] at hpolar
    have hexp : (∫ s in Set.Ioi (0 : ℝ), s ^ (d - 1) *
        ‖𝓕 (fun x : Rd d => (f x : ℂ)) (s • e)‖ ^ 2) =
        (∫ s in Set.Ioi (0 : ℝ), s ^ ((d : ℝ) - 1) *
        ‖𝓕 (fun x : Rd d => (f x : ℂ)) (s • e)‖ ^ 2) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      change s ^ (d - 1) * ‖𝓕 (fun x : Rd d => (f x : ℂ)) (s • e)‖ ^ 2 =
        s ^ ((d : ℝ) - 1) * ‖𝓕 (fun x : Rd d => (f x : ℂ)) (s • e)‖ ^ 2
      congr 1
      rw [← Real.rpow_natCast]
      congr 1
      norm_num [Nat.cast_sub hd]
    rw [hexp] at hpolar
    have hleft : (∫ ζ : Rd d,
        ‖𝓕 (fun x : Rd d => (f x : ℂ)) ζ‖ ^ 2) = 1 := by
      have hp := SchwartzMap.integral_norm_sq_fourier (kernelComplexSchwartz hf)
      rw [SchwartzMap.fourier_coe] at hp
      have hco : (kernelComplexSchwartz hf : Rd d → ℂ) = fun x => (f x : ℂ) := rfl
      rw [hco] at hp
      rw [hp]
      convert hf.integral_sq using 1
      apply integral_congr_ae
      exact ae_of_all _ fun x => by simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [show (∫ ζ : Rd d,
        ‖𝓕 (fun x : Rd d => (f x : ℂ)) ζ‖ ^ 2) =
        ∫ ζ : Rd d, ‖𝓕 (fun x : Rd d => (f x : ℂ)) (‖ζ‖ • e)‖ ^ 2 from
      integral_congr_ae (ae_of_all _ hrad), hpolar] at hleft
    simpa only [V, nsmul_eq_mul, smul_eq_mul, mul_assoc] using hleft
  have hk := hmass hκ
  have hl := hmass hτ
  exact mul_left_cancel₀ hV.ne' (hk.trans hl.symm)

end HigherDimLQGMetric
