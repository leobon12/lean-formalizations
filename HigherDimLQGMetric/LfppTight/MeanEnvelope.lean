import HigherDimLQGMetric.LfppTight.ConvolutionDensity
import HigherDimLQGMetric.ConvField.MeanTest

/-! A positive convolution measure dominates every compact sphere-mean test approximation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_meanTrunc_abs_le_conv {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (w : Rd d) :
    |l2b_meanTruncTest hd hκ hε n w| ≤
      ∫ u : Rd d, |convKernelEps κ ε (w - u)| ∂(unitSphereProb d) := by
  let μ : Measure (Rd d) := unitSphereProb d
  let f : Rd d → ℝ := fun u => convTrunc κ ε u n w
  let g : Rd d → ℝ := fun u => |convKernelEps κ ε (w - u)|
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_unitSphereProb (by omega : 1 ≤ d)
  obtain ⟨B, hB, hbound⟩ := convKernelEps_bounded hd hκ hε
  have hfcont : Continuous f := by
    have h := (continuous_eval_const w).comp
      ((l2b_continuous_convTrunc_exp hd hκ n).comp
        ((continuous_const : Continuous fun _ : Rd d => Real.log ε).prodMk
          continuous_id))
    convert h using 1
    funext u
    simp only [Function.comp_apply, Real.exp_log hε, id_eq, f]
  have hgcont : Continuous g := by
    have hkcont : Continuous (convKernelEps κ ε) :=
      continuous_const.mul
        ((convKernel_contDiff (by omega : 0 < d) hκ).continuous.comp
          (continuous_const_smul _))
    exact (hkcont.comp (continuous_const.sub continuous_id)).abs
  have hgi : Integrable g μ := by
    apply Integrable.of_bound hgcont.aestronglyMeasurable B
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    exact hbound _
  have hpt (u : Rd d) : |f u| ≤ g u := by
    dsimp [f, g]
    rw [l2b_convTrunc_apply hd hκ, abs_mul]
    have hcut := radialProfile_nonneg (((n : ℝ) + 1)⁻¹ • (w - u))
    have hcut1 := radialProfile_le_one (((n : ℝ) + 1)⁻¹ • (w - u))
    rw [abs_of_nonneg hcut]
    have heq : |convKernelEps κ ε (u - w)| = |convKernelEps κ ε (w - u)| := by
      apply congrArg abs
      exact l2b_convKernelEps_radial ε (norm_sub_rev u w)
    rw [← heq]
    exact mul_le_of_le_one_right (abs_nonneg _) hcut1
  have hfi : Integrable f μ := by
    apply hgi.mono' hfcont.aestronglyMeasurable
    exact ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]
      exact hpt u
  rw [l2b_meanTruncTest_apply hd hκ hε n w]
  calc
    |∫ u, f u ∂μ| ≤ ∫ u, |f u| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (f := f)
    _ ≤ ∫ u, g u ∂μ := integral_mono hfi.abs hgi hpt

theorem l6a_posM_real_univ_of_integrable_nonneg {d : ℕ}
    {f : Rd d → ℝ} (hf : Integrable f) (hf0 : ∀ x, 0 ≤ f x) :
    (posM f).real univ = ∫ x, f x := by
  have hnonneg : 0 ≤ ∫ x, f x := integral_nonneg hf0
  rw [Measure.real, posM_univ,
    ← ofReal_integral_eq_lintegral_ofReal hf (ae_of_all _ hf0),
    ENNReal.toReal_ofReal hnonneg]

theorem l6a_meanTrunc_measure_le_conv {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    posM (fun w : Rd d => |l2b_meanTruncTest hd hκ hε n w|) ≤
      Measure.conv (unitSphereProb d)
        (posM (fun w : Rd d => |convKernelEps κ ε w|)) := by
  let f : Rd d → ℝ := fun w => |convKernelEps κ ε w|
  have hfcont : Continuous f := by
    have hkcont : Continuous (convKernelEps κ ε) :=
      continuous_const.mul
        ((convKernel_contDiff (by omega : 0 < d) hκ).continuous.comp
          (continuous_const_smul _))
    exact hkcont.abs
  have hfi : Integrable f := (integrable_convKernelEps hd hκ hε).abs
  obtain ⟨B, hB, hbound⟩ := convKernelEps_bounded hd hκ hε
  have hconv := l6a_conv_posM_eq (unitSphereProb d) f hfcont.measurable
    (fun w => abs_nonneg _) hfi hbound
  rw [hconv]
  unfold posM
  apply withDensity_mono
  exact ae_of_all _ fun w => ENNReal.ofReal_le_ofReal
    (l6a_meanTrunc_abs_le_conv hd hκ hε n w)

end HigherDimLQGMetric
