import HigherDimLQGMetric.ConvField.Scaling

/-! The bounded-continuous convolution obeys the kernel L¹ norm bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {κ : Rd d → ℝ}

theorem l2b_integral_abs_convKernelEps_eq {ε : ℝ} (hε : 0 < ε) :
    (∫ x : Rd d, |convKernelEps κ ε x|) =
      ∫ x : Rd d, |convKernel κ x| := by
  let F : Rd d → ℝ := fun x => |convKernel κ x|
  have hs := integral_comp_affinePt F (inv_pos.mpr hε) (0 : Rd d)
  simp only [add_zero, inv_pow, inv_inv] at hs
  have hp : ε ^ (-(d : ℝ)) = (ε ^ d)⁻¹ := by
    rw [Real.rpow_neg hε.le, Real.rpow_natCast]
  have hpow : ε ^ (-(d : ℝ)) * ε ^ d = 1 := by
    rw [hp]
    exact inv_mul_cancel₀ (pow_ne_zero _ hε.ne')
  calc
    (∫ x : Rd d, |convKernelEps κ ε x|) =
      ε ^ (-(d : ℝ)) * ∫ x : Rd d, F (ε⁻¹ • x) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with x
        rw [convKernelEps, abs_mul, abs_of_nonneg (Real.rpow_nonneg hε.le _)]
    _ = ε ^ (-(d : ℝ)) * (ε ^ d * ∫ x : Rd d, F x) := by rw [hs]
    _ = ∫ x : Rd d, F x := by rw [← mul_assoc, hpow, one_mul]

theorem l2b_abs_conv_ofCont_le_kernelL1 (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (f : C(Rd d, ℝ)) {M : ℝ} (hM : ∀ w, |f w| ≤ M) (z : Rd d) :
    |∫ w : Rd d, convKernelEps κ ε (z - w) * f w| ≤
      M * ∫ x : Rd d, |convKernel κ x| := by
  have hi : Integrable (fun w : Rd d => |convKernelEps κ ε (z - w)|) :=
    ((integrable_convKernelEps hd hκ hε).comp_sub_left z).abs
  have hbound : ∀ᵐ w ∂(volume : Measure (Rd d)),
      ‖convKernelEps κ ε (z - w) * f w‖ ≤ M * |convKernelEps κ ε (z - w)| := by
    filter_upwards with w
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul_of_nonneg_left (hM w) (abs_nonneg _)).trans_eq (mul_comm _ _)
  have h := norm_integral_le_of_norm_le (hi.const_mul M) hbound
  rw [Real.norm_eq_abs, integral_const_mul] at h
  calc
    |∫ w : Rd d, convKernelEps κ ε (z - w) * f w|
        ≤ M * ∫ w : Rd d, |convKernelEps κ ε (z - w)| := h
    _ = M * ∫ x : Rd d, |convKernelEps κ ε x| := by
        congr 1
        exact integral_sub_left_eq_self (fun x : Rd d => |convKernelEps κ ε x|) volume z
    _ = _ := by rw [l2b_integral_abs_convKernelEps_eq hε]

theorem l2b_abs_convMollify_ofCont_le_kernelL1 (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (f : C(Rd d, ℝ)) {M : ℝ} (hM : ∀ w, |f w| ≤ M) (z : Rd d) :
    |convMollify κ ε (ofCont f) z| ≤ M * ∫ x : Rd d, |convKernel κ x| := by
  rw [l2b_convMollify_ofCont hd hκ hε f M hM z]
  exact l2b_abs_conv_ofCont_le_kernelL1 hd hκ hε f hM z

end HigherDimLQGMetric
