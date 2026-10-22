import HigherDimLQGMetric.ConvField.JointMain

/-! The radial convolution kernel has unit mass after the sphere-area factor. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

theorem l2b_radial_kernel_mass (d : ℕ) (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : 0 < ε) :
    ((volume : Measure (Rd d)).toSphere univ).toReal *
      ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) = 1 := by
  haveI : Nontrivial (Rd d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by
    rw [finrank_euclideanSpace_fin]; omega)
  let f : ℝ → ℝ := fun r => convKernelEps κ ε (r • e₁ d)
  have hp := integral_fun_norm_addHaar (volume : Measure (Rd d)) f
  rw [finrank_euclideanSpace_fin, nsmul_eq_mul, smul_eq_mul, Measure.real_def] at hp
  simp only [smul_eq_mul] at hp
  have harea : (d : ℝ) * (volume (ball (0 : Rd d) 1)).toReal =
      ((volume : Measure (Rd d)).toSphere univ).toReal := by
    rw [Measure.toSphere_apply_univ, finrank_euclideanSpace_fin,
      ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have heq : (∫ x : Rd d, f ‖x‖) = ∫ x : Rd d, convKernelEps κ ε x := by
    apply integral_congr_ae
    filter_upwards with x
    exact l2b_convKernelEps_axis_norm hd ε x
  rw [heq, integral_convKernelEps_eq_one hd hκ hε] at hp
  rw [← harea]
  simpa only [f, mul_assoc] using hp.symm

end HigherDimLQGMetric
