import HigherDimLQGMetric.ConvField.RadialAll
import HigherDimLQGMetric.Kernel.CovKernelMoment

/-! Radial integrability of the convolution kernel and its logarithmic moment. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

variable {d : ℕ} {κ : Rd d → ℝ}

theorem l2b_convKernelEps_axis_norm (hd : 2 ≤ d) (ε : ℝ) (x : Rd d) :
    convKernelEps κ ε (‖x‖ • e₁ d) = convKernelEps κ ε x := by
  apply l2b_convKernelEps_radial
  rw [norm_smul, HigherDimLFPP.norm_e₁ (by omega : 0 < d), mul_one]
  simp

theorem l2b_integrable_radial_kernel (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun r : ℝ => r ^ (d - 1) * convKernelEps κ ε (r • e₁ d))
      (Ioi (0 : ℝ)) := by
  haveI : Nontrivial (Rd d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by
    rw [finrank_euclideanSpace_fin]; omega)
  let f : ℝ → ℝ := fun r => convKernelEps κ ε (r • e₁ d)
  have hvec : Integrable (fun x : Rd d => f ‖x‖) := by
    apply (integrable_convKernelEps hd hκ hε).congr
    filter_upwards with x
    exact (l2b_convKernelEps_axis_norm hd ε x).symm
  have hrad := (integrable_fun_norm_addHaar (μ := (volume : Measure (Rd d))) (f := f)).mp hvec
  simpa only [finrank_euclideanSpace_fin, smul_eq_mul] using hrad

theorem l2b_integrable_radial_logKernel (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun r : ℝ => r ^ (d - 1) *
      (Real.log (2 + r) * convKernelEps κ ε (r • e₁ d))) (Ioi (0 : ℝ)) := by
  haveI : Nontrivial (Rd d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by
    rw [finrank_euclideanSpace_fin]; omega)
  let f : ℝ → ℝ := fun r => Real.log (2 + r) * convKernelEps κ ε (r • e₁ d)
  have hvec : Integrable (fun x : Rd d => f ‖x‖) := by
    apply (integrable_logMoment_convKernelEps hd hκ hε).congr
    filter_upwards with x
    exact congrArg (Real.log (2 + ‖x‖) * ·)
      (l2b_convKernelEps_axis_norm hd ε x).symm
  have hrad := (integrable_fun_norm_addHaar (μ := (volume : Measure (Rd d))) (f := f)).mp hvec
  simpa only [finrank_euclideanSpace_fin, smul_eq_mul] using hrad

end HigherDimLQGMetric
