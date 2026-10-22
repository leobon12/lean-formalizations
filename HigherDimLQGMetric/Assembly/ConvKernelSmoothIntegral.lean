import HigherDimLQGMetric.Kernel.ConvKernelMain

/-!
# Provider of the frozen theorem `HigherDimLQGMetric.convKernel_smooth_integral`

`convKernel_smooth_integral_impl` states the frozen anchor `HigherDimLQGMetric/Frozen/ConvKernelSmoothIntegral.lean`
verbatim. Its proof is packet L1c's `convKernel_smooth_integral_proof` (`HigherDimLQGMetric/Kernel/ConvKernelMain.lean`:
[1] Remark 1.1 and Lemma 2.9; MA5 Details (a) A2.4, A2.5). This module imports no frozen theorem anchor.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The frozen statement of `convKernel_smooth_integral`, proved. -/
theorem convKernel_smooth_integral_impl :
    ∀ (d : ℕ), 2 ≤ d → ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ) ∧ ∫ x, convKernel κ x = 1 :=
  convKernel_smooth_integral_proof

end HigherDimLQGMetric
