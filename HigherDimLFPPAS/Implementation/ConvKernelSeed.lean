import HigherDimLFPPAS.Frozen.IsAdmissibleSeed
import HigherDimLFPPAS.Signed.KernelDecay
import HigherDimLQGMetric.Frozen.ConvKernel
import HigherDimLQGMetric.Kernel.ConvKernelSmooth

/-!
# Provider of the frozen theorem `HigherDimLFPPAS.convKernel_seed`

`convKernel_seed_impl` states the frozen anchor `HigherDimLFPPAS/Frozen/ConvKernelSeed.lean` verbatim (the kernel
`K` of (1.2) is real, smooth, with `∫ K = 1`, for every admissible seed; rulings L7, L8). Proof: smoothness and
`∫ K = 1` are the sign-free copy `HigherDimLFPPAS.Signed.l1c_convKernel_seed` (packet G1); reality is the host's
`HigherDimLQGMetric.convKernel_complex_eq_fourierInv`, which has no kernel hypothesis (`𝓕⁻¹ K̂` is the
complexification of `convKernel κ`). This module imports no frozen theorem anchor of this library.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped FourierTransform

namespace HigherDimLFPPAS.Implementation

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- The frozen statement of `convKernel_seed`, proved. -/
theorem convKernel_seed_impl :
    ∀ (d : ℕ), 2 ≤ d → ∀ κ : Rd d → ℝ, IsAdmissibleSeed κ →
      (∀ x : Rd d, (𝓕⁻ (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) x).im = 0) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ) ∧ ∫ x, convKernel κ x = 1 := by
  intro d hd κ hκ
  obtain ⟨hC, -, h1, -⟩ := Signed.l1c_convKernel_seed d hd κ hκ
  refine ⟨fun x => ?_, hC, h1⟩
  rw [← convKernel_complex_eq_fourierInv x]
  exact Complex.ofReal_im _

end HigherDimLFPPAS.Implementation
