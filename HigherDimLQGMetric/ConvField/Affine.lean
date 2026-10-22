import HigherDimLQGMetric.ConvField.Basic
import HigherDimLQGMetric.Field.Affine

/-!
# Translation of the convolution field

Packet L2b. Because the cutoff is centred at the evaluation point, translation
commutes with every truncated pairing, hence with its `limUnder` definition.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {κ : Rd d → ℝ}

theorem l2b_testAffinePull_convTrunc (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ε : ℝ)
    (w z : Rd d) (n : ℕ) :
    testAffinePull 1 w (convTrunc κ ε z n) = convTrunc κ ε (z + w) n := by
  ext x
  rw [testAffinePull_one_apply,
    l2b_convTrunc_apply hd hκ,
    l2b_convTrunc_apply hd hκ]
  congr 1 <;> congr 1 <;> abel_nf

theorem l2b_convMollify_comp_translate (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ε : ℝ)
    (g : DistRd d) (w z : Rd d) :
    convMollify κ ε (affineComp 1 w g) z = convMollify κ ε g (z + w) := by
  unfold convMollify
  congr 1
  funext n
  rw [affineComp_one_apply, l2b_testAffinePull_convTrunc hd hκ]

end HigherDimLQGMetric
