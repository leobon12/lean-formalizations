import HigherDimLQGMetric.KernelIndep.Exponent

/-!
# Provider of the frozen theorem `HigherDimLQGMetric.distExp_spec`

`distExp_spec_impl` states the frozen anchor `HigherDimLQGMetric/Frozen/DistExpSpec.lean` verbatim. Its proof is
packet L9a's `distExp_spec_proof` (`HigherDimLQGMetric/KernelIndep/Exponent.lean`: existence of the white-noise LFPP
exponent for every kernel, HigherDimLFPP, and its kernel independence D-KI, MA6; rulings M7, M9, M21). This module
imports no frozen theorem anchor.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The frozen statement of `distExp_spec`, proved. -/
theorem distExp_spec_impl :
    ∀ (d : ℕ), 2 ≤ d → ∀ ξ : ℝ, 0 < ξ → ∀ Q : ℝ, IsDistanceExponent d ξ Q ↔ Q = distExp d ξ :=
  distExp_spec_proof

end HigherDimLQGMetric
