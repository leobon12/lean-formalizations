import HigherDimLQGMetric.KernelIndep.LowerBound

/-!
# Provider of the frozen theorem `HigherDimLQGMetric.subcritical_nonempty`

`subcritical_nonempty_impl` states the frozen anchor `HigherDimLQGMetric/Frozen/SubcriticalNonempty.lean` verbatim.
Its proof is packet L9a's `subcritical_nonempty_proof` (`HigherDimLQGMetric/KernelIndep/LowerBound.lean`: the
elementary bound `Q(ξ) ≥ 1/ξ − √(2d)`, MA6). This module imports no frozen theorem anchor.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The frozen statement of `subcritical_nonempty`, proved. -/
theorem subcritical_nonempty_impl :
    ∀ (d : ℕ), 2 ≤ d → ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ∀ ξ ∈ Ioo (0 : ℝ) ξ₀, Real.sqrt (2 * d) < distExp d ξ :=
  subcritical_nonempty_proof

end HigherDimLQGMetric
