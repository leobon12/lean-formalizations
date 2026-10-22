import HigherDimLQGMetric.Thm13.GlobalPatch

/-! The B3 interface specializes the universal Theorem 1.3 input. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HigherDimLQGMetric

/-- Assembly bridge once the universal Theorem 1.3 result is available. -/
theorem b3Goal_of_universal (hL8 : ∀ d ξ κ, L8_thm13 d ξ κ) : B3Goal := by
  intro d _ κ _ ξ _ _ _ _
  exact hL8 d ξ κ

end HigherDimLQGMetric
