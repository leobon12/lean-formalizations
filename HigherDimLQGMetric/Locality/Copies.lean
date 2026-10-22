import HigherDimLQGMetric.Local.CopiesMain

/-!
# Conditional metric copies

The dimension-qualified interface of ruling M31 follows from the conditional-copy
theorem in `Local.CopiesMain`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

/-- [1] Lemma 3.11's conditional-copy consequence in the dimensions used by the paper. -/
theorem l7b_copies : L7b_copies := by
  intro d hd ξ Ω mΩ P hP h D₁ D₂ hh h₁ h₂ hcopy
  exact l7b_copies_of_dim hd ξ P h D₁ D₂ hh h₁ h₂ hcopy

end HigherDimLQGMetric
