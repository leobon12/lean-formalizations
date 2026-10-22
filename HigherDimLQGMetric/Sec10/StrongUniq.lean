import HigherDimLQGMetric.Core.MainInputs
import HigherDimLQGMetric.Sec10.Lemma101

/-!
# Uniqueness of strong exponential metric assignments

The strong axioms imply the sharp weak axioms, so sharp weak uniqueness applies.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

/-- Strong uniqueness follows from Lemma 10.1 and sharp weak uniqueness. -/
theorem strongUniqueness_of (h14s : Theorem14SharpStmt) : StrongUniquenessStmt := by
  intro d ξ Q hd hξ hQ D D' hD hD'
  exact h14s d ξ Q hd hξ hQ D D'
    (lemma101 (by omega : 2 ≤ d) hξ hD)
    (lemma101 (by omega : 2 ≤ d) hξ hD')

end HigherDimLQGMetric
