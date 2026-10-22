import HigherDimLQGMetric.Core.MainInputs

/-!
# Weak metric uniqueness from sharp weak uniqueness

Packet L10a: [S] Theorem 1.4 follows from [1] Theorem 1.6 and the sharp weak
uniqueness theorem, with the frozen statement unchanged.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

/-- [S] Theorem 1.4 from its two named inputs. -/
theorem theorem14_of_inputs (hE2 : Theorem16Shape)
    (h14s : Theorem14SharpStmt) : Theorem14Stmt := by
  intro d ξ hd hξ hQ D D' c c' hD hD'
  exact h14s d ξ (distExp d ξ) hd hξ hQ D D'
    (hE2 d hd hξ hQ hD).2 (hE2 d hd hξ hQ hD').2

end HigherDimLQGMetric
