import HigherDimLQGMetric.Amplify.Defs
import HigherDimLQGMetric.Metric.WeylAxioms

/-!
# The collar margin in fine field amplification

This is the numerical inequality in source Lemma 6.1, lines 973–977.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

/-- The source's `e^{4ξδ}<2` leaves enough room for the global shortcut comparison. -/
theorem amplify_collar_margin {cs ℓ x : ℝ} (hcs : 0 < cs) (hℓ : 0 < ℓ)
    (hx : 1 ≤ x) (hx2 : x * x < 2) :
    cs⁻¹ * x * ℓ < x⁻¹ * (4 * max 1 cs⁻¹ * ℓ) := by
  have hxpos : 0 < x := by linarith
  have hm : cs⁻¹ ≤ max 1 cs⁻¹ := le_max_right _ _
  have hci : 0 < cs⁻¹ := inv_pos.2 hcs
  rw [lt_inv_mul_iff₀ hxpos]
  nlinarith [mul_lt_mul_of_pos_left hx2 (mul_pos hci hℓ),
    mul_le_mul_of_nonneg_right hm hℓ.le]

end HigherDimLQGMetric
