import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGContinuity.Caps.FullScales

/-!
# The number of dyadic radii in the full cover window

The cover of Lemma 2.3 uses every dyadic radius in an exponential window.
For the catalogue count we need its upper cardinality bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

/-- The full dyadic window contains at most linearly many scales in `V`. -/
theorem q11_fullScales_card_le {V : ℝ} (hV : 0 ≤ V) :
    ((p4_fullScales V).card : ℝ) ≤ 2 * V / Real.log 2 + 1 := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hratio : 0 ≤ 2 * V / Real.log 2 := by positivity
  have hcard : (p4_fullScales V).card ≤ Nat.floor (2 * V / Real.log 2) + 1 := by
    simp only [p4_fullScales, Nat.card_Icc]
    omega
  have hcast : ((p4_fullScales V).card : ℝ) ≤
      (Nat.floor (2 * V / Real.log 2) : ℝ) + 1 := by
    exact_mod_cast hcard
  exact hcast.trans (add_le_add_left (Nat.floor_le hratio) _)

end HigherDimLQGContinuity
