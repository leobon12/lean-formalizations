/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInZeroRefData
import Mathlib.Data.Rat.Encodable

/-!
# A fixed countable family covering all rational original reference times

PROVE-POCKET-SIDEIN. Use the standard enumeration of the rationals and clip
negative original times to zero. Every positive rational time is retained,
so every positive original interval contains one of these fixed references.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped NNReal

namespace InteractingSLE.Wire.Current.SideTest

/-- A fixed countable original-time family for `withOriginalReferences`. -/
def rationalOriginalTime (n : ℕ) : ℝ≥0 :=
  Real.toNNReal (((Denumerable.eqv ℚ).symm n : ℚ) : ℝ)

/-- Every rational time occurs, with negative times clipped to zero. -/
theorem rationalOriginalTime_eqv (q : ℚ) :
    rationalOriginalTime (Denumerable.eqv ℚ q) = Real.toNNReal (q : ℝ) := by
  simp only [rationalOriginalTime, Equiv.symm_apply_apply]

/-- The fixed family contains a reference strictly inside every original
time interval with a nonnegative left endpoint. -/
theorem exists_rationalOriginalTime_between {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ n : ℕ, a < (rationalOriginalTime n : ℝ) ∧ (rationalOriginalTime n : ℝ) < b := by
  obtain ⟨q, haq, hqb⟩ := exists_rat_btwn hab
  refine ⟨Denumerable.eqv ℚ q, ?_⟩
  rw [rationalOriginalTime_eqv, Real.coe_toNNReal _ (ha.trans haq.le)]
  exact ⟨haq, hqb⟩

end InteractingSLE.Wire.Current.SideTest
