/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow19Windows

/-! # Canonical seed heights for arbitrary returned landing heights

Changing the height on a reference interval separated from zero preserves
both seed heights. The returned-word constancy piece and phase integer
may therefore determine that height without changing hSeed.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology

namespace InteractingSLE.Sec5.Aux61GWindow19
open Aux61GR1F

/-- Both seed heights for the positive reference, for every landing height. -/
theorem positiveBoundary_seed_heights {κ a b v : ℝ} (ha : 0 < a) (hab : a < b) :
    PiecewiseConstantBoundaryData.leftLim (positiveBoundary κ a b v) 0 = -sleLambda κ ∧
      PiecewiseConstantBoundaryData.rightLim (positiveBoundary κ a b v) 0 = sleLambda κ := by
  constructor
  · apply Sec4.leftLim_eq_of_forall (a := -1) (by norm_num)
    intro z hz
    simp only [positiveBoundary, Aux61GPrime.negativeBoundary,
      ite_eq_left hz.2, ite_eq_left (hz.2.trans ha), ite_eq_left (hz.2.trans (ha.trans hab)),
      sub_self, mul_zero, add_zero]
  · apply Sec4.rightLim_eq_of_forall ha
    intro z hz
    simp only [positiveBoundary, Aux61GPrime.negativeBoundary,
      ite_eq_right (not_lt.2 hz.1.le), ite_eq_left hz.2, ite_eq_left (hz.2.trans hab),
      sub_self, mul_zero, add_zero]

/-- Both seed heights for the negative reference, for every landing height. -/
theorem negativeBoundary_seed_heights {κ a b v : ℝ} (hab : a < b) (hb : b < 0) :
    PiecewiseConstantBoundaryData.leftLim (Aux61GPrime.negativeBoundary κ a b v) 0 = -sleLambda κ ∧
      PiecewiseConstantBoundaryData.rightLim (Aux61GPrime.negativeBoundary κ a b v) 0 = sleLambda κ := by
  constructor
  · exact Sec4.leftLim_eq_of_forall hb fun _ hz => Aux61GPrime.negativeBoundary_seedLeft hab hz.1 hz.2
  · exact Sec4.rightLim_eq_of_forall one_pos fun _ hz => Aux61GPrime.negativeBoundary_pos hab hb hz.1

end InteractingSLE.Sec5.Aux61GWindow19
