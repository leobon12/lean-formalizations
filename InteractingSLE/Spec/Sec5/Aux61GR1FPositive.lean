/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GPrimeNegative
import InteractingSLE.Spec.Sec4.Heights

/-! # The positive reference word with a canonical seed

Reuse the landed three-step word with its interval to the right of zero.
Its interior parameter is shifted by `2λ`, giving the desired physical
height there. The existing height-to-weight equivalence proves `RefPos`.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology
open QuantumZipper (chiC)

namespace InteractingSLE.Sec5.Aux61GR1F

/-- Canonical seed heights and the value `v` on the positive interval. -/
def positiveBoundary (κ a b v : ℝ) : ℝ → ℝ :=
  Aux61GPrime.negativeBoundary κ a b (v - 2 * sleLambda κ)

theorem positiveBoundary_pc (κ a b v : ℝ) :
    IsPiecewiseConstantBoundaryData (positiveBoundary κ a b v) {a, b, 0} :=
  Aux61GPrime.negativeBoundary_pc κ a b (v - 2 * sleLambda κ)

theorem positiveBoundary_value {κ a b v z : ℝ} (ha : 0 < a) (hz : z ∈ Ioo a b) :
    positiveBoundary κ a b v z = v := by
  simp only [positiveBoundary, Aux61GPrime.negativeBoundary,
    ite_eq_right (not_lt.2 (ha.trans hz.1).le), ite_eq_right (not_lt.2 hz.1.le),
    ite_eq_left hz.2]
  ring

/-- Both seed weights are zero. In particular the seed is admissible even
when the reference interval is in the boundary-hitting parameter range. -/
theorem positiveBoundary_seed {κ a b v : ℝ} (hκ : 0 < κ) (ha : 0 < a) (hab : a < b) :
    ¬ ForceWord.ThresholdCondition
      (flowLineRhoL κ (positiveBoundary κ a b v) {a, b, 0} 0 0)
      (flowLineRhoR κ (positiveBoundary κ a b v) {a, b, 0} 0 0) 0
      (flowLineXL (positiveBoundary κ a b v) {a, b, 0} 0)
      (flowLineXR (positiveBoundary κ a b v) {a, b, 0} 0) := by
  have hL : PiecewiseConstantBoundaryData.leftLim (positiveBoundary κ a b v) 0 = -sleLambda κ :=
    Sec4.leftLim_eq_of_forall (a := -1) (by norm_num) fun z hz => by
      simp [positiveBoundary, Aux61GPrime.negativeBoundary, hz.2,
        hz.2.trans ha, hz.2.trans (ha.trans hab)]
  have hR : PiecewiseConstantBoundaryData.rightLim (positiveBoundary κ a b v) 0 = sleLambda κ :=
    Sec4.rightLim_eq_of_forall ha fun z hz => by
      simp [positiveBoundary, Aux61GPrime.negativeBoundary, not_lt.2 hz.1.le,
        hz.2, hz.2.trans hab]
  apply Aux61Fib.not_threshold_seed hκ
  · rw [hL]; linarith [Sec4.sleLambda_pos hκ]
  · rw [hR]; linarith [Sec4.sleLambda_pos hκ]

/-- The positive reference has exactly the threshold required by Aux. 64. -/
theorem positiveBoundary_refPos {κ a b v : ℝ} (hκ : 0 < κ) (hκ₄ : κ ≤ 4)
    (ha : 0 < a) (hv : sleLambda κ - Real.pi * chiC κ ≤ v) :
    Aux61Cov.RefPos κ (positiveBoundary κ a b v) {a, b, 0} (Ioo a b) := by
  exact ⟨hκ₄, positiveBoundary_pc κ a b v, a, b, v, rfl, ha.le,
    fun z hz _ => positiveBoundary_value ha hz, (Sec4.le_cumWeightRight_iff hκ).2 hv⟩

end InteractingSLE.Sec5.Aux61GR1F
