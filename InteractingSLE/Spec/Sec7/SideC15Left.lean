/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketLeftFrontier

/-!
# The original change pocket is on the required side of its right wall

PROVE-SIDE-COLLAR2. Derive the side condition of the source strip formula
from the actual left frontier, the wall visits and rational-time
counterflow avoidance. The statement is for a general change pocket.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped NNReal

namespace InteractingSLE.Sec7.SideC15

open WangWu PocketCoord PocketOrientFact PocketLeftFrontier PocketJordan Lemma71I

/-- The source formula's pocket-side condition follows from the same
frontier and counterflow facts that already produce its orientation. -/
theorem changePocket_subset_leftSideOf_of_cfAvoid
    {R L β : ℝ≥0 → ℂ} {r : ℝ≥0} {η : ℝ → ℂ}
    (h : IsChangeConfigInc R L r) (hβ : IsSimpleProper β) (hLβ : L r = β r)
    (hvis : IsWallVisited R η) (hη : ContinuousOn η (Ici 0))
    (hav : ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η q) ∉ leftSideOf (range β)) :
    changePocket R L r ⊆ leftSideOf (range R) := by
  have hopen := Sec5.Cond44Ref.isOpen_leftSideOf_arcRange hβ.isProperArc
  rw [arcRange_realPath] at hopen
  have hd := disjoint_range_of_isWallVisited hvis h.right.2.2.1
    (fun t ht => cfAvoid_of_rat hopen hη hav ht)
  exact h.changePocket_subset_leftSideOf (h.mem_leftSideOf_of_leftFrontier hβ hLβ hd)

end InteractingSLE.Sec7.SideC15
