/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntActiveRetained
import InteractingSLE.Spec.Supplement.GW4LeafWall

/-!
# The existing walk facts supply the proper curves and contact order

No additional pathwise contact-order hypothesis is needed for the active
containment theorem. The already supplied WalkPairPathFacts construct
proper parametrizations with precisely that order, independently of the
remaining recorded-prefix/exit selection.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.WalkIntActive

open WalkMean WalkInf

/-- Extract the proper parametrizations and their common-contact order
from the existing sample event. These are proved data, not a new input. -/
theorem exists_ordered_walk_parametrizations {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {Ω : Type*} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ω : Ω}
    (hfacts : WalkPairPathFacts κ b jumps E ω) :
    ∃ α β : ℝ≥0 → ℂ, Supp9B.IsProperCurve α ∧ Supp9B.IsProperCurve β ∧
      range α = physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (walkRuns κ b jumps E ω).1 ∧
      range β = physOf (boundaryWalkSpec b jumps (Real.pi / 2) false)
        (walkRuns κ b jumps E ω).2 ∧
      ∀ u u' v v' : ℝ≥0, α u = β v → α u' = β v' → (u < u' ↔ v < v') := by
  obtain ⟨α, hα, hα0, hαrange⟩ := hfacts.1
  obtain ⟨β, hβ, hβ0, hβrange⟩ := hfacts.2.1
  exact ⟨α, β, hα, hβ, hαrange, hβrange,
    hfacts.2.2 α β hαrange hβrange
      (GW4Leaf.isCompleteSimpleFlow_of_isProperCurve hα hα0)
      (GW4Leaf.isCompleteSimpleFlow_of_isProperCurve hβ hβ0)⟩

end InteractingSLE.Theorem14.WalkIntActive
