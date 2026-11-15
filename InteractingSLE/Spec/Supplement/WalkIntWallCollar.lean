/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntWallFrontier

/-!
# Local ordinary-walk containment gives the physical frontier collar

The original matching clauses already express containment of the own walk
in a retained prefix and domination of the other walk near the landing.
These imply the ordinary-union containment used by the frontier adapter.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal

namespace InteractingSLE.Theorem14.WalkIntWall

open WalkBdry WalkMean

/-- The two original local matching containment clauses cover the ordinary
union, without any assumption on real trace contacts. -/
theorem ordinary_cover_of_domination {s s' : ExplState} {F : Set ℂ} {p : ℂ} {r : ℝ}
    (hown : wsetOf s ∩ ball p r ⊆ F)
    (hother : wsetOf s' ∩ ball p r ⊆ wsetOf s) :
    (wsetOf s ∪ wsetOf s') ∩ ball p r ⊆ F := by
  rintro z ⟨hz | hz, hb⟩
  · exact hown ⟨hz, hb⟩
  · exact hown ⟨hother ⟨hz, hb⟩, hb⟩

/-- The frontier collar is a conclusion of local containment of the two
ordinary walks. It is not an additional geometric hypothesis here. -/
theorem frontier_collar_of_ordinary_cover {sR sL : ExplState} {wR wL : ExplSpec}
    {α β : ℝ≥0 → ℂ} (hα : Supp9B.IsProperCurve α) (hβ : Supp9B.IsProperCurve β)
    (hR : range α = physOf wR sR) (hL : range β = physOf wL sL)
    {C F : Set ℂ} (hC : C ∈ betweenComponents (physOf wR sR) (physOf wL sL))
    {p : ℂ} {r : ℝ} (hlocal : (wsetOf sR ∪ wsetOf sL) ∩ ball p r ⊆ F) :
    frontier C ∩ ball p r ⊆ closure F ∪ {z : ℂ | z.im = 0} := by
  rintro z ⟨hz, hb⟩
  rcases frontier_between_walks_subset hα hβ hR hL hC hz with hw | hr
  · exact Or.inl (subset_closure (hlocal ⟨hw, hb⟩))
  · exact Or.inr hr

end InteractingSLE.Theorem14.WalkIntWall
